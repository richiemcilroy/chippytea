//! A single streaming worker classifies before descending, emits bounded batches,
//! and leaves persistent indexing and candidate retention to the SQLite owner.
use crate::activity::ActivitySnapshot;
use crate::lock_facts::{BunLockCache, NpmLockCache};
use crate::model::{Candidate, RULE_VERSION, Result, Root, ScanBatch, ScanStats};
use crate::recommendations;
use crate::refresh::RecentFileHints;
pub use crate::safety::measure;
use crate::safety::{
    self, Directory, DiscoveryEntry, Entry, EntryMeta, Hardlinks, Measurement, MeasurementPolicy,
};
use serde_json::Value;
use std::collections::VecDeque;
use std::ffi::{CString, OsStr, OsString};
use std::io::Read;
use std::mem::size_of;
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::rc::Rc;
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[cfg(test)]
const LARGE_FILE_BYTES: u64 = 100_000_000;
const BATCH_INTERVAL: Duration = Duration::from_millis(100);
const MAX_BATCH: usize = 64;
const MAX_SHALLOW_FRONTIER: usize = 32;
const MAX_DEFERRED_ARTIFACTS: usize = 256;
const MAX_SCAN_LANES: usize = 4;
const MAX_MEASUREMENT_JOB_BYTES: usize = 1024 * 1024;
const MEASUREMENT_QUANTUM_ENTRIES: usize = 256;
const MEASUREMENT_QUANTUM: Duration = Duration::from_millis(5);
// Discovery and measurement retain descriptor-anchored stacks. This is a
// process-wide scheduling ceiling. Standalone scan processes reserve this
// budget plus non-traversal headroom before admitting filesystem work; the
// native host's descriptor limits are never changed by discovery.
pub(crate) const MAX_SCHEDULED_DIRECTORY_FDS: usize = MAX_SHALLOW_FRONTIER + 6 * safety::MAX_DEPTH;
const MAX_ACTIVE_MEASUREMENTS: usize =
    (MAX_SCHEDULED_DIRECTORY_FDS - MAX_SHALLOW_FRONTIER) / safety::MAX_DEPTH - MAX_SCAN_LANES;
const DAY_NS: i64 = 86_400_000_000_000;
const DEVELOPER_QUIET_DAYS: i64 = 7;
#[cfg(test)]
const INSTALLER_QUIET_DAYS: i64 = 14;
#[cfg(test)]
const DOWNLOAD_QUIET_DAYS: i64 = 30;
/// Mutation preparation may reuse an activity snapshot no older than this
/// before its measurement; the final recheck always captures a fresh one.
const ACTIVITY_MAX_AGE: Duration = Duration::from_secs(1);
/// Scan-time gating tolerates a slightly older snapshot. Suggestions are only
/// ranking output; `revalidate` re-gates every item before any mutation.
const SCAN_ACTIVITY_MAX_AGE: Duration = Duration::from_secs(5);

/// Interactive discovery stops at artifact boundaries which cannot produce a
/// recommendation. Exhaustive metadata coverage remains available explicitly
/// for inventory diagnostics and equivalent traversal benchmarks.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ScanMode {
    #[default]
    Suggestions,
    MetadataCoverage,
}

struct Publisher<F> {
    callback: F,
    queued: Vec<Candidate>,
    last: Instant,
}
impl<F: FnMut(ScanBatch)> Publisher<F> {
    fn new(callback: F) -> Self {
        Self {
            callback,
            queued: Vec::with_capacity(MAX_BATCH),
            last: Instant::now(),
        }
    }
    fn queue(&mut self, candidate: Candidate, stats: &ScanStats, force: bool) {
        self.queued.push(candidate);
        if force || self.queued.len() >= MAX_BATCH || self.last.elapsed() >= BATCH_INTERVAL {
            self.flush(stats);
        }
    }
    fn flush(&mut self, stats: &ScanStats) {
        (self.callback)(ScanBatch {
            candidates: std::mem::replace(&mut self.queued, Vec::with_capacity(MAX_BATCH)),
            stats: stats.clone(),
        });
        self.last = Instant::now();
    }
}

#[derive(Clone)]
struct Evidence {
    kind: &'static str,
    title: String,
    explanation: &'static str,
    consequence: &'static str,
    fingerprint: String,
    blocked: Option<String>,
    latest_modified_ns: i64,
    quiet_days: i64,
    activity_root: Option<PathBuf>,
}

/// One safely captured evidence file. The digest commits to the exact bytes,
/// so a cached identity hit and a fresh read produce identical fingerprints.
#[derive(Clone)]
struct EvidenceSource {
    bytes: Rc<[u8]>,
    identity: crate::model::Identity,
    digest: blake3::Hash,
}

impl EvidenceSource {
    fn from_regular(file: safety::RegularFile) -> Self {
        let digest = blake3::hash(&file.bytes);
        Self {
            bytes: file.bytes.into(),
            identity: file.identity,
            digest,
        }
    }
}

const MAX_CONTENT_CACHE_ENTRIES: usize = 64;
const MAX_CONTENT_CACHE_BYTES: usize = 16 * 1024 * 1024;

/// Session-scoped identity-keyed cache of evidence file contents. A hit
/// requires the complete current pathname metadata (device, inode, mode, size,
/// mtime, ctime, links, owner, flags) to equal the metadata captured directly
/// after the verified read; any difference falls through to a fresh, fully
/// validated read. It never persists across scan sessions, and a cached answer
/// never feeds a mutation: `revalidate` always rereads evidence uncached.
#[derive(Default)]
struct ContentCache {
    entries: Vec<(PathBuf, EntryMeta, EvidenceSource)>,
    retained_bytes: usize,
}

impl ContentCache {
    fn read(&mut self, path: &Path, cancel: &AtomicBool) -> Result<EvidenceSource> {
        safety::cancelled(cancel)?;
        if let Some(index) = self
            .entries
            .iter()
            .position(|(cached, _, _)| cached == path)
        {
            // The no-follow lookup cannot be satisfied by a substituted link,
            // and any content, permission, ownership or link-count change moves
            // the file's ctime out from under the captured metadata.
            match safety::metadata(path) {
                Ok(current)
                    if current == self.entries[index].1
                        && safety::regular_evidence_metadata(&current) =>
                {
                    let source = self.entries[index].2.clone();
                    self.entries[index..].rotate_left(1);
                    return Ok(source);
                }
                _ => {
                    let evicted = self.entries.remove(index);
                    self.retained_bytes -= evicted.2.bytes.len();
                }
            }
        }
        let source = EvidenceSource::from_regular(safety::read_regular(path, cancel)?);
        // Retention needs the full pathname metadata observed after the
        // verified read. A file already changed again is served fresh but not
        // remembered; failing to cache is never failing the caller.
        if let Ok(meta) = safety::metadata(path)
            && meta.identity == source.identity
            && safety::regular_evidence_metadata(&meta)
            && source.bytes.len() <= MAX_CONTENT_CACHE_BYTES
        {
            while !self.entries.is_empty()
                && (self.entries.len() >= MAX_CONTENT_CACHE_ENTRIES
                    || self.retained_bytes + source.bytes.len() > MAX_CONTENT_CACHE_BYTES)
            {
                let evicted = self.entries.remove(0);
                self.retained_bytes -= evicted.2.bytes.len();
            }
            self.retained_bytes += source.bytes.len();
            self.entries
                .push((path.to_path_buf(), meta, source.clone()));
        }
        Ok(source)
    }
}

/// Read caches for one discovery traversal. Ownership facts and captured file
/// contents are disposable together and never outlive their scan session.
#[derive(Default)]
pub(crate) struct EvidenceCaches {
    locks: NpmLockCache,
    bun_locks: BunLockCache,
    pnpm_locks: PnpmLockCache,
    manifest_workspaces: ManifestWorkspaceCache,
    contents: ContentCache,
}

fn read_source(
    path: &Path,
    cancel: &AtomicBool,
    caches: Option<&mut EvidenceCaches>,
) -> Result<EvidenceSource> {
    match caches {
        Some(caches) => caches.contents.read(path, cancel),
        None => Ok(EvidenceSource::from_regular(safety::read_regular(
            path, cancel,
        )?)),
    }
}

fn add_evidence(
    hash: &mut blake3::Hasher,
    path: &Path,
    source: &EvidenceSource,
    latest_modified_ns: &mut i64,
) {
    hash.update(path.as_os_str().as_bytes());
    hash.update(source.digest.as_bytes());
    let identity = &source.identity;
    hash.update(&identity.device.to_le_bytes());
    hash.update(&identity.inode.to_le_bytes());
    hash.update(&identity.modified_ns.to_le_bytes());
    hash.update(&identity.changed_ns.to_le_bytes());
    *latest_modified_ns = (*latest_modified_ns).max(identity.modified_ns);
}

fn path_exists(path: &Path) -> Result<bool> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!("Cannot verify project configuration: {error}")),
    }
}

fn node_manifest(bytes: &[u8]) -> Result<Value> {
    let parsed: Value =
        serde_json::from_slice(bytes).map_err(|_| "package.json is not valid JSON")?;
    let object = parsed.as_object().ok_or("package.json is not an object")?;
    let recognized = object
        .get("name")
        .and_then(Value::as_str)
        .is_some_and(|name| !name.trim().is_empty())
        || ["dependencies", "devDependencies", "optionalDependencies"]
            .iter()
            .any(|key| object.get(*key).is_some_and(Value::is_object))
        || object
            .get("workspaces")
            .is_some_and(|v| v.is_array() || v.is_object());
    if !recognized {
        return Err("The package manifest does not identify a project".into());
    }
    Ok(parsed)
}

/// Match ordinary component globs without allocating or crossing a separator.
/// Anchored prefix/suffix literals bound the ordered runs between wildcards.
fn workspace_component(pattern: &str, component: &str) -> bool {
    if component.starts_with('.') && !pattern.starts_with('.') {
        return false;
    }
    let mut literals = pattern.split('*');
    let Some(remaining) = component.strip_prefix(literals.next().unwrap()) else {
        return false;
    };
    let Some(suffix) = literals.next_back() else {
        return remaining.is_empty();
    };
    let Some(mut remaining) = remaining.strip_suffix(suffix) else {
        return false;
    };
    for literal in literals {
        let Some(index) = remaining.find(literal) else {
            return false;
        };
        remaining = &remaining[index + literal.len()..];
    }
    true
}

/// Deliberately small subset: root `.`, component `*`, and whole-component `**`.
/// Unsupported syntax stays diagnostic instead of guessing project ownership.
fn workspace_pattern(pattern: &str, relative: &str) -> Result<bool> {
    let pattern = pattern.trim_end_matches('/');
    let pattern = pattern.strip_prefix("./").unwrap_or(pattern);
    if pattern == "." {
        return Ok(relative.is_empty());
    }
    if pattern.is_empty() || pattern.starts_with('/') || pattern.len() > 1024 {
        return Err("Workspace paths are not supported local relative patterns".into());
    }
    let parts: Vec<_> = pattern.split('/').collect();
    if parts.len() > 64
        || parts.iter().any(|part| {
            part.is_empty()
                || *part == "."
                || *part == ".."
                || (part.contains("**") && *part != "**")
                || part.contains(['?', '[', ']', '{', '}', '!', '\\', '(', ')', '|'])
        })
    {
        return Err("Complex workspace patterns need manual inspection".into());
    }
    let components: Vec<_> = relative.split('/').collect();
    let mut previous = vec![false; components.len() + 1];
    previous[0] = true;
    for part in parts {
        let mut current = vec![false; previous.len()];
        if part == "**" {
            current[0] = previous[0];
            for index in 1..current.len() {
                current[index] = previous[index]
                    || (!components[index - 1].starts_with('.') && current[index - 1]);
            }
        } else {
            for index in 1..current.len() {
                current[index] =
                    previous[index - 1] && workspace_component(part, components[index - 1]);
            }
        }
        previous = current;
    }
    Ok(previous[components.len()])
}

fn workspace_includes(patterns: &[String], relative: &str) -> Result<bool> {
    if patterns.len() > 512 {
        return Err("Workspace membership exceeds the bounded evidence limit".into());
    }
    let mut included = false;
    let mut excluded = false;
    for pattern in patterns {
        if let Some(pattern) = pattern.strip_prefix('!') {
            excluded |= workspace_pattern(pattern, relative)?;
        } else {
            included |= workspace_pattern(pattern, relative)?;
        }
    }
    Ok(included && !excluded)
}

fn manifest_workspaces(manifest: &Value) -> Result<Vec<String>> {
    let Some(workspaces) = manifest.get("workspaces") else {
        return Ok(Vec::new());
    };
    let entries = workspaces
        .as_array()
        .or_else(|| workspaces.get("packages").and_then(Value::as_array))
        .ok_or("Workspace membership is not a supported list")?;
    entries
        .iter()
        .map(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .ok_or_else(|| "Workspace membership is not a list of paths".into())
        })
        .collect()
}

const MAX_MANIFEST_CACHE_ENTRIES: usize = 8;
const MAX_MANIFEST_CACHE_BYTES: usize = 1024 * 1024;
const MIN_MANIFEST_CACHE_BYTES: usize = 8 * 1024;

struct CachedManifestWorkspaces {
    digest: blake3::Hash,
    patterns: Vec<String>,
}

impl CachedManifestWorkspaces {
    fn heap_bytes(&self) -> Option<usize> {
        self.patterns.iter().try_fold(
            self.patterns.capacity().checked_mul(size_of::<String>())?,
            |bytes, pattern| bytes.checked_add(pattern.capacity()),
        )
    }
}

/// Scan-local ancestor workspace lists, never local manifest names, identities,
/// membership answers or cleanup permission. Charge all retained capacities,
/// including unused entry and pattern slots. Input and Value allocations are
/// transient and remain subject to the existing bounded evidence reader.
struct ManifestWorkspaceCache {
    entries: Vec<CachedManifestWorkspaces>,
    entry_limit: usize,
    byte_limit: usize,
    retained_bytes: usize,
}

impl Default for ManifestWorkspaceCache {
    fn default() -> Self {
        Self::with_limits(MAX_MANIFEST_CACHE_ENTRIES, MAX_MANIFEST_CACHE_BYTES)
    }
}

impl ManifestWorkspaceCache {
    fn with_limits(entry_limit: usize, byte_limit: usize) -> Self {
        let byte_limit = byte_limit.min(MAX_MANIFEST_CACHE_BYTES);
        let mut entry_limit = entry_limit
            .min(MAX_MANIFEST_CACHE_ENTRIES)
            .min(byte_limit / size_of::<CachedManifestWorkspaces>());
        let mut entries = Vec::with_capacity(entry_limit);
        let mut retained_bytes = entries.capacity() * size_of::<CachedManifestWorkspaces>();
        if retained_bytes > byte_limit {
            entries = Vec::new();
            entry_limit = 0;
            retained_bytes = 0;
        }
        Self {
            entries,
            entry_limit,
            byte_limit,
            retained_bytes,
        }
    }

    /// The digest describes these exact, currently identity-validated bytes.
    /// Entry cancellation is an additional cooperative boundary, consistent
    /// with the lock caches. Once parsing starts, preserve the original error
    /// order through extraction and matching before polling cancellation again.
    fn includes_captured(
        &mut self,
        digest: blake3::Hash,
        bytes: &[u8],
        relative: &str,
        cancel: &AtomicBool,
    ) -> Result<bool> {
        safety::cancelled(cancel)?;
        if self.entry_limit > 0
            && bytes.len() >= MIN_MANIFEST_CACHE_BYTES
            && let Some(index) = self.entries.iter().position(|entry| entry.digest == digest)
        {
            let included = workspace_includes(&self.entries[index].patterns, relative)?;
            safety::cancelled(cancel)?;
            self.entries[index..].rotate_left(1);
            return Ok(included);
        }
        let parsed = (|| {
            let manifest = node_manifest(bytes)?;
            let patterns = manifest_workspaces(&manifest)?;
            let included = workspace_includes(&patterns, relative)?;
            Ok((patterns, included))
        })();
        self.finish_miss(digest, bytes.len(), parsed, cancel)
    }

    fn finish_miss(
        &mut self,
        digest: blake3::Hash,
        input_bytes: usize,
        parsed: Result<(Vec<String>, bool)>,
        cancel: &AtomicBool,
    ) -> Result<bool> {
        // Parse/extraction/matching errors win over cancellation discovered
        // after that contiguous work. No error or cancelled result is retained.
        let (patterns, included) = parsed?;
        safety::cancelled(cancel)?;
        if self.entry_limit == 0 || input_bytes < MIN_MANIFEST_CACHE_BYTES {
            return Ok(included);
        }
        let entry = CachedManifestWorkspaces { digest, patterns };
        let Some(heap_bytes) = entry.heap_bytes() else {
            return Ok(included);
        };
        let container_bytes = self.entries.capacity() * size_of::<CachedManifestWorkspaces>();
        if heap_bytes > self.byte_limit - container_bytes {
            return Ok(included); // Oversized valid lists answer without eviction.
        }
        safety::cancelled(cancel)?;
        while self.entries.len() == self.entry_limit
            || heap_bytes > self.byte_limit - self.retained_bytes
        {
            let evicted = self.entries.remove(0);
            self.retained_bytes -= evicted
                .heap_bytes()
                .expect("Previously admitted capacities");
        }
        self.retained_bytes += heap_bytes;
        self.entries.push(entry);
        Ok(included)
    }
}

fn yaml_scalar(value: &str) -> Result<&str> {
    let value = value.trim();
    let value = if value.len() >= 2
        && ((value.starts_with('\'') && value.ends_with('\''))
            || (value.starts_with('"') && value.ends_with('"')))
    {
        &value[1..value.len() - 1]
    } else {
        if value.starts_with(['*', '!']) {
            return Err("YAML aliases and tags cannot establish workspace ownership".into());
        }
        value
    };
    if value.is_empty() || value.contains(['\'', '"', '\\', '#', '&', '|', '>', '{', '}', '[', ']'])
    {
        return Err("Complex pnpm workspace evidence needs manual inspection".into());
    }
    Ok(value)
}

fn pnpm_workspace_patterns(bytes: &[u8]) -> Result<Vec<String>> {
    let text = std::str::from_utf8(bytes).map_err(|_| "The pnpm workspace file is not UTF-8")?;
    let mut inside = false;
    let mut found = false;
    let mut patterns = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        if !line.starts_with(' ') {
            if line == "packages:" {
                if found {
                    return Err("Duplicate pnpm workspace membership is ambiguous".into());
                }
                inside = true;
                found = true;
            } else {
                inside = false;
            }
        } else if inside {
            let value = line
                .strip_prefix("  - ")
                .ok_or("Complex pnpm workspace membership needs manual inspection")?;
            patterns.push(yaml_scalar(value)?.to_owned());
        }
    }
    if !found {
        return Err("The pnpm workspace file has no supported package list".into());
    }
    Ok(patterns)
}

/// Visit every importer using the existing deliberately limited lock grammar.
/// A match never skips later validation, including duplicate section errors.
fn visit_pnpm_importers<'a>(bytes: &'a [u8], mut importer: impl FnMut(&'a str)) -> Result<()> {
    let text = std::str::from_utf8(bytes).map_err(|_| "The pnpm lockfile is not UTF-8")?;
    let mut version = false;
    let mut importers = false;
    let mut saw_importers = false;
    let mut packages = false;
    for line in text.lines() {
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        if let Some(value) = line.strip_prefix("lockfileVersion:") {
            if version {
                return Err("Duplicate pnpm lockfile version is ambiguous".into());
            }
            if !matches!(yaml_scalar(value)?, "6.0" | "9.0") {
                return Err("This pnpm lockfile version needs manual inspection".into());
            }
            version = true;
        }
        if !line.starts_with(' ') {
            importers = line == "importers:";
            if importers {
                if saw_importers {
                    return Err("Duplicate pnpm importers are ambiguous".into());
                }
                saw_importers = true;
            }
            packages |= line == "packages:" || line == "packages: {}";
        } else if importers && line.starts_with("  ") && !line.starts_with("   ") {
            let key = line
                .trim()
                .strip_suffix(": {}")
                .or_else(|| line.trim().strip_suffix(':'))
                .ok_or("Complex pnpm importer evidence needs manual inspection")?;
            importer(yaml_scalar(key)?);
        }
    }
    if !version || !saw_importers || !packages {
        return Err("The pnpm lockfile lacks recognized importer and package evidence".into());
    }
    Ok(())
}

fn pnpm_lock_owns(bytes: &[u8], relative: &str) -> Result<bool> {
    let relative = if relative.is_empty() { "." } else { relative };
    let mut owns = false;
    visit_pnpm_importers(bytes, |key| owns |= key == relative)?;
    Ok(owns)
}

const MAX_PNPM_CACHE_ENTRIES: usize = 8;
const MAX_PNPM_CACHE_BYTES: usize = 1024 * 1024;
const MIN_PNPM_CACHE_BYTES: usize = 32 * 1024;

struct PnpmKeyRange {
    offset: u32,
    length: u32,
}

struct PnpmFacts {
    bytes: Vec<u8>,
    keys: Vec<PnpmKeyRange>,
}

impl PnpmFacts {
    fn capture(
        bytes: &[u8],
        relative: &str,
        heap_limit: usize,
        cancel: &AtomicBool,
    ) -> Result<(bool, Option<Self>)> {
        safety::cancelled(cancel)?;
        let relative = if relative.is_empty() { "." } else { relative };
        let mut owns = false;
        let mut retained = Some(Vec::<&str>::new());
        let mut byte_count = 0usize;
        // Borrowed keys are transient and separately bounded to 1 MiB. Stop
        // collecting if either budget is exceeded, but finish the same parser.
        let max_keys = MAX_PNPM_CACHE_BYTES / size_of::<&str>();
        visit_pnpm_importers(bytes, |key| {
            owns |= key == relative;
            let Some(keys) = retained.as_mut() else {
                return;
            };
            let required = byte_count.checked_add(key.len()).and_then(|bytes| {
                (keys.len() + 1)
                    .checked_mul(size_of::<PnpmKeyRange>())
                    .and_then(|ranges| bytes.checked_add(ranges))
            });
            if required.is_none_or(|required| required > heap_limit) || keys.len() == max_keys {
                retained = None;
                return;
            }
            if keys.len() == keys.capacity() {
                let capacity = keys.capacity().saturating_mul(2).max(4).min(max_keys);
                keys.reserve_exact(capacity - keys.len());
                if keys.capacity() > max_keys {
                    retained = None;
                    return;
                }
            }
            keys.push(key);
            byte_count += key.len();
        })?;
        // Keep parse errors ahead of cancellation discovered after parsing.
        // The original pure pnpm parser has no cancellation checkpoints.
        safety::cancelled(cancel)?;
        let Some(mut keys) = retained else {
            return Ok((owns, None));
        };
        keys.sort_unstable();
        keys.dedup();
        safety::cancelled(cancel)?;
        let byte_count = keys.iter().map(|key| key.len()).sum();
        let mut facts = Self {
            bytes: Vec::with_capacity(byte_count),
            keys: Vec::with_capacity(keys.len()),
        };
        if facts.heap_bytes() > heap_limit {
            return Ok((owns, None));
        }
        for key in keys {
            safety::cancelled(cancel)?;
            let (Ok(offset), Ok(length)) =
                (u32::try_from(facts.bytes.len()), u32::try_from(key.len()))
            else {
                return Ok((owns, None));
            };
            facts.keys.push(PnpmKeyRange { offset, length });
            facts.bytes.extend_from_slice(key.as_bytes());
        }
        safety::cancelled(cancel)?;
        Ok((owns, Some(facts)))
    }

    fn owns(&self, relative: &str) -> bool {
        let relative = if relative.is_empty() { "." } else { relative };
        self.keys
            .binary_search_by(|key| {
                let start = key.offset as usize;
                self.bytes[start..start + key.length as usize].cmp(relative.as_bytes())
            })
            .is_ok()
    }

    fn heap_bytes(&self) -> usize {
        self.bytes.capacity() + self.keys.capacity() * size_of::<PnpmKeyRange>()
    }
}

struct CachedPnpm {
    digest: blake3::Hash,
    facts: PnpmFacts,
}

/// Scan-local pure importer facts, never file identities or deletion permission.
/// The cap charges actual retained capacities, including unused entry slots.
/// Input bytes, allocator overhead and bounded temporary keys are not retained.
struct PnpmLockCache {
    entries: Vec<CachedPnpm>,
    entry_limit: usize,
    byte_limit: usize,
    retained_bytes: usize,
}

impl Default for PnpmLockCache {
    fn default() -> Self {
        Self::with_limits(MAX_PNPM_CACHE_ENTRIES, MAX_PNPM_CACHE_BYTES)
    }
}

impl PnpmLockCache {
    fn with_limits(entry_limit: usize, byte_limit: usize) -> Self {
        let byte_limit = byte_limit.min(MAX_PNPM_CACHE_BYTES);
        let mut entry_limit = entry_limit
            .min(MAX_PNPM_CACHE_ENTRIES)
            .min(byte_limit / size_of::<CachedPnpm>());
        let mut entries = Vec::with_capacity(entry_limit);
        let mut retained_bytes = entries.capacity() * size_of::<CachedPnpm>();
        if retained_bytes > byte_limit {
            entries = Vec::new();
            entry_limit = 0;
            retained_bytes = 0;
        }
        Self {
            entries,
            entry_limit,
            byte_limit,
            retained_bytes,
        }
    }

    /// The digest must describe these exact, freshly identity-validated bytes.
    /// Small locks use the allocation-free ownership visitor without retention.
    fn owns_captured(
        &mut self,
        digest: blake3::Hash,
        bytes: &[u8],
        relative: &str,
        cancel: &AtomicBool,
    ) -> Result<bool> {
        safety::cancelled(cancel)?;
        if self.entry_limit == 0 || bytes.len() < MIN_PNPM_CACHE_BYTES {
            let owns = pnpm_lock_owns(bytes, relative)?;
            safety::cancelled(cancel)?;
            return Ok(owns);
        }
        if let Some(index) = self.entries.iter().position(|entry| entry.digest == digest) {
            let owns = self.entries[index].facts.owns(relative);
            safety::cancelled(cancel)?;
            self.entries[index..].rotate_left(1);
            return Ok(owns);
        }
        let container_bytes = self.entries.capacity() * size_of::<CachedPnpm>();
        let (owns, facts) =
            PnpmFacts::capture(bytes, relative, self.byte_limit - container_bytes, cancel)?;
        let Some(facts) = facts else {
            // Oversized valid evidence answers normally and displaces nothing.
            return Ok(owns);
        };
        let heap_bytes = facts.heap_bytes();
        safety::cancelled(cancel)?;
        while self.entries.len() == self.entry_limit
            || heap_bytes > self.byte_limit - self.retained_bytes
        {
            let evicted = self.entries.remove(0);
            self.retained_bytes -= evicted.facts.heap_bytes();
        }
        self.retained_bytes += heap_bytes;
        self.entries.push(CachedPnpm { digest, facts });
        Ok(owns)
    }
}

fn node_lock_owns(
    name: &str,
    bytes: &[u8],
    relative: &str,
    manifest: &Value,
    cancel: &AtomicBool,
) -> Result<bool> {
    match name {
        "package-lock.json" | "npm-shrinkwrap.json" => {
            crate::lock_facts::npm_owns(bytes, relative, cancel)
        }
        "yarn.lock" => {
            let text = std::str::from_utf8(bytes).map_err(|_| "The Yarn lockfile is not UTF-8")?;
            if !text.contains("# yarn lockfile v1") {
                return Err("This Yarn layout needs manual inspection".into());
            }
            Ok(true) // Ancestor ownership still requires declared workspace membership.
        }
        "bun.lock" => crate::lock_facts::bun_owns(
            bytes,
            relative,
            manifest.get("name").and_then(Value::as_str),
            cancel,
        ),
        "bun.lockb" => {
            // A bounded binary ownership marker, never executed or used to infer
            // workspace membership. Text locks carry the exact member table.
            const HEADER: &[u8] = b"#!/usr/bin/env bun\nbun-lockfile-format-v0\n";
            let offset = HEADER.len();
            if !bytes.starts_with(HEADER) || bytes.len() < offset + 4 + 32 + 8 + 24 {
                return Err("The Bun binary lock header is invalid or incomplete".into());
            }
            let version = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
            let end = u64::from_le_bytes(bytes[offset + 36..offset + 44].try_into().unwrap());
            if !matches!(version, 2 | 3) || end < (offset + 68) as u64 || end > bytes.len() as u64 {
                return Err("The Bun binary lock version or length is unsupported".into());
            }
            Ok(relative.is_empty())
        }
        "pnpm-lock.yaml" => pnpm_lock_owns(bytes, relative),
        _ => Ok(false),
    }
}

#[cfg(test)]
fn node_evidence(root: &Root, project: &Path, cancel: &AtomicBool) -> Result<Option<Evidence>> {
    node_evidence_cached(root, project, cancel, None)
}

fn node_evidence_cached(
    root: &Root,
    project: &Path,
    cancel: &AtomicBool,
    mut caches: Option<&mut EvidenceCaches>,
) -> Result<Option<Evidence>> {
    safety::cancelled(cancel)?;
    let manifest = project.join("package.json");
    if !path_exists(&manifest)? {
        return Err(
            "The dependency directory has no project manifest; ownership is unverified".into(),
        );
    }
    let source = read_source(&manifest, cancel, caches.as_deref_mut())?;
    let parsed = node_manifest(&source.bytes)?;
    let mut hash = blake3::Hasher::new();
    let mut latest_modified_ns = 0;
    add_evidence(&mut hash, &manifest, &source, &mut latest_modified_ns);
    let mut owner = None;
    let mut blocked = None;
    for directory in project
        .ancestors()
        .take(64)
        .take_while(|path| path.starts_with(&root.path))
    {
        safety::cancelled(cancel)?;
        let relative = project
            .strip_prefix(directory)
            .unwrap()
            .to_str()
            .ok_or("Workspace paths are not supported UTF-8 names")?;
        let mut node_member = directory == project;
        let mut pnpm_member = directory == project;
        if directory != project && path_exists(&directory.join("package.json"))? {
            let file = directory.join("package.json");
            let source = read_source(&file, cancel, caches.as_deref_mut())?;
            if source.bytes.len() >= MIN_MANIFEST_CACHE_BYTES
                && let Some(caches) = caches.as_deref_mut()
            {
                node_member = caches.manifest_workspaces.includes_captured(
                    source.digest,
                    &source.bytes,
                    relative,
                    cancel,
                )?;
                add_evidence(&mut hash, &file, &source, &mut latest_modified_ns);
            } else {
                let ancestor = node_manifest(&source.bytes)?;
                add_evidence(&mut hash, &file, &source, &mut latest_modified_ns);
                node_member = workspace_includes(&manifest_workspaces(&ancestor)?, relative)?;
            }
        }
        for name in [
            ".npmrc",
            ".yarnrc",
            ".yarnrc.yml",
            "bunfig.toml",
            "pnpm-workspace.yaml",
        ] {
            safety::cancelled(cancel)?;
            let config = directory.join(name);
            if !path_exists(&config)? {
                continue;
            }
            let source = read_source(&config, cancel, caches.as_deref_mut())?;
            add_evidence(&mut hash, &config, &source, &mut latest_modified_ns);
            if name == "pnpm-workspace.yaml" && directory != project {
                pnpm_member =
                    workspace_includes(&pnpm_workspace_patterns(&source.bytes)?, relative)?;
            }
            if name == ".yarnrc.yml" {
                blocked = Some(
                    "Modern Yarn or shared installation layouts need manual inspection".into(),
                );
            }
            if name == "bunfig.toml" {
                let text = std::str::from_utf8(&source.bytes)
                    .map_err(|_| "Bun configuration is not UTF-8")?;
                let _: toml::Value =
                    toml::from_str(text).map_err(|_| "Bun configuration is invalid TOML")?;
            }
        }
        let mut recognized_lock = false;
        let mut has_lock = false;
        for name in [
            "npm-shrinkwrap.json",
            "package-lock.json",
            "yarn.lock",
            "bun.lock",
            "bun.lockb",
            "pnpm-lock.yaml",
        ] {
            safety::cancelled(cancel)?;
            let file = directory.join(name);
            if !path_exists(&file)? {
                continue;
            }
            has_lock = true;
            let source = read_source(&file, cancel, caches.as_deref_mut())?;
            add_evidence(&mut hash, &file, &source, &mut latest_modified_ns);
            let declares_member = if name == "pnpm-lock.yaml" {
                pnpm_member
            } else {
                node_member
            };
            // Cache only pure parsing of identity-verified captured bytes.
            // Presence, parent/file identities, evidence hashing and workspace
            // membership are checked for every member, including a cache hit.
            let owns = match (name, caches.as_deref_mut()) {
                ("package-lock.json" | "npm-shrinkwrap.json", Some(caches)) => caches
                    .locks
                    .owns_captured(Some(source.digest), &source.bytes, relative, cancel),
                ("bun.lock", Some(caches)) => caches.bun_locks.owns_captured(
                    Some(source.digest),
                    &source.bytes,
                    relative,
                    parsed.get("name").and_then(Value::as_str),
                    cancel,
                ),
                ("pnpm-lock.yaml", Some(caches)) => {
                    caches
                        .pnpm_locks
                        .owns_captured(source.digest, &source.bytes, relative, cancel)
                }
                _ => node_lock_owns(name, &source.bytes, relative, &parsed, cancel),
            }?;
            recognized_lock |= owns && declares_member;
        }
        if recognized_lock {
            owner = Some(directory.to_path_buf());
            break;
        }
        if has_lock || path_exists(&directory.join(".git"))? {
            break; // Never borrow ownership across a separate install or repository.
        }
    }
    let owner = owner
        .ok_or("No supported lockfile proves ownership of this project or workspace member")?;
    Ok(Some(Evidence {
        kind: "node",
        title: format!(
            "{} dependencies",
            project
                .file_name()
                .unwrap_or_else(|| OsStr::new("Node project"))
                .to_string_lossy()
        ),
        explanation: "A project manifest and a supported npm, Yarn classic, Bun or pnpm lockfile identify this installed dependency directory. Workspace membership is verified when the lock belongs to an ancestor.",
        consequence: "Dependencies must be reinstalled from the owning project or workspace before it runs. Network access and compatible installation options may be needed. Linked source files outside this directory are preserved.",
        fingerprint: hash.finalize().to_hex().to_string(),
        blocked,
        latest_modified_ns,
        quiet_days: DEVELOPER_QUIET_DAYS,
        activity_root: Some(owner),
    }))
}

fn parse_toml(bytes: &[u8]) -> Result<toml::Value> {
    let text = std::str::from_utf8(bytes).map_err(|_| "Cargo configuration is not UTF-8")?;
    toml::from_str(text).map_err(|_| "Cargo configuration is not valid TOML".into())
}

fn cargo_evidence(
    root: &Root,
    project: &Path,
    artifact: &Path,
    cancel: &AtomicBool,
    mut caches: Option<&mut EvidenceCaches>,
) -> Result<Option<Evidence>> {
    safety::cancelled(cancel)?;
    let manifest = project.join("Cargo.toml");
    if !path_exists(&manifest)? {
        return Ok(None);
    }
    let source = read_source(&manifest, cancel, caches.as_deref_mut())?;
    let parsed = parse_toml(&source.bytes)?;
    let package = parsed.get("package").and_then(toml::Value::as_table);
    let workspace = parsed.get("workspace").and_then(toml::Value::as_table);
    if !(package.is_some_and(|p| {
        p.get("name")
            .and_then(toml::Value::as_str)
            .is_some_and(|n| !n.is_empty())
    }) || workspace.is_some())
    {
        return Err("Cargo.toml does not identify a package or workspace".into());
    }
    let mut hash = blake3::Hasher::new();
    let mut latest_modified_ns = 0;
    add_evidence(&mut hash, &manifest, &source, &mut latest_modified_ns);
    let lock = project.join("Cargo.lock");
    if path_exists(&lock)? {
        let source = read_source(&lock, cancel, caches.as_deref_mut())?;
        parse_toml(&source.bytes)?;
        add_evidence(&mut hash, &lock, &source, &mut latest_modified_ns);
    }
    let mut recognized_marker = false;
    for name in ["CACHEDIR.TAG", ".rustc_info.json"] {
        safety::cancelled(cancel)?;
        let marker = artifact.join(name);
        if !path_exists(&marker)? {
            continue;
        }
        let source = read_source(&marker, cancel, caches.as_deref_mut())?;
        let valid = if name == "CACHEDIR.TAG" {
            source
                .bytes
                .starts_with(b"Signature: 8a477f597d28d172789f06886806bc55")
        } else {
            serde_json::from_slice::<Value>(&source.bytes)
                .ok()
                .is_some_and(|value| value.get("rustc_fingerprint").is_some())
        };
        if !valid {
            return Err("The target directory's Cargo marker is invalid".into());
        }
        // Markers are included in the tree digest too. They establish ownership;
        // their original absolute path must not be used during staged measurement.
        add_evidence(&mut hash, &marker, &source, &mut latest_modified_ns);
        recognized_marker = true;
    }
    if !recognized_marker {
        return Ok(None);
    }
    let mut blocked = None;
    if package.is_some_and(|p| p.contains_key("workspace")) {
        blocked = Some("This package delegates target ownership to another workspace".into());
    }
    if std::env::var_os("CARGO_TARGET_DIR").is_some()
        || std::env::var_os("CARGO_BUILD_TARGET_DIR").is_some()
    {
        blocked = Some("A custom Cargo output directory is configured in this process".into());
    }
    let mut current = Some(project);
    while let Some(directory) = current {
        for name in [".cargo/config", ".cargo/config.toml"] {
            safety::cancelled(cancel)?;
            let config = directory.join(name);
            if path_exists(&config)? {
                let source = read_source(&config, cancel, caches.as_deref_mut())?;
                let parsed = parse_toml(&source.bytes)?;
                add_evidence(&mut hash, &config, &source, &mut latest_modified_ns);
                if parsed
                    .get("build")
                    .and_then(toml::Value::as_table)
                    .is_some_and(|table| {
                        table.contains_key("target-dir") || table.contains_key("build-dir")
                    })
                    || parsed
                        .get("env")
                        .and_then(toml::Value::as_table)
                        .is_some_and(|table| {
                            table.contains_key("CARGO_TARGET_DIR")
                                || table.contains_key("CARGO_BUILD_TARGET_DIR")
                        })
                {
                    blocked = Some("Cargo config uses a nonstandard output directory".into());
                }
            }
        }
        // A manifest with its own [workspace] starts a new workspace, including
        // a package with an empty workspace table. Outer manifests neither own
        // its target directory nor affect its evidence freshness. Ancestor Cargo
        // configuration still applies and is checked independently above.
        if directory != project && workspace.is_none() {
            let parent_manifest = directory.join("Cargo.toml");
            if path_exists(&parent_manifest)? {
                let source = read_source(&parent_manifest, cancel, caches.as_deref_mut())?;
                let parsed = parse_toml(&source.bytes)?;
                add_evidence(
                    &mut hash,
                    &parent_manifest,
                    &source,
                    &mut latest_modified_ns,
                );
                if parsed.get("workspace").is_some() {
                    blocked = Some(
                        "An ancestor workspace owns the default Cargo output directory".into(),
                    );
                }
            }
        }
        if directory == root.path {
            break;
        }
        current = directory
            .parent()
            .filter(|parent| parent.starts_with(&root.path));
    }
    // Global config is not scanned or read outside the chosen root. Its presence
    // makes a default-output claim ambiguous and therefore blocks cleanup.
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")));
    if let Some(home) = cargo_home {
        for name in ["config", "config.toml"] {
            safety::cancelled(cancel)?;
            if path_exists(&home.join(name))? && !home.starts_with(&root.path) {
                blocked = Some("Global Cargo configuration is outside this folder's authorization; output ownership is uncertain".into());
            }
        }
    }
    Ok(Some(Evidence {
        kind: "cargo",
        title: format!(
            "{} build artifacts",
            project
                .file_name()
                .unwrap_or_else(|| OsStr::new("Cargo project"))
                .to_string_lossy()
        ),
        explanation: "Cargo project evidence and a standard target marker identify this project's default build output.",
        consequence: "The next build must recompile. Compiled applications and binaries inside this target directory are removed too.",
        fingerprint: hash.finalize().to_hex().to_string(),
        blocked,
        latest_modified_ns,
        quiet_days: DEVELOPER_QUIET_DAYS,
        activity_root: None,
    }))
}

/// A named directory alone is not a Python environment. Only a direct-child
/// `pyvenv.cfg`, reached without following any link, positively identifies one;
/// anything else leaves the directory an ordinary folder.
fn venv_evidence(
    project: &Path,
    artifact: &Path,
    cancel: &AtomicBool,
    caches: Option<&mut EvidenceCaches>,
) -> Result<Option<Evidence>> {
    safety::cancelled(cancel)?;
    let marker = artifact.join("pyvenv.cfg");
    if !path_exists(&marker)? {
        return Ok(None);
    }
    // The no-follow lookup classifies a symbolic-link marker as not a regular
    // file; a linked pyvenv.cfg cannot identify this directory.
    if !safety::metadata(&marker)?.is_file() {
        return Ok(None);
    }
    let source = read_source(&marker, cancel, caches)?;
    let mut hash = blake3::Hasher::new();
    hash.update(format!("venv-v{RULE_VERSION}").as_bytes());
    let mut latest_modified_ns = 0;
    add_evidence(&mut hash, &marker, &source, &mut latest_modified_ns);
    Ok(Some(Evidence {
        kind: "venv",
        title: format!(
            "{} Python environment",
            project
                .file_name()
                .unwrap_or_else(|| OsStr::new("Python project"))
                .to_string_lossy()
        ),
        explanation: "A pyvenv.cfg file identifies this directory as a Python virtual environment created for the neighbouring project.",
        consequence: "The environment must be recreated (for example with python -m venv) and its packages reinstalled before the project runs again. Source files outside this directory are preserved.",
        fingerprint: hash.finalize().to_hex().to_string(),
        blocked: None,
        latest_modified_ns,
        quiet_days: DEVELOPER_QUIET_DAYS,
        activity_root: Some(project.to_path_buf()),
    }))
}

/// Generated web build caches are recognized only beside their project's own
/// `package.json`. A cache directory without that sibling manifest, or with a
/// linked one, stays an ordinary folder.
fn webcache_evidence(
    project: &Path,
    artifact: &Path,
    cancel: &AtomicBool,
    caches: Option<&mut EvidenceCaches>,
) -> Result<Option<Evidence>> {
    safety::cancelled(cancel)?;
    let explanation = match artifact.file_name().and_then(OsStr::to_str) {
        Some(".next") => {
            "The .next directory holds this project's generated build output and cache, identified by the project manifest beside it."
        }
        Some(".nuxt") => {
            "The .nuxt directory holds this project's generated build output and cache, identified by the project manifest beside it."
        }
        Some(".turbo") => {
            "The .turbo directory holds this project's task cache, identified by the project manifest beside it."
        }
        Some(".parcel-cache") => {
            "The .parcel-cache directory holds this project's bundler cache, identified by the project manifest beside it."
        }
        _ => return Ok(None),
    };
    let manifest = project.join("package.json");
    if !path_exists(&manifest)? {
        return Ok(None);
    }
    if !safety::metadata(&manifest)?.is_file() {
        return Ok(None);
    }
    let source = read_source(&manifest, cancel, caches)?;
    let mut hash = blake3::Hasher::new();
    hash.update(format!("webcache-v{RULE_VERSION}").as_bytes());
    // Sibling caches share one manifest; the cache's own name keeps each
    // directory's evidence distinct.
    hash.update(artifact.file_name().unwrap_or_default().as_bytes());
    let mut latest_modified_ns = 0;
    add_evidence(&mut hash, &manifest, &source, &mut latest_modified_ns);
    Ok(Some(Evidence {
        kind: "webcache",
        title: format!(
            "{} build cache",
            project
                .file_name()
                .unwrap_or_else(|| OsStr::new("Web project"))
                .to_string_lossy()
        ),
        explanation,
        consequence: "The next build or dev run regenerates it; rebuild before serving this project. Source files outside this directory are preserved.",
        fingerprint: hash.finalize().to_hex().to_string(),
        blocked: None,
        latest_modified_ns,
        quiet_days: DEVELOPER_QUIET_DAYS,
        activity_root: Some(project.to_path_buf()),
    }))
}

fn clock_ns() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
        .min(i64::MAX as u128) as i64
}

fn quiet_for(latest_modified_ns: i64, now_ns: i64, days: i64) -> bool {
    latest_modified_ns <= now_ns.saturating_sub(days.saturating_mul(DAY_NS))
}

fn unfinished_component(name: &OsStr) -> bool {
    let bytes = name.as_bytes();
    [
        b".download".as_slice(),
        b".crdownload",
        b".partial",
        b".part",
        b".filepart",
        b".aria2",
        b".tmp",
        b".temp",
    ]
    .iter()
    .any(|suffix| {
        bytes
            .get(bytes.len().saturating_sub(suffix.len())..)
            .is_some_and(|tail| tail.eq_ignore_ascii_case(suffix))
    }) || bytes
        .get(..19)
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b".com.google.chrome."))
}

fn downloads_boundary(root: &Root) -> Option<PathBuf> {
    recommendations::downloads_boundary(root)
}

#[cfg(test)]
fn in_downloads(root: &Root, path: &Path) -> bool {
    downloads_boundary(root).is_some_and(|boundary| path.starts_with(boundary))
}

fn unfinished_download(boundary: Option<&Path>, path: &Path) -> bool {
    boundary.is_some_and(|boundary| {
        path.strip_prefix(boundary).is_ok_and(|relative| {
            relative
                .components()
                .any(|component| unfinished_component(component.as_os_str()))
        })
    })
}

fn suggestion_reason(found: &Evidence, measured: &Measurement, now_ns: i64) -> Option<String> {
    let minimum = recommendations::minimum_bytes(found.kind);
    if measured.allocated_bytes < minimum {
        return Some(format!(
            "Less than {} MB is allocated locally; it does not meet this category's size threshold",
            minimum / 1_000_000
        ));
    }
    let latest = measured.latest_modified_ns.max(found.latest_modified_ns);
    if !quiet_for(latest, now_ns, found.quiet_days) {
        return Some(format!(
            "Recently modified; recommendations require {} quiet days",
            found.quiet_days
        ));
    }
    None
}

fn everyday_evidence(path: &Path, meta: &EntryMeta, kind: &'static str) -> Option<Evidence> {
    if meta.is_file() && meta.identity.size < recommendations::minimum_bytes(kind) {
        return None;
    }
    let (explanation, consequence) = match kind {
        "cache" => (
            "An old cache in your authorized user Library/Caches location. Apps may regenerate or download this data again; it is not personal application-support data.",
            "Close the owning app before moving this cache to Trash. Ownership cannot always be identified; an app can keep writing to files in Trash, and changes there can prevent automatic restore. The app may need network access or start more slowly. Keep offline data you still need. Trash does not free space or earn chips.",
        ),
        "log" => (
            "An old, sizeable log file in your authorized user Library/Logs location. Logs can help diagnose a problem; age does not establish that they are no longer needed.",
            "Review this log before moving it to Trash. Keep it if you are troubleshooting or need a diagnostic record. Trash does not free space or earn chips.",
        ),
        "crashreport" => (
            "An old crash or diagnostic report in your authorized user Library/Logs/DiagnosticReports location. It may still be useful for support or troubleshooting.",
            "Review the report before moving it to Trash. Keep reports needed by support. Trash does not free space or earn chips.",
        ),
        "xcode" => (
            "Old Xcode-generated data in your authorized user Library/Developer/Xcode/DerivedData location. Archives, simulators, device support and project source are not included.",
            "Close Xcode and build tools before moving this folder to Trash. Xcode must rebuild or reindex the affected project, and compiled products in this folder are removed. Trash does not free space or earn chips.",
        ),
        "installer" => (
            "An old downloaded disk image or installer in your authorized Downloads location. Its age does not prove installation completed or that you no longer need it.",
            "Review the installer before moving it to Trash. Keep it if you need to reinstall offline. Downloads never earn chips, and Trash does not free space.",
        ),
        "archive" => (
            "An old downloaded archive or disk image in your authorized Downloads location. This scan does not assume it has been extracted or that another copy exists.",
            "Check that you no longer need the archive before moving it to Trash. It may be your only copy. Downloads never earn chips, and Trash does not free space.",
        ),
        "largefile" => (
            "A large, older document, media file or archive in an authorized personal-file scope. Size and modification time make it worth reviewing, not automatically disposable.",
            "Open or preview this file and decide whether to keep it. Personal files are Trash-only, never earn chips, and are never permanently removed by chippytea.",
        ),
        "download" => (
            "A large local download in your authorized Downloads location. Review its contents; age and size do not prove it is no longer needed.",
            "Review the file before moving it to Trash. You can restore it while it remains in Trash. Personal files never earn chips.",
        ),
        _ => return None,
    };
    let name = path.file_name()?.to_string_lossy();
    let title = match kind {
        "cache" => format!("{name} cache"),
        "xcode" => format!("{name} Xcode data"),
        _ => name.into_owned(),
    };
    Some(Evidence {
        kind,
        title,
        explanation,
        consequence,
        fingerprint: format!("{kind}-v{RULE_VERSION}"),
        blocked: None,
        latest_modified_ns: meta.identity.modified_ns,
        quiet_days: recommendations::quiet_days(kind),
        activity_root: recommendations::checks_activity(kind).then(|| path.to_path_buf()),
    })
}

fn evidence(
    root: &Root,
    path: &Path,
    meta: &EntryMeta,
    cancel: &AtomicBool,
) -> Result<Option<Evidence>> {
    evidence_with_downloads(
        root,
        path,
        meta,
        downloads_boundary(root).as_deref(),
        cancel,
    )
}

fn evidence_with_downloads(
    root: &Root,
    path: &Path,
    meta: &EntryMeta,
    downloads: Option<&Path>,
    cancel: &AtomicBool,
) -> Result<Option<Evidence>> {
    evidence_with_downloads_cached(root, path, meta, downloads, cancel, None)
}

fn evidence_with_downloads_cached(
    root: &Root,
    path: &Path,
    meta: &EntryMeta,
    downloads: Option<&Path>,
    cancel: &AtomicBool,
    caches: Option<&mut EvidenceCaches>,
) -> Result<Option<Evidence>> {
    if let Some(kind) = recommendations::library_candidate(root, path, meta.is_dir()) {
        return Ok(everyday_evidence(path, meta, kind));
    }
    if recommendations::library_area(root, path).is_some() {
        // Library containers are never developer projects and are not themselves
        // cleanup units. Only the location-specific adapters above may classify.
        return Ok(None);
    }
    // Most traversed directories cannot be adapters. Reject them by their
    // final component before walking the parent and authorization prefixes.
    // Supported artifacts and Downloads still pass the scope check below.
    let directory_kind = if meta.is_dir() {
        match path.file_name().and_then(OsStr::to_str) {
            Some(
                name @ ("node_modules" | "target" | ".venv" | "venv" | ".next" | ".nuxt" | ".turbo"
                | ".parcel-cache"),
            ) => Some(name),
            Some(name) if crate::project_providers::recognizes_name(OsStr::new(name)) => Some(name),
            _ => return Ok(None),
        }
    } else {
        None
    };
    let Some(parent) = path
        .parent()
        .filter(|parent| parent.starts_with(&root.path))
    else {
        return Ok(None);
    };
    if meta.is_dir() {
        match directory_kind {
            Some("node_modules") => match node_evidence_cached(root, parent, cancel, caches) {
                Ok(found) => Ok(found),
                Err(reason) => Ok(Some(Evidence {
                    kind: "node",
                    title: format!(
                        "{} dependencies",
                        parent.file_name().unwrap_or_default().to_string_lossy()
                    ),
                    explanation: "A dependency directory was found, but its installation ownership or layout could not be verified.",
                    consequence: "This diagnostic entry is unavailable for cleanup. Inspect the owning project and package-manager configuration first.",
                    fingerprint: format!("unverified-node-v{RULE_VERSION}"),
                    blocked: Some(reason),
                    latest_modified_ns: meta.identity.modified_ns,
                    quiet_days: DEVELOPER_QUIET_DAYS,
                    activity_root: None,
                })),
            },
            Some("target") => cargo_evidence(root, parent, path, cancel, caches),
            Some(".venv" | "venv") => venv_evidence(parent, path, cancel, caches),
            Some(".next" | ".nuxt" | ".turbo" | ".parcel-cache") => {
                webcache_evidence(parent, path, cancel, caches)
            }
            Some(name) if crate::project_providers::recognizes_name(OsStr::new(name)) => {
                crate::project_providers::identify(root, path, cancel).map(|found| {
                    found.map(|found| Evidence {
                        kind: found.kind,
                        title: found.title,
                        explanation: found.explanation,
                        consequence: found.consequence,
                        fingerprint: found.fingerprint,
                        blocked: found.blocked,
                        latest_modified_ns: found.latest_modified_ns,
                        quiet_days: recommendations::quiet_days(found.kind),
                        activity_root: Some(found.activity_root),
                    })
                })
            }
            _ => Ok(None),
        }
    } else if meta.is_file()
        && downloads.is_some_and(|boundary| path.starts_with(boundary))
        && !unfinished_download(downloads, path)
    {
        let kind = if recommendations::installer(path) {
            "installer"
        } else if recommendations::archive(path) {
            "archive"
        } else {
            "download"
        };
        Ok(everyday_evidence(path, meta, kind))
    } else if meta.is_file()
        && meta.identity.size >= recommendations::minimum_bytes("largefile")
        && recommendations::personal_scope(root, path)
        && path
            .file_name()
            .is_some_and(recommendations::personal_file_name)
        && !path
            .strip_prefix(&root.path)
            .unwrap()
            .components()
            .any(|part| unfinished_component(part.as_os_str()))
    {
        Ok(everyday_evidence(path, meta, "largefile"))
    } else {
        Ok(None)
    }
}

fn make_candidate(root: &Root, path: &Path, meta: &EntryMeta, found: &Evidence) -> Candidate {
    let mut hash = blake3::Hasher::new();
    hash.update(root.id.as_bytes());
    hash.update(path.as_os_str().as_bytes());
    Candidate {
        id: hash.finalize().to_hex()[..24].to_string(),
        root_id: root.id.clone(),
        path: path.to_path_buf(),
        title: found.title.clone(),
        kind: found.kind.into(),
        logical_bytes: 0,
        allocated_bytes: 0,
        file_count: 0,
        modified_ns: meta.identity.modified_ns.max(found.latest_modified_ns),
        explanation: found.explanation.into(),
        consequence: found.consequence.into(),
        eligible_permanent: false,
        suggestion_eligible: false,
        provisional: true,
        blocked_reason: Some(
            "Measuring and checking this item; cleanup is not yet available".into(),
        ),
        identity: meta.identity.clone(),
        fingerprint: String::new(),
        evidence: found.fingerprint.clone(),
    }
}

fn apply_measurement(candidate: &mut Candidate, measured: &Measurement) {
    candidate.logical_bytes = measured.logical_bytes;
    candidate.allocated_bytes = measured.allocated_bytes;
    candidate.file_count = measured.files;
    candidate.modified_ns = candidate.modified_ns.max(measured.latest_modified_ns);
    candidate.fingerprint.clone_from(&measured.fingerprint);
}

fn tally(stats: &mut ScanStats, links: &mut Hardlinks, meta: &EntryMeta, device: u64) {
    stats.entries += 1;
    if meta.identity.device != device || meta.is_dataless() {
        return;
    }
    if meta.is_dir() {
        stats.directories += 1;
    }
    if meta.is_file() {
        stats.files += 1;
        if links.first(meta) {
            stats.logical_bytes = stats.logical_bytes.saturating_add(meta.identity.size);
            stats.allocated_bytes = stats.allocated_bytes.saturating_add(meta.allocated);
        }
    }
}

/// Final components that can begin a recognized artifact boundary. Shared with
/// refresh invalidation so an event inside any of them remeasures the whole
/// artifact. The conditional names below still need their positive evidence.
pub(crate) fn artifact_component(name: &OsStr) -> bool {
    crate::project_providers::recognizes_name(name)
        || matches!(
            name.to_str(),
            Some(
                "node_modules"
                    | "target"
                    | ".venv"
                    | "venv"
                    | ".next"
                    | ".nuxt"
                    | ".turbo"
                    | ".parcel-cache"
            )
        )
}

fn is_artifact_name(path: &Path) -> bool {
    path.file_name().is_some_and(artifact_component)
}

/// Names that are artifacts only alongside their marker or sibling manifest.
/// Without that evidence the directory stays ordinary and is traversed, unlike
/// node_modules/target boundaries which never become ordinary content.
fn is_conditional_artifact_name(path: &Path) -> bool {
    path.file_name()
        .is_some_and(crate::project_providers::recognizes_name)
        || matches!(
            path.file_name().and_then(OsStr::to_str),
            Some(".venv" | "venv" | ".next" | ".nuxt" | ".turbo" | ".parcel-cache")
        )
}

/// An incremental event anywhere within a recognized artifact invalidates and
/// remeasures that entire artifact, rather than publishing its individual files.
fn scoped_start(root: &Root, scope: Option<&Path>) -> Result<PathBuf> {
    let scope = scope.unwrap_or(&root.path);
    // The journal preserves excluded scopes for no-probe reconciliation; the
    // standalone scanner must still reject the original protected input.
    safety::check_scope_policy(root, scope)?;
    crate::refresh::normalize_scope(root, scope)
}

struct ScanDirectory {
    directory: Directory,
    depth: usize,
    classify: bool,
    lane: usize,
}

struct DeferredArtifact {
    entry: Entry,
    evidence: Evidence,
    early_quiet: bool,
    blocked: Option<String>,
}

struct ArtifactReview {
    entry: Entry,
    found: Evidence,
    candidate: Candidate,
    blocked: Option<String>,
    is_dir: bool,
    cutoff: i64,
    can_learn: bool,
    recent_leaf: Option<PathBuf>,
}

impl ArtifactReview {
    fn retained_bytes(&self) -> usize {
        let candidate = &self.candidate;
        self.entry
            .path
            .as_os_str()
            .len()
            .saturating_add(candidate.id.len())
            .saturating_add(candidate.root_id.len())
            .saturating_add(candidate.path.as_os_str().len())
            .saturating_add(candidate.title.len())
            .saturating_add(candidate.kind.len())
            .saturating_add(candidate.explanation.len())
            .saturating_add(candidate.consequence.len())
            .saturating_add(candidate.fingerprint.len())
            .saturating_add(candidate.evidence.len())
            .saturating_add(candidate.blocked_reason.as_ref().map_or(0, String::len))
            .saturating_add(self.found.title.len())
            .saturating_add(self.found.fingerprint.len())
            .saturating_add(self.blocked.as_ref().map_or(0, String::len))
            .saturating_add(
                self.found
                    .activity_root
                    .as_ref()
                    .map_or(0, |path| path.as_os_str().len()),
            )
            .saturating_add(
                self.recent_leaf
                    .as_ref()
                    .map_or(0, |path| path.as_os_str().len()),
            )
    }
}

struct ArtifactMeasurement {
    review: ArtifactReview,
    cursor: safety::MeasurementCursor,
}

fn verify_deferred_artifact(
    root: &Root,
    entry: &Entry,
    found: &Evidence,
    downloads: Option<&Path>,
    cancel: &AtomicBool,
) -> Result<()> {
    safety::cancelled(cancel)?;
    if safety::metadata(&entry.path)? != entry.meta {
        return Err(
            "The artifact changed while waiting for metadata coverage; refresh this location"
                .into(),
        );
    }
    safety::cancelled(cancel)?;
    let current = evidence_with_downloads(root, &entry.path, &entry.meta, downloads, cancel)?
        .ok_or("Project ownership changed while waiting for metadata coverage")?;
    if current.fingerprint != found.fingerprint
        || current.blocked != found.blocked
        || current.latest_modified_ns != found.latest_modified_ns
        || current.activity_root != found.activity_root
    {
        return Err(
            "Project evidence changed while waiting for metadata coverage; refresh this location"
                .into(),
        );
    }
    safety::cancelled(cancel)
}

/// A failed or stale hint is only a cache miss. It must never hide an ordinary
/// traversal error, grant cleanup permission, or contribute measured bytes.
fn recent_file_modified(
    root: &Root,
    artifact: &Entry,
    path: &Path,
    cancel: &AtomicBool,
    checkpoint: &impl Fn(),
    cutoff: i64,
) -> Result<Option<i64>> {
    let observed = safety::scope_metadata_with_ancestor(root, path, artifact, cancel, checkpoint);
    safety::cancelled(cancel)?;
    Ok(observed
        .ok()
        .flatten()
        .filter(|meta| is_recent_local_file(meta, root.identity.device, cutoff))
        .map(|meta| meta.identity.modified_ns))
}

fn is_recent_local_file(meta: &EntryMeta, device: u64, cutoff: i64) -> bool {
    meta.identity.modified_ns > cutoff
        && meta.is_file()
        && !meta.is_dataless()
        && meta.identity.device == device
        && meta.links == 1
        && meta.uid == unsafe { libc::geteuid() }
}

fn activity_reason(
    cached: &mut Option<(Instant, Result<ActivitySnapshot>)>,
    project: &Path,
    kind: &str,
    cancel: &AtomicBool,
    max_age: Duration,
) -> Option<String> {
    match ActivitySnapshot::capture_with_max_age(cached, max_age, cancel) {
        Ok(snapshot) => snapshot.blocked_for(kind, project, cancel),
        Err(reason) => Some(reason.clone()),
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_artifact_review<F: FnMut(ScanBatch)>(
    mut review: ArtifactReview,
    measured: Result<Measurement>,
    root: &Root,
    cancel: &AtomicBool,
    stats: &mut ScanStats,
    activity: &mut Option<(Instant, Result<ActivitySnapshot>)>,
    caches: &mut EvidenceCaches,
    downloads: Option<&Path>,
    recent_files: Option<&mut RecentFileHints>,
    publisher: &mut Publisher<F>,
) {
    let mut quality_reason = Some("Measurement is incomplete".to_owned());
    match measured {
        Ok(measured) => {
            stats.skipped += measured.skipped;
            stats.errors += measured.errors;
            if measured.pruned {
                stats.excluded_artifacts += 1;
                if measured.errors == 0
                    && let Some(path) = review.recent_leaf.as_deref()
                    && let Some(hints) = recent_files
                {
                    hints.remember(root, &review.entry.path, path);
                }
            }
            apply_measurement(&mut review.candidate, &measured);
            quality_reason = suggestion_reason(&review.found, &measured, clock_ns());
            review.blocked = review.blocked.or(measured.unsafe_reason);
            if measured.pruned {
                quality_reason = Some(
                    "Measurement stopped when this artifact became ineligible; remaining contents were not traversed"
                        .into(),
                );
            }
        }
        Err(reason) => {
            review.blocked = Some(reason);
            if safety::cancelled(cancel).is_err() {
                stats.cancelled = true;
            } else {
                stats.errors += 1;
            }
        }
    }
    if recommendations::checks_git(review.found.kind)
        && review.blocked.is_none()
        && quality_reason.is_none()
    {
        let project = review.entry.path.parent().unwrap();
        if let Err(reason) = git_untracked(root, project, &review.entry.path, cancel) {
            review.blocked = Some(reason);
        }
    }
    if recommendations::checks_activity(review.found.kind)
        && review.blocked.is_none()
        && quality_reason.is_none()
    {
        review.blocked = activity_reason(
            activity,
            review
                .found
                .activity_root
                .as_deref()
                .unwrap_or_else(|| review.entry.path.parent().unwrap()),
            review.found.kind,
            cancel,
            SCAN_ACTIVITY_MAX_AGE,
        );
    }
    // Evidence captured before a queued or yielded measurement is never enough
    // to publish an actionable row. Re-read it after the terminal measurement.
    if review.blocked.is_none() && quality_reason.is_none() {
        match evidence_with_downloads_cached(
            root,
            &review.entry.path,
            &review.entry.meta,
            downloads,
            cancel,
            Some(caches),
        ) {
            Ok(Some(current))
                if current.fingerprint == review.found.fingerprint && current.blocked.is_none() => {
            }
            _ => {
                review.blocked =
                    Some("Project evidence changed during the scan; refresh this review".into());
            }
        }
    }
    if quality_reason.is_none() && review.candidate.fingerprint.is_empty() {
        quality_reason = Some(
            "This was a diagnostic-only measurement; refresh to review current eligibility".into(),
        );
    }
    review.candidate.blocked_reason = review.blocked;
    review.candidate.provisional = false;
    review.candidate.suggestion_eligible =
        review.candidate.blocked_reason.is_none() && quality_reason.is_none() && !stats.cancelled;
    review.candidate.eligible_permanent =
        recommendations::permanent_kind(review.found.kind) && review.candidate.suggestion_eligible;
    let first_finding = review.candidate.suggestion_eligible && stats.first_finding_ms.is_none();
    if review.candidate.suggestion_eligible {
        stats.candidates += 1;
        stats.first_finding_ms.get_or_insert(stats.elapsed_ms);
        review.candidate.explanation.push_str(&format!(
            " At least {} MB is allocated locally. The {} have been unmodified for at least {} days.",
            recommendations::minimum_bytes(review.found.kind) / 1_000_000,
            if review.is_dir {
                "contents and identification files"
            } else {
                "file contents"
            },
            review.found.quiet_days
        ));
    } else {
        stats.skipped += 1;
        if let Some(reason) = quality_reason {
            review
                .candidate
                .explanation
                .push_str(&format!(" Not suggested: {reason}."));
        }
    }
    publisher.queue(review.candidate, stats, first_finding);
}

#[allow(clippy::too_many_arguments)]
fn advance_artifact_measurement<F: FnMut(ScanBatch)>(
    mut job: ArtifactMeasurement,
    root: &Root,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    checkpoint: &impl Fn(),
    stats: &mut ScanStats,
    links: &mut Hardlinks,
    activity: &mut Option<(Instant, Result<ActivitySnapshot>)>,
    caches: &mut EvidenceCaches,
    downloads: Option<&Path>,
    recent_files: Option<&mut RecentFileHints>,
    publisher: &mut Publisher<F>,
    started: Instant,
) -> Option<ArtifactMeasurement> {
    let entry_path = &job.review.entry.path;
    let candidate = &mut job.review.candidate;
    let recent_leaf = &mut job.review.recent_leaf;
    let can_learn = job.review.can_learn;
    let cutoff = job.review.cutoff;
    let measured = job.cursor.advance(
        cancel,
        MEASUREMENT_QUANTUM_ENTRIES,
        Instant::now() + MEASUREMENT_QUANTUM,
        |observed, partial| {
            if observed.path != *entry_path {
                tally(stats, links, &observed.meta, root.identity.device);
                if can_learn
                    && recent_leaf.is_none()
                    && partial.errors == 0
                    && partial.unsafe_reason.is_none()
                    && is_recent_local_file(&observed.meta, root.identity.device, cutoff)
                    && !kept.iter().any(|kept| observed.path.starts_with(kept))
                {
                    *recent_leaf = Some(observed.path.clone());
                }
            }
            if publisher.last.elapsed() >= BATCH_INTERVAL {
                stats.elapsed_ms = started.elapsed().as_millis() as u64;
                apply_measurement(candidate, partial);
                publisher.queue(candidate.clone(), stats, true);
                // Publishing has returned and released engine/index locks.
                checkpoint();
            }
            Ok(())
        },
    );
    match measured {
        Ok(safety::MeasurementProgress::Pending) => Some(job),
        Ok(safety::MeasurementProgress::Complete(measured)) => {
            stats.elapsed_ms = started.elapsed().as_millis() as u64;
            finish_artifact_review(
                job.review,
                Ok(measured),
                root,
                cancel,
                stats,
                activity,
                caches,
                downloads,
                recent_files,
                publisher,
            );
            None
        }
        Err(reason) => {
            stats.elapsed_ms = started.elapsed().as_millis() as u64;
            finish_artifact_review(
                job.review,
                Err(reason),
                root,
                cancel,
                stats,
                activity,
                caches,
                downloads,
                recent_files,
                publisher,
            );
            None
        }
    }
}

pub fn scan(
    root: &Root,
    scope: Option<&Path>,
    cancel: &AtomicBool,
    publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    scan_with_exclusions(root, scope, &[], cancel, publish)
}

pub fn scan_with_exclusions(
    root: &Root,
    scope: Option<&Path>,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    scan_with_checkpoint(root, scope, kept, cancel, || {}, publish)
}

pub fn scan_with_checkpoint(
    root: &Root,
    scope: Option<&Path>,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    checkpoint: impl Fn(),
    publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    scan_with_checkpoint_mode(
        root,
        scope,
        kept,
        cancel,
        ScanMode::Suggestions,
        checkpoint,
        publish,
    )
}

pub fn scan_with_checkpoint_mode(
    root: &Root,
    scope: Option<&Path>,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    mode: ScanMode,
    checkpoint: impl Fn(),
    publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    scan_with_options(
        root,
        scope,
        kept,
        cancel,
        ScanOptions {
            mode,
            recent_files: None,
        },
        checkpoint,
        publish,
    )
}

pub(crate) struct ScanOptions<'a> {
    pub mode: ScanMode,
    /// The caller owns a disposable local pool, never the live runtime pool.
    /// Every hit freshly verifies the file and selected artifact's ancestry.
    pub recent_files: Option<&'a mut RecentFileHints>,
}

pub(crate) fn scan_with_options(
    root: &Root,
    scope: Option<&Path>,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    mut options: ScanOptions<'_>,
    checkpoint: impl Fn(),
    publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    let mut session = ScanSession::new(options.mode);
    let selected = scope.unwrap_or(&root.path);
    if root.kind == "home"
        && (selected == root.path || recommendations::library_corridor(root, selected))
    {
        safety::check_scope_policy(root, selected)?;
        safety::validate_root(root)?;
        let mut lanes: Vec<PathBuf> = recommendations::HOME_LIBRARY_ROUTES
            .iter()
            .map(|route| root.path.join(route))
            .filter(|path| path.starts_with(selected))
            .collect();
        // Normal Home discovery still excludes Library before metadata. These
        // three fixed, grant-anchored probes never enumerate other Library data.
        // Reuse one session so hard-link accounting remains shared across lanes.
        if selected == root.path {
            lanes.push(root.path.clone());
        }
        return session.scan(
            root,
            ScanScope {
                path: Some(selected),
                expected: None,
                recent_files: options.recent_files.as_deref_mut(),
                starts: Some(&lanes),
            },
            kept,
            cancel,
            checkpoint,
            publish,
        );
    }
    session.scan(
        root,
        ScanScope {
            path: scope,
            expected: None,
            recent_files: options.recent_files,
            starts: None,
        },
        kept,
        cancel,
        checkpoint,
        publish,
    )
}

/// A lockfile refresh covers the original item and its immediate build output.
/// The latter is selected by exact directory-entry spelling, because an APFS
/// lookup for a synthetic `target` path may otherwise resolve `Target`.
pub(crate) fn scan_cargo_lock_with_checkpoint_mode(
    root: &Root,
    origin: &Path,
    kept: &[PathBuf],
    cancel: &AtomicBool,
    mode: ScanMode,
    checkpoint: impl Fn(),
    mut publish: impl FnMut(ScanBatch),
) -> Result<ScanStats> {
    let target = crate::refresh::cargo_lock_target(root, origin)?
        .ok_or("The lockfile refresh is not an authorized dependency scope")?;
    let started = Instant::now();
    let mut session = ScanSession::new(mode);
    let origin_stats = session.scan(
        root,
        ScanScope {
            path: Some(origin),
            expected: None,
            recent_files: None,
            starts: None,
        },
        kept,
        cancel,
        &checkpoint,
        |mut batch| {
            // The second footprint has not been examined yet.
            batch.stats.complete = false;
            publish(batch);
        },
    )?;
    if origin_stats.cancelled || safety::cancelled(cancel).is_err() {
        return Ok(ScanStats {
            complete: false,
            cancelled: true,
            ..origin_stats
        });
    }

    let mut candidate: Option<Candidate> = None;
    let target_stats = if kept.iter().any(|path| target.starts_with(path)) {
        ScanStats {
            complete: true,
            skipped: 1,
            ..Default::default()
        }
    } else {
        let guard = safety::ExactChild::observe(root, &target, cancel, &checkpoint)?;
        let measured = if let Some(expected) = guard.metadata() {
            let mut invalid = false;
            let stats = session.scan(
                root,
                ScanScope {
                    path: Some(&target),
                    expected: Some(expected),
                    recent_files: None,
                    starts: None,
                },
                kept,
                cancel,
                &checkpoint,
                |batch| {
                    // An artifact boundary produces at most one distinct row.
                    // Keep only its latest version, never all progress batches.
                    // Neither a row nor earned-finding counters become visible
                    // until the exact namespace and selected object are verified.
                    for next in batch.candidates {
                        if next.path != target
                            || next.root_id != root.id
                            || next.identity != expected.identity
                            || candidate.as_ref().is_some_and(|prior| prior.id != next.id)
                        {
                            invalid = true;
                        } else {
                            candidate = Some(next);
                        }
                    }
                    let mut visible = batch.stats;
                    visible.candidates = 0;
                    visible.first_finding_ms = None;
                    let mut stats = crate::combine_stats(&origin_stats, &visible);
                    stats.complete = false;
                    stats.cancelled |= origin_stats.cancelled;
                    stats.elapsed_ms = started.elapsed().as_millis() as u64;
                    publish(ScanBatch {
                        candidates: Vec::new(),
                        stats,
                    });
                },
            )?;
            if invalid {
                return Err("The selected build output changed during its refresh".into());
            }
            stats
        } else {
            ScanStats {
                complete: true,
                ..Default::default()
            }
        };
        guard.validate(root, cancel, &checkpoint)?;
        measured
    };
    let mut stats = crate::combine_stats(&origin_stats, &target_stats);
    stats.complete = origin_stats.complete && target_stats.complete;
    stats.cancelled |= origin_stats.cancelled;
    stats.elapsed_ms = started.elapsed().as_millis() as u64;
    if origin_stats.first_finding_ms.is_none() && target_stats.first_finding_ms.is_some() {
        stats.first_finding_ms = Some(stats.elapsed_ms);
    }
    if stats.complete {
        stats.message = "Lockfile and build output refresh complete.".into();
    }
    publish(ScanBatch {
        candidates: candidate.into_iter().collect(),
        stats: stats.clone(),
    });
    Ok(stats)
}

/// Both leaves of a dependency refresh share hard-link accounting. Traversal
/// queues, evidence caches and measurement fingerprints remain local to a leaf.
struct ScanSession {
    mode: ScanMode,
    links: Hardlinks,
}

struct ScanScope<'a> {
    path: Option<&'a Path>,
    expected: Option<&'a EntryMeta>,
    recent_files: Option<&'a mut RecentFileHints>,
    /// Fixed grant-anchored logical lanes advanced within one fair scheduler.
    starts: Option<&'a [PathBuf]>,
}

impl ScanSession {
    fn new(mode: ScanMode) -> Self {
        Self {
            mode,
            links: Hardlinks::default(),
        }
    }

    fn scan(
        &mut self,
        root: &Root,
        mut scope: ScanScope<'_>,
        kept: &[PathBuf],
        cancel: &AtomicBool,
        checkpoint: impl Fn(),
        publish: impl FnMut(ScanBatch),
    ) -> Result<ScanStats> {
        let mode = self.mode;
        let links = &mut self.links;
        let _local_io = safety::LocalOnlyIo::new()?;
        let started = Instant::now();
        let mut stats = ScanStats {
            message: "Scanning authorized local files…".into(),
            ..ScanStats::default()
        };
        let mut publisher = Publisher::new(publish);
        safety::cancelled(cancel)?;
        let selected = scoped_start(root, scope.path)?;
        let logical_lanes = scope.starts.is_some();
        let default_start = [selected.clone()];
        let starts = scope.starts.unwrap_or(&default_start);
        if starts.len() > MAX_SCAN_LANES {
            return Err("The scan exceeds the bounded logical-lane limit".into());
        }
        if scope.expected.is_some() && starts.len() != 1 {
            return Err("An exact refresh cannot span multiple logical lanes".into());
        }
        let mut next = VecDeque::new();
        // Use the same lookup for existence and initial metadata. A short-lived
        // incremental scope may disappear before discovery starts; only a verified
        // absent descendant is complete with no entries. The grant itself is strict.
        for (lane, requested) in starts.iter().enumerate() {
            safety::cancelled(cancel)?;
            if kept.iter().any(|path| requested.starts_with(path)) {
                stats.skipped += 1;
                continue;
            }
            let start = match scoped_start(root, Some(requested)) {
                Ok(start) => start,
                Err(_) if logical_lanes => {
                    stats.errors += 1;
                    continue;
                }
                Err(reason) => return Err(reason),
            };
            let observed = if start == root.path {
                safety::validate_root(root).and_then(|()| safety::metadata(&start).map(Some))
            } else {
                safety::scope_metadata(root, &start, cancel)
            };
            let meta = match observed {
                Ok(Some(meta)) => meta,
                Ok(None) => {
                    if scope.expected.is_some() {
                        return Err(
                            "The selected refresh scope disappeared before traversal".into()
                        );
                    }
                    if logical_lanes {
                        continue;
                    }
                    stats.complete = true;
                    stats.elapsed_ms = started.elapsed().as_millis() as u64;
                    stats.message = "Removed scope reconciled without scanning its parent.".into();
                    return Ok(stats);
                }
                Err(_) if logical_lanes && safety::cancelled(cancel).is_ok() => {
                    stats.errors += 1;
                    continue;
                }
                Err(reason) => return Err(reason),
            };
            if scope.expected.is_some_and(|expected| expected != &meta) {
                return Err("The selected refresh scope changed before traversal".into());
            }
            next.push_back((Entry { path: start, meta }, 0, true, lane));
        }
        let mut frontier: VecDeque<ScanDirectory> = VecDeque::new();
        let mut deferred: VecDeque<DeferredArtifact> = VecDeque::new();
        let mut measurements: VecDeque<ArtifactMeasurement> = VecDeque::new();
        let mut measurement_turn = false;
        let mut lane_turn = 0;
        let mut activity = None;
        let mut caches = EvidenceCaches::default();
        let downloads = downloads_boundary(root);
        loop {
            checkpoint();
            if safety::cancelled(cancel).is_err() {
                stats.cancelled = true;
                break;
            }
            if publisher.last.elapsed() >= BATCH_INTERVAL {
                stats.elapsed_ms = started.elapsed().as_millis() as u64;
                publisher.flush(&stats);
            }
            let discovery_done = next.is_empty() && frontier.is_empty() && deferred.is_empty();
            if !measurements.is_empty()
                && (measurement_turn
                    || measurements.len() >= MAX_ACTIVE_MEASUREMENTS
                    || discovery_done)
            {
                measurement_turn = false;
                let job = measurements
                    .pop_front()
                    .expect("the measurement queue was checked above");
                if let Some(job) = advance_artifact_measurement(
                    job,
                    root,
                    kept,
                    cancel,
                    &checkpoint,
                    &mut stats,
                    links,
                    &mut activity,
                    &mut caches,
                    downloads.as_deref(),
                    scope.recent_files.as_deref_mut(),
                    &mut publisher,
                    started,
                ) {
                    measurements.push_back(job);
                }
                if stats.cancelled {
                    break;
                }
                continue;
            }
            measurement_turn = true;
            // Explicit metadata coverage postpones known non-suggestions while
            // shallow discovery can still find useful work. Interactive discovery
            // never queues them. Drain the oldest item at capacity so this queue
            // never grows with the number of projects on disk.
            let deferred_job = if deferred.len() == MAX_DEFERRED_ARTIFACTS
                || (next.is_empty() && frontier.is_empty())
            {
                deferred.pop_front()
            } else {
                None
            };
            let (entry, depth, classify, lane, previous_checks, opened_directory) =
                if let Some(job) = deferred_job {
                    (
                        job.entry,
                        0,
                        false,
                        0,
                        Some((job.evidence, job.early_quiet, job.blocked)),
                        None,
                    )
                } else if let Some((entry, depth, classify, lane)) = next.pop_front() {
                    (entry, depth, classify, lane, None, None)
                } else {
                    if logical_lanes && !frontier.is_empty() {
                        for offset in 0..starts.len() {
                            let lane = (lane_turn + offset) % starts.len();
                            if let Some(index) =
                                frontier.iter().position(|frame| frame.lane == lane)
                            {
                                frontier.rotate_left(index);
                                lane_turn = (lane + 1) % starts.len();
                                break;
                            }
                        }
                    }
                    let Some(frame) = frontier.front_mut() else {
                        break;
                    };
                    let library = recommendations::library_area(root, &frame.directory.path);
                    let next_entry = if library.is_some()
                        || (mode == ScanMode::Suggestions
                            && !downloads
                                .as_ref()
                                .is_some_and(|path| frame.directory.path.starts_with(path)))
                    {
                        let home_children =
                            root.kind == "home" && frame.directory.path == root.path;
                        let step = if let Some((area, suffix)) = library {
                            frame.directory.next_library_discovery(
                                cancel,
                                area == recommendations::LibraryArea::Caches
                                    && suffix.as_os_str().is_empty(),
                            )
                        } else if recommendations::personal_scope(root, &frame.directory.path) {
                            frame
                                .directory
                                .next_personal_discovery(cancel, home_children)
                        } else {
                            frame.directory.next_discovery(cancel, home_children)
                        };
                        match step {
                            Ok(step) => {
                                stats.entries += step.files + step.skipped;
                                stats.files += step.files;
                                stats.skipped += step.skipped;
                                stats.metadata_skipped += step.metadata_skipped;
                                if step.entry.is_none() && !step.finished {
                                    continue;
                                }
                                match step.entry {
                                    Some(DiscoveryEntry::Directory(path)) => {
                                        // Keep is a lexical boundary, so avoid opening
                                        // or initializing a reader for any kept subtree.
                                        if kept.iter().any(|kept| path.starts_with(kept)) {
                                            stats.entries += 1;
                                            stats.directories += 1;
                                            stats.skipped += 1;
                                            stats.metadata_skipped += 1;
                                            continue;
                                        }
                                        match frame.directory.open_discovered(
                                            path,
                                            root.identity.device,
                                            cancel,
                                        ) {
                                            Ok((entry, directory)) => Ok(Some((entry, directory))),
                                            Err(reason) if safety::cancelled(cancel).is_err() => {
                                                Err(reason)
                                            }
                                            Err(_) => {
                                                stats.entries += 1;
                                                stats.directories += 1;
                                                stats.errors += 1;
                                                stats.skipped += 1;
                                                continue;
                                            }
                                        }
                                    }
                                    Some(DiscoveryEntry::Metadata(entry)) => {
                                        Ok(Some((entry, None)))
                                    }
                                    None => Ok(None),
                                }
                            }
                            Err(reason) => Err(reason),
                        }
                    } else {
                        frame
                            .directory
                            .next(cancel)
                            .map(|entry| entry.map(|entry| (entry, None)))
                    };
                    match next_entry {
                        Ok(Some((entry, opened))) => (
                            entry,
                            frame.depth + 1,
                            frame.classify,
                            frame.lane,
                            None,
                            opened,
                        ),
                        Ok(None) => {
                            if frame.directory.unchanged().is_err() {
                                stats.errors += 1;
                            }
                            frontier.pop_front();
                            continue;
                        }
                        Err(_) if safety::cancelled(cancel).is_err() => {
                            stats.cancelled = true;
                            break;
                        }
                        Err(_) => {
                            stats.errors += 1;
                            frontier.pop_front();
                            continue;
                        }
                    }
                };
            let was_deferred = previous_checks.is_some();
            if !was_deferred {
                // A queued root was already counted when first discovered. Its
                // descendants still use the same global hard-link accounting below.
                tally(&mut stats, links, &entry.meta, root.identity.device);
            }
            let is_dir = entry.meta.is_dir();
            if kept.iter().any(|path| entry.path.starts_with(path))
                || unfinished_download(downloads.as_deref(), &entry.path)
            {
                stats.skipped += 1;
                continue;
            }
            if entry.meta.identity.device != root.identity.device
                || entry.meta.is_symlink()
                || entry.meta.is_dataless()
                || safety::excluded_home_media(root, &entry.path)
                || safety::excluded_name(entry.path.file_name().unwrap_or_default(), is_dir)
                || (recommendations::library_area(root, &entry.path).is_some()
                    && !recommendations::library_route_allowed(root, &entry.path))
                || (!is_dir && !entry.meta.is_file())
            {
                stats.skipped += 1;
                continue;
            }
            if mode == ScanMode::Suggestions
                && classify
                && is_dir
                && entry.path != root.path
                && is_artifact_name(&entry.path)
                && !is_conditional_artifact_name(&entry.path)
                && !quiet_for(
                    entry.meta.identity.modified_ns,
                    clock_ns(),
                    DEVELOPER_QUIET_DAYS,
                )
            {
                // Unconditional artifact names are boundaries even without
                // ownership evidence. Conditional names may instead be ordinary
                // folders containing older projects, so recognize those first.
                // Evidence can only make a recognized artifact's date newer.
                stats.skipped += 1;
                stats.excluded_artifacts += 1;
                continue;
            }
            let mut classify_children = classify;
            let (found, previous_checks) = if let Some((found, quiet, blocked)) = previous_checks {
                (Ok(Some(found)), Some((quiet, blocked)))
            } else if classify && entry.path != root.path {
                (
                    evidence_with_downloads_cached(
                        root,
                        &entry.path,
                        &entry.meta,
                        downloads.as_deref(),
                        cancel,
                        Some(&mut caches),
                    ),
                    None,
                )
            } else {
                (Ok(None), None)
            };
            match found {
                Ok(Some(found)) => {
                    // Keep protects a descendant from removal with a newly
                    // recognized parent artifact too. Only prune after positive
                    // recognition: ordinary ancestors must still discover their
                    // other children. No measurement may enter this artifact.
                    if kept.iter().any(|kept| kept.starts_with(&entry.path)) {
                        stats.skipped += 1;
                        if is_dir {
                            stats.excluded_artifacts += 1;
                        }
                        continue;
                    }
                    if mode == ScanMode::Suggestions
                        && is_dir
                        && is_conditional_artifact_name(&entry.path)
                        && !quiet_for(
                            entry.meta.identity.modified_ns,
                            clock_ns(),
                            found.quiet_days,
                        )
                    {
                        // The marker establishes this conditional boundary;
                        // its recent date excludes it without enumerating it.
                        stats.skipped += 1;
                        stats.excluded_artifacts += 1;
                        continue;
                    }
                    // Artifact measurement owns a separate validated traversal. Do
                    // not retain an unused discovery descriptor alongside its stack.
                    drop(opened_directory);
                    stats.elapsed_ms = started.elapsed().as_millis() as u64;
                    let mut candidate = make_candidate(root, &entry.path, &entry.meta, &found);
                    // Diagnostics stay in the index, but only completed useful rows
                    // become public suggestions. Cheap evidence, age and activity
                    // checks can exclude the whole artifact before opening it.
                    let (early_quiet, blocked) = if let Some(previous) = previous_checks {
                        previous
                    } else {
                        let quiet = quiet_for(
                            entry
                                .meta
                                .identity
                                .modified_ns
                                .max(found.latest_modified_ns),
                            clock_ns(),
                            found.quiet_days,
                        );
                        let mut blocked = found.blocked.clone();
                        if recommendations::checks_activity(found.kind)
                            && blocked.is_none()
                            && quiet
                        {
                            blocked = activity_reason(
                                &mut activity,
                                found
                                    .activity_root
                                    .as_deref()
                                    .unwrap_or_else(|| entry.path.parent().unwrap()),
                                found.kind,
                                cancel,
                                SCAN_ACTIVITY_MAX_AGE,
                            );
                        }
                        (quiet, blocked)
                    };
                    if was_deferred {
                        if let Err(reason) = verify_deferred_artifact(
                            root,
                            &entry,
                            &found,
                            downloads.as_deref(),
                            cancel,
                        ) {
                            if safety::cancelled(cancel).is_err() {
                                stats.cancelled = true;
                            } else {
                                stats.errors += 1;
                            }
                            stats.skipped += 1;
                            candidate.blocked_reason = Some(reason);
                            candidate.provisional = false;
                            publisher.queue(candidate, &stats, false);
                            continue;
                        }
                    } else if is_dir && (!early_quiet || blocked.is_some()) {
                        if mode == ScanMode::Suggestions {
                            stats.skipped += 1;
                            stats.excluded_artifacts += 1;
                            candidate.blocked_reason = blocked.or_else(|| {
                                Some(format!(
                                    "Recently modified; recommendations require {} quiet days",
                                    found.quiet_days
                                ))
                            });
                            candidate.provisional = false;
                            candidate.explanation.push_str(
                            " Not suggested: this artifact is already excluded by its ownership, modification time or current activity. Its contents were not traversed or measured.",
                        );
                            publisher.queue(candidate, &stats, false);
                            continue;
                        }
                        publisher.queue(candidate, &stats, false);
                        deferred.push_back(DeferredArtifact {
                            entry,
                            evidence: found,
                            early_quiet,
                            blocked,
                        });
                        continue;
                    }
                    if mode == ScanMode::Suggestions
                        && !was_deferred
                        && is_dir
                        && early_quiet
                        && blocked.is_none()
                        && let Some(path) = scope
                            .recent_files
                            .as_deref()
                            .and_then(|hints| hints.get(&root.id, &entry.path))
                    {
                        let proof = if kept.iter().any(|kept| path.starts_with(kept)) {
                            Ok(None)
                        } else {
                            recent_file_modified(
                                root,
                                &entry,
                                path,
                                cancel,
                                &checkpoint,
                                clock_ns().saturating_sub(found.quiet_days.saturating_mul(DAY_NS)),
                            )
                        };
                        let modified = match proof {
                            Ok(modified) => modified,
                            Err(_) => {
                                stats.cancelled = true;
                                break;
                            }
                        };
                        if let Some(modified_ns) = modified {
                            stats.skipped += 1;
                            stats.excluded_artifacts += 1;
                            candidate.modified_ns = candidate.modified_ns.max(modified_ns);
                            candidate.provisional = false;
                            candidate.blocked_reason = Some(format!(
                                "Artifact contents changed within the required {} quiet days",
                                found.quiet_days
                            ));
                            candidate.explanation.push_str(
                            " A recently modified local file was verified inside this artifact. Its contents were not traversed or measured.",
                        );
                            publisher.queue(candidate, &stats, false);
                            continue;
                        }
                        // Missing, aged, or unsafe paths are only local misses.
                        // Ordinary traversal still proves current eligibility.
                        if let Some(hints) = scope.recent_files.as_deref_mut() {
                            hints.remove(&root.id, &entry.path);
                        }
                    }
                    publisher.queue(candidate.clone(), &stats, false);
                    let cutoff = clock_ns().saturating_sub(found.quiet_days.saturating_mul(DAY_NS));
                    let can_learn = mode == ScanMode::Suggestions
                        && !was_deferred
                        && is_dir
                        && early_quiet
                        && blocked.is_none()
                        && scope.recent_files.is_some();
                    let policy = if recommendations::developer_measurement(found.kind) {
                        MeasurementPolicy::Developer
                    } else {
                        MeasurementPolicy::Strict
                    };
                    let cursor = if mode == ScanMode::Suggestions
                        && !was_deferred
                        && early_quiet
                        && blocked.is_none()
                    {
                        safety::MeasurementCursor::suggestion(
                            &entry.path,
                            root.identity.device,
                            policy,
                            cutoff,
                            cancel,
                        )
                    } else if !was_deferred && early_quiet && blocked.is_none() {
                        safety::MeasurementCursor::full(
                            &entry.path,
                            root.identity.device,
                            policy,
                            cancel,
                        )
                    } else {
                        safety::MeasurementCursor::metadata(
                            &entry.path,
                            root.identity.device,
                            policy,
                            cancel,
                        )
                    };
                    stats.elapsed_ms = started.elapsed().as_millis() as u64;
                    let review = ArtifactReview {
                        entry,
                        found,
                        candidate,
                        blocked,
                        is_dir,
                        cutoff,
                        can_learn,
                        recent_leaf: None,
                    };
                    if review.retained_bytes() > MAX_MEASUREMENT_JOB_BYTES {
                        finish_artifact_review(
                            review,
                            Err(
                                "Artifact scheduling metadata exceeds the bounded queue limit"
                                    .into(),
                            ),
                            root,
                            cancel,
                            &mut stats,
                            &mut activity,
                            &mut caches,
                            downloads.as_deref(),
                            scope.recent_files.as_deref_mut(),
                            &mut publisher,
                        );
                    } else {
                        match cursor {
                            Ok(cursor) => {
                                measurements.push_back(ArtifactMeasurement { review, cursor })
                            }
                            Err(reason) => finish_artifact_review(
                                review,
                                Err(reason),
                                root,
                                cancel,
                                &mut stats,
                                &mut activity,
                                &mut caches,
                                downloads.as_deref(),
                                scope.recent_files.as_deref_mut(),
                                &mut publisher,
                            ),
                        }
                    }
                    if stats.cancelled {
                        break;
                    }
                    continue;
                }
                Err(_) => {
                    stats.skipped += 1;
                    if mode == ScanMode::Suggestions && is_artifact_name(&entry.path) {
                        stats.excluded_artifacts += 1;
                        continue;
                    }
                    classify_children = false;
                }
                Ok(None) => {
                    // A conditional artifact name without its positive evidence
                    // is an ordinary folder: traversed, measured, and free to
                    // contain further classified projects.
                    if classify
                        && is_artifact_name(&entry.path)
                        && !is_conditional_artifact_name(&entry.path)
                        && entry.path != root.path
                    {
                        stats.skipped += 1;
                        if mode == ScanMode::Suggestions {
                            stats.excluded_artifacts += 1;
                            continue;
                        }
                        classify_children = false;
                    }
                }
            }
            if is_dir {
                // Explicit metadata mode covers unsupported artifacts without
                // reclassifying their internals. A bounded breadth-first frontier
                // favors shallow useful projects; overflow switches to depth first.
                if depth >= safety::MAX_DEPTH {
                    stats.skipped += 1;
                    stats.errors += 1;
                    continue;
                }
                let opened = match opened_directory {
                    Some(directory) => Ok(directory),
                    None if depth == 0 => Directory::open(&entry.path),
                    None => match frontier.front() {
                        Some(parent) => parent.directory.open_child(&entry),
                        None => Directory::open(&entry.path),
                    },
                };
                match opened {
                    Ok(directory) => {
                        let frame = ScanDirectory {
                            directory,
                            depth,
                            classify: classify_children,
                            lane,
                        };
                        if frontier.len() < MAX_SHALLOW_FRONTIER {
                            frontier.push_back(frame);
                        } else {
                            frontier.push_front(frame);
                        }
                    }
                    Err(_) => {
                        stats.errors += 1;
                        stats.skipped += 1;
                    }
                }
            }
            if publisher.last.elapsed() >= BATCH_INTERVAL {
                stats.elapsed_ms = started.elapsed().as_millis() as u64;
                publisher.flush(&stats);
            }
        }
        stats.elapsed_ms = started.elapsed().as_millis() as u64;
        if links.saturated() {
            stats.errors += 1;
        }
        stats.complete = !stats.cancelled && stats.errors == 0;
        stats.message = if logical_lanes && stats.cancelled {
            "Scan cancelled; completed findings remain available.".into()
        } else if logical_lanes && stats.errors > 0 {
            "Scan finished with inaccessible locations; completed findings are ready to review."
                .into()
        } else if logical_lanes {
            "Scan complete. Targeted cleanup and personal-file findings are ready to review.".into()
        } else if stats.cancelled {
            "Scan cancelled; the displayed coverage is partial".into()
        } else if links.saturated() {
            "Partial accounting: the bounded hard-link identity limit was reached; additional shared files received zero size credit".into()
        } else if stats.errors > 0 {
            format!(
                "Partial coverage: {} inaccessible or changed portions; {} excluded boundaries",
                stats.errors, stats.skipped
            )
        } else if mode == ScanMode::Suggestions {
            format!(
                "Suggestion discovery complete; {} entries examined and {} ineligible artifact contents excluded from traversal",
                stats.entries, stats.excluded_artifacts
            )
        } else {
            format!(
                "Scan complete within the selected scope; {} protected, unsupported, kept, or unqualified opportunities excluded",
                stats.skipped
            )
        };
        publisher.flush(&stats);
        Ok(stats)
    }
}

pub fn revalidate(root: &Root, candidate: &Candidate, cancel: &AtomicBool) -> Result<()> {
    revalidate_observing(root, candidate, cancel, |_, _| Ok(()))
}

/// Streams identities during the full mutation validation. Observations are
/// provisional until every ownership, policy, fingerprint and Git check has
/// passed; callers must roll back their manifest if this returns an error.
pub(crate) fn revalidate_observing(
    root: &Root,
    candidate: &Candidate,
    cancel: &AtomicBool,
    observe: impl FnMut(&Entry, &Measurement) -> Result<()>,
) -> Result<()> {
    let _local_io = safety::LocalOnlyIo::new()?;
    safety::cancelled(cancel)?;
    safety::validate_root(root)?;
    if candidate.root_id != root.id
        || candidate.path == root.path
        || !candidate.path.starts_with(&root.path)
    {
        return Err("The item is outside its authorized location".into());
    }
    safety::check_scope_policy(root, &candidate.path)?;
    if let Some(reason) = &candidate.blocked_reason {
        return Err(format!("This item is not available for cleanup: {reason}"));
    }
    let meta = safety::metadata(&candidate.path)?;
    if meta.identity != candidate.identity || meta.identity.device != root.identity.device {
        return Err("The item changed since review; scan it again".into());
    }
    safety::validate_ancestors(candidate.path.parent().ok_or("No item parent")?)?;
    let current = evidence(root, &candidate.path, &meta, cancel)?
        .ok_or("The item's project evidence is no longer recognized")?;
    if current.kind != candidate.kind || current.fingerprint != candidate.evidence {
        return Err("Project configuration changed since review".into());
    }
    if let Some(reason) = &current.blocked {
        return Err(reason.clone());
    }
    if candidate.eligible_permanent && !recommendations::permanent_kind(current.kind) {
        return Err(
            "This category is review and Trash-only; permanent cleanup is not allowed".into(),
        );
    }
    let mut activity = None;
    let project = candidate.path.parent().unwrap();
    let git_evidence = if recommendations::checks_git(current.kind) {
        git_untracked(root, project, &candidate.path, cancel)?
    } else {
        None
    };
    if recommendations::checks_activity(current.kind)
        && let Some(reason) = activity_reason(
            &mut activity,
            current.activity_root.as_deref().unwrap_or(project),
            current.kind,
            cancel,
            ACTIVITY_MAX_AGE,
        )
    {
        return Err(reason);
    }
    let policy = if recommendations::developer_measurement(current.kind) {
        MeasurementPolicy::Developer
    } else {
        MeasurementPolicy::Strict
    };
    let measured = safety::measure_try_observing_with_policy(
        &candidate.path,
        root.identity.device,
        cancel,
        policy,
        observe,
    )?;
    if let Some(reason) = &measured.unsafe_reason {
        return Err(reason.clone());
    }
    if let Some(reason) = suggestion_reason(&current, &measured, clock_ns()) {
        return Err(format!(
            "This item no longer meets the recommendation policy: {reason}."
        ));
    }
    if !candidate.suggestion_eligible {
        return Err("This diagnostic item was not offered as a cleanup suggestion; scan again to review current recommendations".into());
    }
    if measured.fingerprint != candidate.fingerprint
        || measured.logical_bytes != candidate.logical_bytes
        || measured.allocated_bytes != candidate.allocated_bytes
        || measured.files != candidate.file_count
    {
        return Err("The item's contents changed since review; scan it again".into());
    }
    // Ownership files and running processes are outside the artifact digest.
    // Recheck them after a potentially long walk before the caller commits its
    // manifest or stages the item; the streamed observations alone are not proof.
    safety::validate_root(root)?;
    let latest_meta = safety::metadata(&candidate.path)?;
    if latest_meta.identity != candidate.identity
        || latest_meta.identity.device != root.identity.device
        || latest_meta.is_dataless()
    {
        return Err("The item changed during verification; scan it again".into());
    }
    let project = candidate.path.parent().unwrap();
    safety::validate_ancestors(project)?;
    let latest = evidence(root, &candidate.path, &latest_meta, cancel)?
        .ok_or("Project ownership disappeared during verification")?;
    if latest.kind != current.kind
        || latest.fingerprint != current.fingerprint
        || latest.blocked != current.blocked
        || latest.activity_root != current.activity_root
    {
        return Err("Project configuration changed during verification; review again".into());
    }
    // Processes started during the potentially long measurement must be seen:
    // the final gate always captures fresh and never reuses an aged snapshot.
    if recommendations::checks_activity(current.kind)
        && let Some(reason) = ActivitySnapshot::capture(cancel)?.blocked_for(
            current.kind,
            latest.activity_root.as_deref().unwrap_or(project),
            cancel,
        )
    {
        return Err(reason);
    }
    if let Some(git) = git_evidence {
        // An unchanged outer repository does not prove that a new, nearer
        // repository has not started tracking this project's contents.
        for ancestor in candidate
            .path
            .parent()
            .unwrap()
            .ancestors()
            .take_while(|ancestor| *ancestor != git.work_tree)
        {
            safety::cancelled(cancel)?;
            if path_exists(&ancestor.join(".git"))? {
                return Err(
                    "Repository ownership changed during verification; review again".into(),
                );
            }
        }
        git.unchanged(root, cancel)?;
    } else if recommendations::checks_git(current.kind)
        && git_untracked(
            root,
            candidate.path.parent().unwrap(),
            &candidate.path,
            cancel,
        )?
        .is_some()
    {
        return Err("Repository ownership appeared during verification; review again".into());
    }
    safety::cancelled(cancel)
}

const MAX_GIT_POINTER_BYTES: u64 = 4096;
const MAX_GIT_INDEX_BYTES: u64 = 4 * 1024 * 1024;
const GIT_OUTPUT_WAIT: Duration = Duration::from_millis(15);

#[derive(Debug)]
struct GitEvidenceEntry {
    path: PathBuf,
    metadata: Option<EntryMeta>,
    digest: Option<blake3::Hash>,
}

/// Git metadata is read only as evidence. It never becomes part of an artifact
/// or authorizes traversal beyond the user's existing filesystem grant.
#[derive(Debug)]
struct GitEvidence {
    work_tree: PathBuf,
    directory: PathBuf,
    entries: Vec<GitEvidenceEntry>,
}

fn git_metadata(root: &Root, path: &Path, cancel: &AtomicBool) -> Result<Option<EntryMeta>> {
    safety::cancelled(cancel)?;
    safety::absolute_components(path)?;
    let relative = path
        .strip_prefix(&root.path)
        .map_err(|_| "Git metadata is outside this folder's authorization")?;
    if relative
        .components()
        .any(|part| part.as_os_str() != ".git" && safety::excluded_name(part.as_os_str(), true))
    {
        return Err("Git metadata lies in a protected or cloud-managed location".into());
    }
    let parent = path.parent().ok_or("Git metadata has no parent")?;
    safety::validate_ancestors(parent)?;
    // Reject redirection, another account's metadata and nested volumes before
    // starting Git. The fixed number of evidence paths keeps this work bounded.
    for ancestor in parent
        .ancestors()
        .take_while(|ancestor| ancestor.starts_with(&root.path))
    {
        safety::cancelled(cancel)?;
        let meta = safety::metadata(ancestor)?;
        if !meta.is_dir()
            || meta.is_dataless()
            || meta.uid != unsafe { libc::geteuid() }
            || meta.identity.device != root.identity.device
        {
            return Err(
                "Git metadata requires owned physical folders on the authorized volume".into(),
            );
        }
    }
    let directory = safety::open_directory(parent)?;
    let name = CString::new(
        path.file_name()
            .ok_or("Git metadata has no name")?
            .as_bytes(),
    )
    .map_err(|_| "Git metadata contains an invalid path")?;
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe {
        libc::fstatat(
            directory.as_raw_fd(),
            name.as_ptr(),
            &mut stat,
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return if std::io::Error::last_os_error().raw_os_error() == Some(libc::ENOENT) {
            Ok(None)
        } else {
            Err("Git metadata could not be inspected".into())
        };
    }
    let meta = safety::metadata(path)?;
    if meta.is_symlink()
        || meta.is_dataless()
        || meta.uid != unsafe { libc::geteuid() }
        || meta.identity.device != root.identity.device
        || (!meta.is_dir() && !meta.is_file())
        || (meta.is_file() && meta.links != 1)
    {
        return Err(
            "Git metadata requires owned, independent local files and physical folders".into(),
        );
    }
    Ok(Some(meta))
}

fn git_pointer_path(root: &Root, base: &Path, bytes: &[u8]) -> Result<PathBuf> {
    let bytes = bytes.strip_suffix(b"\n").unwrap_or(bytes);
    let bytes = bytes.strip_suffix(b"\r").unwrap_or(bytes);
    if bytes.is_empty() || bytes.contains(&0) || bytes.contains(&b'\n') || bytes.contains(&b'\r') {
        return Err("Git metadata contains an invalid path pointer".into());
    }
    let source = Path::new(OsStr::from_bytes(bytes));
    let mut resolved = if source.is_absolute() {
        PathBuf::from("/")
    } else {
        base.to_path_buf()
    };
    let mut named_component = false;
    for component in source.components() {
        match component {
            Component::RootDir | Component::CurDir => {}
            Component::Normal(name) => {
                named_component = true;
                resolved.push(name);
            }
            Component::ParentDir => {
                // Leading ../ components use an already-validated physical
                // base. Collapsing child/.. could conceal a symbolic link and
                // disagree with Git's own interpretation of the pointer.
                if named_component {
                    return Err("Git metadata contains an ambiguous parent path".into());
                }
                if !resolved.pop() {
                    return Err("Git metadata contains an invalid parent path".into());
                }
            }
            Component::Prefix(_) => return Err("Git metadata contains an unsupported path".into()),
        }
    }
    if !resolved.starts_with(&root.path) {
        return Err("Git metadata is outside this folder's authorization".into());
    }
    Ok(resolved)
}

/// An ordinary index contains all tracked names locally. Split/sparse indexes
/// can consult additional files or object stores, so this first worktree support
/// deliberately excludes them. Git still validates the index checksum itself.
fn validate_git_index(bytes: &[u8]) -> Result<()> {
    let malformed = || "The Git index format could not be safely verified".to_owned();
    if bytes.len() < 32 || bytes.len() as u64 > MAX_GIT_INDEX_BYTES || &bytes[..4] != b"DIRC" {
        return Err(malformed());
    }
    let word = |offset: usize| -> Result<u32> {
        let slice = bytes.get(offset..offset + 4).ok_or_else(malformed)?;
        Ok(u32::from_be_bytes(slice.try_into().unwrap()))
    };
    let version = word(4)?;
    if !matches!(version, 2 | 3) {
        return Err("Compressed or unfamiliar Git indexes need manual inspection".into());
    }
    let count = word(8)? as usize;
    if count > bytes.len() / 64 {
        return Err(malformed());
    }
    let end = bytes.len() - 20; // SHA-1; alternate object formats are excluded below.
    let mut offset = 12usize;
    for _ in 0..count {
        let header = bytes
            .get(offset..offset + 62)
            .filter(|_| offset + 62 <= end)
            .ok_or_else(malformed)?;
        let flags = u16::from_be_bytes(header[60..62].try_into().unwrap());
        if word(offset + 24)? & 0o170000 == 0o040000 {
            return Err("Sparse Git indexes need manual inspection".into());
        }
        let extended = flags & 0x4000 != 0;
        if extended && version == 2 {
            return Err(malformed());
        }
        let name_start = offset + 62 + if extended { 2 } else { 0 };
        let length = (flags & 0x0fff) as usize;
        let name_end = if length < 0x0fff {
            name_start.checked_add(length).ok_or_else(malformed)?
        } else {
            let remaining = bytes.get(name_start..end).ok_or_else(malformed)?;
            name_start
                + remaining
                    .iter()
                    .position(|byte| *byte == 0)
                    .ok_or_else(malformed)?
        };
        let name = bytes
            .get(name_start..name_end)
            .filter(|_| name_end < end)
            .ok_or_else(malformed)?;
        if name.is_empty()
            || bytes[name_end] != 0
            || name.contains(&0)
            || name
                .split(|byte| *byte == b'/')
                .any(|part| matches!(part, b"" | b"." | b".." | b".git"))
        {
            return Err(malformed());
        }
        let consumed = name_end + 1 - offset;
        let next = offset + consumed.div_ceil(8) * 8;
        if next > end || bytes[name_end..next].iter().any(|byte| *byte != 0) {
            return Err(malformed());
        }
        offset = next;
    }
    while offset < end {
        let header = bytes
            .get(offset..offset + 8)
            .filter(|_| offset + 8 <= end)
            .ok_or_else(malformed)?;
        if !header[0].is_ascii_uppercase() {
            return Err(
                "Split, sparse or unfamiliar Git index extensions need manual inspection".into(),
            );
        }
        offset = offset
            .checked_add(8 + word(offset + 4)? as usize)
            .filter(|next| *next <= end)
            .ok_or_else(malformed)?;
    }
    Ok(())
}

/// Includes can read configuration outside the validated evidence set. Reject
/// them before Git starts, as well as sparse/alternate-hash layouts that need a
/// wider evidence model. This parses section/key names only; Git parses values.
fn validate_git_config(bytes: &[u8]) -> Result<()> {
    // Git accepts a UTF-8 BOM before the first section. Match that behavior
    // before checking includes so it cannot conceal the first section name.
    let bytes = bytes.strip_prefix(b"\xef\xbb\xbf").unwrap_or(bytes);
    let text =
        std::str::from_utf8(bytes).map_err(|_| "Git configuration is not supported UTF-8")?;
    let mut section = String::new();
    for physical in text.lines() {
        let line = physical.trim_start();
        if line.is_empty() || line.starts_with(['#', ';']) {
            continue;
        }
        if physical
            .bytes()
            .rev()
            .take_while(|byte| *byte == b'\\')
            .count()
            % 2
            == 1
        {
            return Err("Continued Git configuration values need manual inspection".into());
        }
        if let Some(header) = line.strip_prefix('[') {
            let header = header.trim_start();
            let end = header
                .find(|character: char| {
                    !character.is_ascii_alphanumeric() && character != '-' && character != '.'
                })
                .unwrap_or(header.len());
            if end == 0 || !header.contains(']') {
                return Err("Git configuration sections could not be verified".into());
            }
            section = header[..end]
                .split('.')
                .next()
                .unwrap()
                .to_ascii_lowercase();
            if matches!(section.as_str(), "include" | "includeif") {
                return Err(
                    "Git configuration includes require manual inspection of ownership".into(),
                );
            }
        } else {
            let key_end = line
                .find(|character: char| !character.is_ascii_alphanumeric() && character != '-')
                .unwrap_or(line.len());
            let key = &line[..key_end];
            if (section == "core"
                && (key.eq_ignore_ascii_case("sparsecheckout")
                    || key.eq_ignore_ascii_case("sparsecheckoutcone")))
                || (section == "extensions"
                    && (key.eq_ignore_ascii_case("objectformat")
                        || key.eq_ignore_ascii_case("sparseindex")))
            {
                return Err(
                    "Sparse or alternate-format Git repositories need manual inspection".into(),
                );
            }
        }
    }
    Ok(())
}

impl GitEvidence {
    fn directory(&mut self, root: &Root, path: &Path, cancel: &AtomicBool) -> Result<()> {
        let meta = git_metadata(root, path, cancel)?.ok_or("Git metadata folder is missing")?;
        if !meta.is_dir() {
            return Err("Git metadata does not identify a physical repository folder".into());
        }
        self.entries.push(GitEvidenceEntry {
            path: path.to_path_buf(),
            metadata: Some(meta),
            digest: None,
        });
        Ok(())
    }

    fn file(
        &mut self,
        root: &Root,
        path: &Path,
        required: bool,
        limit: u64,
        cancel: &AtomicBool,
    ) -> Result<Option<Vec<u8>>> {
        let metadata = git_metadata(root, path, cancel)?;
        let bytes = if let Some(meta) = &metadata {
            if !meta.is_file() || meta.identity.size > limit {
                return Err("Git evidence is not a supported bounded regular file".into());
            }
            let source = safety::read_regular(path, cancel)?;
            if source.identity != meta.identity || safety::metadata(path)? != *meta {
                return Err("Git evidence changed while being captured".into());
            }
            Some(source.bytes)
        } else if required {
            return Err("Required Git evidence is missing".into());
        } else {
            None
        };
        self.entries.push(GitEvidenceEntry {
            path: path.to_path_buf(),
            metadata,
            digest: bytes.as_deref().map(blake3::hash),
        });
        Ok(bytes)
    }

    fn capture(root: &Root, work_tree: &Path, cancel: &AtomicBool) -> Result<Self> {
        let marker = work_tree.join(".git");
        let meta =
            git_metadata(root, &marker, cancel)?.ok_or("Git repository marker disappeared")?;
        let mut evidence = Self {
            work_tree: work_tree.to_path_buf(),
            directory: marker.clone(),
            entries: Vec::with_capacity(12),
        };
        let linked = meta.is_file();
        let common = if linked {
            let bytes = evidence
                .file(root, &marker, true, MAX_GIT_POINTER_BYTES, cancel)?
                .unwrap();
            let pointer = bytes
                .strip_prefix(b"gitdir: ")
                .ok_or("The Git worktree marker is not a supported gitdir pointer")?;
            let directory = git_pointer_path(root, work_tree, pointer)?;
            let worktrees = directory
                .parent()
                .ok_or("Git worktree metadata has no parent")?;
            let common = worktrees
                .parent()
                .ok_or("Git worktree has no common repository")?;
            if worktrees.file_name() != Some(OsStr::new("worktrees"))
                || common.file_name() != Some(OsStr::new(".git"))
            {
                return Err("Only standard linked Git worktree ownership is supported".into());
            }
            evidence.directory(root, common, cancel)?;
            evidence.directory(root, worktrees, cancel)?;
            evidence.directory(root, &directory, cancel)?;
            let bytes = evidence
                .file(
                    root,
                    &directory.join("commondir"),
                    true,
                    MAX_GIT_POINTER_BYTES,
                    cancel,
                )?
                .unwrap();
            if git_pointer_path(root, &directory, &bytes)? != common {
                return Err("Git worktree common-directory ownership is inconsistent".into());
            }
            let bytes = evidence
                .file(
                    root,
                    &directory.join("gitdir"),
                    true,
                    MAX_GIT_POINTER_BYTES,
                    cancel,
                )?
                .unwrap();
            if !Path::new(OsStr::from_bytes(&bytes)).is_absolute()
                || git_pointer_path(root, &directory, &bytes)? != marker
            {
                return Err("Git worktree backpointer does not match this project".into());
            }
            let common = common.to_path_buf();
            evidence.directory = directory;
            common
        } else {
            evidence.directory(root, &marker, cancel)?;
            // A directory with an extra commondir is a separate unsupported
            // layout; do not let Git silently redirect it after validation.
            if evidence
                .file(
                    root,
                    &marker.join("commondir"),
                    false,
                    MAX_GIT_POINTER_BYTES,
                    cancel,
                )?
                .is_some()
            {
                return Err(
                    "Nonstandard Git common-directory ownership needs manual inspection".into(),
                );
            }
            marker
        };
        let directory = evidence.directory.clone();
        evidence.file(
            root,
            &directory.join("HEAD"),
            true,
            MAX_GIT_POINTER_BYTES,
            cancel,
        )?;
        if let Some(index) = evidence.file(
            root,
            &directory.join("index"),
            linked,
            MAX_GIT_INDEX_BYTES,
            cancel,
        )? {
            validate_git_index(&index)?;
        }
        for path in [common.join("config"), directory.join("config.worktree")] {
            if let Some(config) = evidence.file(root, &path, false, MAX_GIT_INDEX_BYTES, cancel)? {
                validate_git_config(&config)?;
            }
        }
        evidence.directory(root, &common.join("objects"), cancel)?;
        evidence.directory(root, &common.join("refs"), cancel)?;
        evidence.unchanged(root, cancel)?;
        Ok(evidence)
    }

    fn unchanged(&self, root: &Root, cancel: &AtomicBool) -> Result<()> {
        safety::validate_root(root)?;
        for saved in &self.entries {
            let current = git_metadata(root, &saved.path, cancel)?;
            let same = match (&saved.metadata, current) {
                (None, None) => true,
                (Some(before), Some(after)) if before.is_dir() => {
                    before.identity.device == after.identity.device
                        && before.identity.inode == after.identity.inode
                        && before.identity.mode == after.identity.mode
                }
                (Some(before), Some(after)) => *before == after,
                _ => false,
            };
            if !same {
                return Err(
                    "Git ownership or index changed during the safety check; review again".into(),
                );
            }
            if let Some(digest) = saved.digest {
                let source = safety::read_regular(&saved.path, cancel)?;
                if blake3::hash(&source.bytes) != digest
                    || saved.metadata.as_ref().map(|meta| &meta.identity) != Some(&source.identity)
                    || saved.metadata.as_ref() != Some(&safety::metadata(&saved.path)?)
                {
                    return Err("Git evidence changed during the safety check; review again".into());
                }
            }
        }
        safety::cancelled(cancel)
    }
}

/// Poll is only a scheduling hint; the existing read and child-status checks
/// remain authoritative. A failed, interrupted or unexpected poll falls back
/// to the unspent portion of the old sleep, without introducing a new error.
fn git_output_wait_duration(
    stdout_pending: bool,
    poll: impl FnOnce() -> (libc::c_int, libc::c_short, Duration),
) -> Duration {
    if !stdout_pending {
        // EOF can precede child exit. Polling that hung-up descriptor again
        // would return immediately while try_wait still reports a live child.
        return GIT_OUTPUT_WAIT;
    }
    let (count, events, elapsed) = poll();
    let readable = libc::POLLIN | libc::POLLHUP;
    if (count == 0 && events == 0)
        || (count == 1 && events & readable != 0 && events & !readable == 0)
    {
        Duration::ZERO
    } else {
        // Includes POLLERR/POLLNVAL, unknown readiness and every errno,
        // including EINTR. Repeated poll failures must not create a spin loop.
        GIT_OUTPUT_WAIT.saturating_sub(elapsed)
    }
}

fn poll_git_output(fd: RawFd) -> (libc::c_int, libc::c_short, Duration) {
    let mut descriptor = libc::pollfd {
        fd,
        events: libc::POLLIN,
        revents: 0,
    };
    let started = Instant::now();
    // Cancellation is an atomic flag, not a descriptor event. Never wait for
    // the whole child deadline here; retain the old cooperative wait quantum.
    let count = unsafe { libc::poll(&mut descriptor, 1, GIT_OUTPUT_WAIT.as_millis() as i32) };
    (count, descriptor.revents, started.elapsed())
}

fn wait_for_git_output(fd: RawFd, stdout_pending: bool) {
    let remaining = git_output_wait_duration(stdout_pending, || poll_git_output(fd));
    if !remaining.is_zero() {
        std::thread::sleep(remaining);
    }
}

/// No repository means no Git-tracked descendants. A real repository requires a
/// successful, empty, literal-pathspec query; every uncertainty fails closed.
fn git_untracked(
    root: &Root,
    project: &Path,
    artifact: &Path,
    cancel: &AtomicBool,
) -> Result<Option<GitEvidence>> {
    let mut repository = None;
    for ancestor in project.ancestors() {
        safety::cancelled(cancel)?;
        let git = ancestor.join(".git");
        if !path_exists(&git)? {
            continue;
        }
        if !ancestor.starts_with(&root.path) {
            return Err("Repository ownership lies outside this folder's authorization".into());
        }
        repository = Some(GitEvidence::capture(root, ancestor, cancel)?);
        break;
    }
    let Some(repository) = repository else {
        return Ok(None);
    };
    let relative = artifact
        .strip_prefix(&repository.work_tree)
        .map_err(|_| "Artifact is outside its repository")?;
    // Index spelling can survive a case-only filesystem rename. Always match
    // it conservatively, while keeping wildcard characters in paths literal.
    let mut pathspec = OsString::from(":(literal,icase)");
    pathspec.push(relative.as_os_str());
    let mut child = Command::new("/usr/bin/git")
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_TERMINAL_PROMPT", "0")
        .arg("-c")
        .arg("core.fsmonitor=false")
        .arg("-C")
        .arg(&repository.work_tree)
        .arg("--git-dir")
        .arg(&repository.directory)
        .arg("--work-tree")
        .arg(&repository.work_tree)
        .args(["ls-files", "--cached", "-z", "--"])
        .arg(pathspec)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| format!("Git tracking could not be checked: {error}"))?;
    let mut output = child.stdout.take().ok_or("Git output was unavailable")?;
    let fd = output.as_raw_fd();
    if unsafe { libc::fcntl(fd, libc::F_SETFL, libc::O_NONBLOCK) } != 0 {
        let _ = child.kill();
        let _ = child.wait();
        return Err("Git tracking output could not be bounded".into());
    }
    let deadline = Instant::now() + Duration::from_secs(2);
    let mut buffer = [0u8; 256];
    let result = loop {
        if let Err(reason) = safety::cancelled(cancel) {
            break Err(reason);
        }
        let stdout_pending = match output.read(&mut buffer) {
            Ok(count) if count > 0 => {
                break Err("Git tracks content inside this artifact; cleanup is excluded".into());
            }
            Ok(_) => false,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => true,
            Err(_) => break Err("Git tracking output could not be verified".into()),
        };
        match child.try_wait() {
            Ok(Some(status)) => {
                if !status.success() {
                    break Err("Git tracking check failed; the artifact is excluded".into());
                }
                match output.read(&mut buffer) {
                    Ok(0) => break Ok(()),
                    Ok(_) => {
                        break Err(
                            "Git tracks content inside this artifact; cleanup is excluded".into(),
                        );
                    }
                    Err(_) => break Err("Git tracking output was incomplete".into()),
                }
            }
            Err(_) => break Err("Git tracking process could not be inspected".into()),
            Ok(None) => {}
        }
        if Instant::now() >= deadline {
            break Err("Git tracking timed out; the artifact is excluded".into());
        }
        // Only pending stdout uses readiness. EOF while the child is alive
        // keeps the old sleep; the deadline and all decisions remain above.
        wait_for_git_output(fd, stdout_pending);
    };
    let _ = child.kill();
    let _ = child.wait();
    result?;
    repository.unchanged(root, cancel)?;
    Ok(Some(repository))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::os::unix::fs::symlink;

    fn fixture() -> (tempfile::TempDir, Root, PathBuf) {
        let temp = tempfile::tempdir().unwrap();
        let base = std::fs::canonicalize(temp.path()).unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        let project = base.join("project");
        std::fs::create_dir(&project).unwrap();
        std::fs::write(
            project.join("package.json"),
            br#"{"name":"fixture","dependencies":{"x":"1"}}"#,
        )
        .unwrap();
        std::fs::write(
            project.join("package-lock.json"),
            br#"{"lockfileVersion":3,"packages":{}}"#,
        )
        .unwrap();
        std::fs::create_dir(project.join("node_modules")).unwrap();
        std::fs::write(project.join("node_modules/payload"), [7u8; 4096]).unwrap();
        (temp, root, project)
    }

    fn cargo_refresh_fixture() -> (tempfile::TempDir, Root, PathBuf) {
        let (temp, root, project) = fixture();
        std::fs::write(
            project.join("Cargo.toml"),
            "[package]\nname = 'disposable'\nversion = '0.1.0'\n",
        )
        .unwrap();
        std::fs::write(project.join("Cargo.lock"), "version = 4\n").unwrap();
        std::fs::create_dir(project.join("target")).unwrap();
        std::fs::write(
            project.join("target/CACHEDIR.TAG"),
            "Signature: 8a477f597d28d172789f06886806bc55\n",
        )
        .unwrap();
        std::fs::write(project.join("target/payload"), [3u8; 4096]).unwrap();
        std::fs::create_dir_all(project.join("unrelated/deep/source")).unwrap();
        std::fs::write(
            project.join("unrelated/deep/source/keep"),
            b"preserved source",
        )
        .unwrap();
        age_tree(&project, 8);
        (temp, root, project)
    }

    #[test]
    fn lockfile_refresh_finds_unindexed_target_without_enumerating_unrelated_subtrees() {
        for mode in [ScanMode::Suggestions, ScanMode::MetadataCoverage] {
            let (_temp, root, project) = cargo_refresh_fixture();
            let target = project.join("target");
            let (full, full_rows) = candidates_in_mode(&root, mode);
            assert!(full.complete);
            let expected = full_rows.iter().find(|row| row.path == target).unwrap();
            let reads = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
            let observed = std::rc::Rc::clone(&reads);
            let mut rows = Vec::new();
            let stats = safety::tests::with_directory_read_observer(
                move |path| observed.borrow_mut().push(path.to_path_buf()),
                || {
                    scan_cargo_lock_with_checkpoint_mode(
                        &root,
                        &project.join("Cargo.lock"),
                        &[],
                        &AtomicBool::new(false),
                        mode,
                        || {},
                        |batch| rows.extend(batch.candidates),
                    )
                    .unwrap()
                },
            );
            assert!(stats.complete);
            assert_eq!(stats.entries, 4);
            assert_eq!(stats.files, 3);
            assert_eq!(stats.directories, 1);
            assert_eq!(rows, vec![expected.clone()]);
            assert!(
                reads
                    .borrow()
                    .iter()
                    .all(|path| path == &project || path.starts_with(&target))
            );
        }
    }

    #[test]
    fn lockfile_refresh_reconciles_origin_directories_and_deduplicates_linked_leaves() {
        let (_temp, root, project) = cargo_refresh_fixture();
        let origin = project.join("Cargo.lock");
        std::fs::remove_file(&origin).unwrap();
        std::fs::create_dir(&origin).unwrap();
        std::fs::write(
            origin.join("keep-source"),
            b"preserve this type replacement",
        )
        .unwrap();
        let stats = scan_cargo_lock_with_checkpoint_mode(
            &root,
            &origin,
            &[],
            &AtomicBool::new(false),
            ScanMode::Suggestions,
            || {},
            |_| {},
        )
        .unwrap();
        assert!(stats.complete);
        assert_eq!(
            stats.entries, 3,
            "Origin subtree is covered; invalid Cargo evidence excludes target contents"
        );
        assert_eq!(
            std::fs::read(origin.join("keep-source")).unwrap(),
            b"preserve this type replacement"
        );

        for mode in [ScanMode::Suggestions, ScanMode::MetadataCoverage] {
            let temp = tempfile::tempdir().unwrap();
            let path = temp.path().canonicalize().unwrap();
            let origin = path.join("Cargo.lock");
            std::fs::write(&origin, [1u8; 4096]).unwrap();
            std::fs::hard_link(&origin, path.join("target")).unwrap();
            let root = safety::authorize(&path, "downloads").unwrap();
            let meta = safety::metadata(&origin).unwrap();
            let stats = scan_cargo_lock_with_checkpoint_mode(
                &root,
                &origin,
                &[],
                &AtomicBool::new(false),
                mode,
                || {},
                |_| {},
            )
            .unwrap();
            assert!(stats.complete);
            assert_eq!((stats.entries, stats.files), (2, 2));
            assert_eq!(stats.logical_bytes, meta.identity.size);
            assert_eq!(stats.allocated_bytes, meta.allocated);
        }
    }

    #[test]
    fn lockfile_refresh_does_not_publish_target_after_case_rename() {
        let (_temp, root, project) = cargo_refresh_fixture();
        let target = project.join("target");
        let renamed = project.join("Target");
        let mut moved = false;
        let mut published = Vec::new();
        let result = scan_cargo_lock_with_checkpoint_mode(
            &root,
            &project.join("Cargo.lock"),
            &[],
            &AtomicBool::new(false),
            ScanMode::Suggestions,
            || {},
            |batch| {
                // The target's final row is buffered before this progress callback.
                if batch.stats.entries > 1 && !moved {
                    assert!(batch.candidates.is_empty());
                    assert_eq!(batch.stats.candidates, 0);
                    assert!(!batch.stats.complete);
                    std::fs::rename(&target, &renamed).unwrap();
                    moved = true;
                }
                published.extend(batch.candidates);
            },
        );
        assert!(moved && result.is_err());
        assert!(published.is_empty());
        assert_eq!(std::fs::read(renamed.join("payload")).unwrap(), [3u8; 4096]);

        // A fresh replay proves exact-name absence without traversing an alias.
        let stats = scan_cargo_lock_with_checkpoint_mode(
            &root,
            &project.join("Cargo.lock"),
            &[],
            &AtomicBool::new(false),
            ScanMode::Suggestions,
            || {},
            |batch| assert!(batch.candidates.is_empty()),
        )
        .unwrap();
        assert!(stats.complete);
        assert_eq!(stats.entries, 1);
    }

    #[test]
    fn selected_scope_rejects_replacement_or_disappearance_before_start() {
        for replace in [false, true] {
            let (_temp, root, project) = cargo_refresh_fixture();
            let target = project.join("target");
            let expected = safety::metadata(&target).unwrap();
            std::fs::rename(&target, project.join("preserved-target")).unwrap();
            if replace {
                std::fs::create_dir(&target).unwrap();
            }
            let result = ScanSession::new(ScanMode::Suggestions).scan(
                &root,
                ScanScope {
                    path: Some(&target),
                    expected: Some(&expected),
                    recent_files: None,
                    starts: None,
                },
                &[],
                &AtomicBool::new(false),
                || {},
                |batch| assert!(batch.candidates.is_empty()),
            );
            assert!(result.is_err());
        }
    }

    fn candidates(root: &Root) -> (ScanStats, Vec<Candidate>) {
        candidates_in_mode(root, ScanMode::Suggestions)
    }

    #[test]
    fn missing_incremental_scope_finishes_before_traversal_or_publication() {
        let (_temp, root, project) = fixture();
        let stats = scan_with_checkpoint_mode(
            &root,
            Some(&root.path.join("vanished/child")),
            &[],
            &AtomicBool::new(false),
            ScanMode::Suggestions,
            || panic!("A missing scope must not start traversal"),
            |_| panic!("A missing scope must not publish a batch"),
        )
        .unwrap();
        assert!(stats.complete && !stats.cancelled);
        assert_eq!((stats.entries, stats.errors, stats.candidates), (0, 0, 0));
        assert_eq!(
            std::fs::read(project.join("node_modules/payload")).unwrap(),
            [7u8; 4096]
        );
    }

    #[test]
    fn disappearance_after_initial_metadata_stays_partial() {
        let (_temp, root, project) = fixture();
        let moved = root.path.join("preserved-project");
        let moved_once = std::cell::Cell::new(false);
        let stats = scan_with_checkpoint_mode(
            &root,
            Some(&project),
            &[],
            &AtomicBool::new(false),
            ScanMode::Suggestions,
            || {
                if !moved_once.replace(true) {
                    std::fs::rename(&project, &moved).unwrap();
                }
            },
            |batch| assert!(batch.candidates.is_empty()),
        )
        .unwrap();
        assert!(!stats.complete && stats.errors > 0);
        assert_eq!(stats.entries, 1);
        assert_eq!(
            std::fs::read(moved.join("node_modules/payload")).unwrap(),
            [7u8; 4096]
        );
    }

    #[test]
    fn missing_descendant_still_refreshes_its_existing_artifact_boundary() {
        let (_temp, root, project) = fixture();
        let stats = scan_with_checkpoint_mode(
            &root,
            Some(&project.join("node_modules/vanished")),
            &[],
            &AtomicBool::new(false),
            ScanMode::MetadataCoverage,
            || {},
            |_| {},
        )
        .unwrap();
        assert!(stats.complete && stats.errors == 0);
        assert!(stats.entries >= 2, "The existing artifact must be measured");
    }

    fn candidates_in_mode(root: &Root, mode: ScanMode) -> (ScanStats, Vec<Candidate>) {
        let mut rows = std::collections::BTreeMap::new();
        let stats = scan_with_checkpoint_mode(
            root,
            None,
            &[],
            &AtomicBool::new(false),
            mode,
            || {},
            |batch| {
                assert!(batch.candidates.len() <= MAX_BATCH);
                for row in batch.candidates {
                    rows.insert(row.id.clone(), row);
                }
            },
        )
        .unwrap();
        (stats, rows.into_values().collect())
    }
    fn age_tree(path: &Path, days: u64) {
        if path.is_dir() {
            for entry in std::fs::read_dir(path).unwrap() {
                age_tree(&entry.unwrap().path(), days);
            }
        }
        let modified = SystemTime::now() - Duration::from_secs(days * 86_400);
        std::fs::File::open(path)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(modified))
            .unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn eligible_revalidation_fixture() -> (tempfile::TempDir, Root, PathBuf, Candidate) {
        let (temp, root, project) = fixture();
        let path = CString::new(root.path.as_os_str().as_bytes()).unwrap();
        let mut capacity: libc::statfs = unsafe { std::mem::zeroed() };
        assert_eq!(unsafe { libc::statfs(path.as_ptr(), &mut capacity) }, 0);
        assert!(
            capacity.f_bavail.saturating_mul(capacity.f_bsize as u64)
                >= 3 * 1024 * 1024 * 1024 + LARGE_FILE_BYTES,
            "The disposable allocated-file test requires a 3 GiB reserve"
        );
        {
            let mut payload = std::fs::File::create(project.join("node_modules/payload")).unwrap();
            let block = vec![0x63; 1024 * 1024];
            let mut remaining = LARGE_FILE_BYTES;
            while remaining > 0 {
                let size = remaining.min(block.len() as u64) as usize;
                payload.write_all(&block[..size]).unwrap();
                remaining -= size as u64;
            }
            payload.sync_all().unwrap();
        }
        age_tree(&project, 9);
        let (_, rows) = candidates(&root);
        let candidate = rows
            .into_iter()
            .find(|candidate| candidate.suggestion_eligible)
            .expect("The allocated, aged fixture must be eligible before changing its context");
        (temp, root, project, candidate)
    }

    fn policy_evidence(kind: &'static str, days: i64) -> Evidence {
        Evidence {
            kind,
            title: "fixture".into(),
            explanation: "fixture",
            consequence: "fixture",
            fingerprint: "fixture".into(),
            blocked: None,
            latest_modified_ns: 0,
            quiet_days: days,
            activity_root: None,
        }
    }
    #[test]
    fn fresh_artifact_boundary_is_pruned_without_a_diagnostic() {
        let (_temp, root, _) = fixture();
        let (stats, rows) = candidates(&root);
        assert!(rows.is_empty());
        assert!(stats.first_finding_ms.is_none());
        assert_eq!(stats.candidates, 0);
        assert_eq!(stats.files, 2);
        assert_eq!(stats.excluded_artifacts, 1);
        assert!(stats.skipped >= 1);
        assert!(stats.complete, "{}", stats.message);

        let (covered, rows) = candidates_in_mode(&root, ScanMode::MetadataCoverage);
        assert!(covered.complete, "{}", covered.message);
        assert_eq!(covered.entries, 6);
        assert_eq!(covered.files, 3);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].kind, "node");
        assert_eq!(rows[0].logical_bytes, 4096);
        assert!(!rows[0].suggestion_eligible && !rows[0].eligible_permanent);
    }

    #[test]
    fn fresh_artifacts_skip_missing_or_unreadable_ownership() {
        use std::os::unix::fs::PermissionsExt;
        for (artifact_name, manifest_name, contents) in [
            (
                "node_modules",
                "package.json",
                br#"{"name":"fixture"}"#.as_slice(),
            ),
            (
                "target",
                "Cargo.toml",
                b"[package]\nname = 'fixture'\nversion = '0.1.0'\n".as_slice(),
            ),
        ] {
            for unreadable in [false, true] {
                let temp = tempfile::tempdir().unwrap();
                let base = std::fs::canonicalize(temp.path()).unwrap();
                let project = base.join("project");
                let artifact = project.join(artifact_name);
                std::fs::create_dir_all(&artifact).unwrap();
                std::fs::write(artifact.join("preserve"), b"disposable payload").unwrap();
                let manifest = project.join(manifest_name);
                if unreadable {
                    std::fs::write(&manifest, contents).unwrap();
                    std::fs::set_permissions(&manifest, std::fs::Permissions::from_mode(0o000))
                        .unwrap();
                }
                let root = safety::authorize(&base, "projects").unwrap();
                let excluded = artifact.clone();
                let (stats, rows) = safety::tests::with_directory_read_observer(
                    move |path| assert!(!path.starts_with(&excluded)),
                    || candidates(&root),
                );
                if unreadable {
                    std::fs::set_permissions(&manifest, std::fs::Permissions::from_mode(0o600))
                        .unwrap();
                    assert_eq!(std::fs::read(&manifest).unwrap(), contents);
                } else {
                    assert!(!manifest.exists());
                }
                assert!(
                    rows.is_empty(),
                    "Ownership was not inspected or established"
                );
                assert_eq!(stats.excluded_artifacts, 1);
                assert_eq!(stats.skipped, 1);
                assert_eq!(stats.errors, 0);
                assert!(stats.complete, "{}", stats.message);
                assert_eq!(
                    std::fs::read(artifact.join("preserve")).unwrap(),
                    b"disposable payload"
                );
            }
        }
    }

    #[test]
    fn a_fresh_artifact_named_authorized_root_still_discovers_nested_projects() {
        for name in ["node_modules", "target"] {
            let (_temp, original_root, project) = fixture();
            let authorized = original_root.path.join(name);
            std::fs::create_dir(&authorized).unwrap();
            let nested_project = authorized.join("project");
            std::fs::rename(project, &nested_project).unwrap();
            age_tree(&nested_project, 8);
            let root = safety::authorize(&authorized, "projects").unwrap();
            assert!(!quiet_for(
                root.identity.modified_ns,
                clock_ns(),
                DEVELOPER_QUIET_DAYS,
            ));
            let (stats, rows) = candidates(&root);
            assert!(stats.complete, "{}", stats.message);
            assert_eq!(stats.excluded_artifacts, 0);
            assert_eq!(rows.len(), 1);
            assert_eq!(rows[0].path, nested_project.join("node_modules"));
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn aged_eligible_artifact_matches_full_metadata_discovery() {
        let (_temp, root, _, candidate) = eligible_revalidation_fixture();
        let (stats, rows) = candidates_in_mode(&root, ScanMode::MetadataCoverage);
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.candidates, 1);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].path, candidate.path);
        assert_eq!(rows[0].identity, candidate.identity);
        assert_eq!(rows[0].evidence, candidate.evidence);
        assert_eq!(rows[0].fingerprint, candidate.fingerprint);
        assert_eq!(rows[0].logical_bytes, candidate.logical_bytes);
        assert_eq!(rows[0].allocated_bytes, candidate.allocated_bytes);
        assert_eq!(rows[0].file_count, candidate.file_count);
        assert!(rows[0].suggestion_eligible && rows[0].eligible_permanent);
    }
    #[test]
    fn developer_link_is_a_leaf_without_reading_its_target() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 8);
        symlink("/etc/passwd", project.join("node_modules/external")).unwrap();
        let (_, rows) = candidates_in_mode(&root, ScanMode::MetadataCoverage);
        assert_eq!(rows[0].logical_bytes, 4096);
        assert!(rows[0].blocked_reason.is_none());
        assert_eq!(
            std::fs::read_link(project.join("node_modules/external")).unwrap(),
            Path::new("/etc/passwd")
        );
        assert!(!rows[0].eligible_permanent);
    }
    #[test]
    fn malformed_manifest_and_unrecognized_target_are_excluded() {
        let (_temp, root, project) = fixture();
        std::fs::write(project.join("package.json"), b"this is not JSON").unwrap();
        std::fs::create_dir(project.join("target")).unwrap();
        std::fs::write(project.join("target/personal"), b"keep me").unwrap();
        age_tree(&project, 8);
        let (stats, rows) = candidates(&root);
        assert_eq!(rows.len(), 1);
        assert!(
            rows[0]
                .blocked_reason
                .as_deref()
                .unwrap()
                .contains("valid JSON")
        );
        assert!(!rows[0].suggestion_eligible && !rows[0].provisional);
        assert!(stats.skipped >= 2);
        assert_eq!(stats.excluded_artifacts, 2);
        assert_eq!(
            std::fs::read(project.join("target/personal")).unwrap(),
            b"keep me"
        );
    }
    #[test]
    fn git_output_wait_does_not_poll_eof_while_a_child_is_still_alive() {
        let delay = git_output_wait_duration(false, || {
            panic!("EOF must sleep rather than repeatedly poll a hung-up pipe")
        });
        assert_eq!(delay, Duration::from_millis(15));
    }

    #[test]
    fn git_output_wait_returns_to_read_and_status_checks_after_readiness_or_timeout() {
        for (count, events, elapsed) in [
            (0, 0, Duration::from_millis(15)),
            (1, libc::POLLIN, Duration::from_millis(2)),
            (1, libc::POLLHUP, Duration::from_millis(3)),
            (1, libc::POLLIN | libc::POLLHUP, Duration::from_millis(4)),
        ] {
            assert_eq!(
                git_output_wait_duration(true, || (count, events, elapsed)),
                Duration::ZERO,
                "Readiness and EOF are wakeups, never ownership decisions"
            );
        }
    }

    #[test]
    fn git_output_wait_errors_and_unknown_events_use_only_the_remaining_quantum() {
        for (count, events) in [
            (-1, 0), // Every poll errno, including EINTR, has this result.
            (1, libc::POLLERR),
            (1, libc::POLLNVAL),
            (1, libc::POLLOUT),
            (1, libc::POLLIN | libc::POLLERR),
            (1, libc::POLLHUP | libc::POLLNVAL),
            (1, 0),
            (0, libc::POLLIN),
            (2, libc::POLLIN),
        ] {
            for (elapsed, remaining) in [(0, 15), (4, 11), (15, 0), (20, 0)] {
                assert_eq!(
                    git_output_wait_duration(true, || {
                        (count, events, Duration::from_millis(elapsed))
                    }),
                    Duration::from_millis(remaining),
                    "count={count}, events={events}, elapsed={elapsed}"
                );
            }
        }
    }

    fn git_output_pipe() -> (std::io::PipeReader, std::io::PipeWriter) {
        // Keep both ends close-on-exec so concurrently spawned test children
        // cannot inherit the writer and delay this pipe's EOF.
        let (reader, writer) = std::io::pipe().unwrap();
        assert_eq!(
            unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_SETFL, libc::O_NONBLOCK) },
            0
        );
        (reader, writer)
    }

    #[test]
    fn git_output_poll_leaves_pipe_bytes_and_eof_for_the_original_reader() {
        let (mut reader, mut writer) = git_output_pipe();
        let mut buffer = [0u8; 256];
        assert_eq!(
            reader.read(&mut buffer).unwrap_err().kind(),
            std::io::ErrorKind::WouldBlock
        );

        // Already-available bytes avoid any timing-sensitive producer race.
        writer.write_all(b"tracked\0").unwrap();
        let ready = poll_git_output(reader.as_raw_fd());
        assert_eq!(ready.0, 1);
        assert_ne!(ready.1 & libc::POLLIN, 0);
        assert_eq!(git_output_wait_duration(true, || ready), Duration::ZERO);
        assert_eq!(reader.read(&mut buffer).unwrap(), b"tracked\0".len());
        assert_eq!(&buffer[..b"tracked\0".len()], b"tracked\0");
        assert_eq!(
            reader.read(&mut buffer).unwrap_err().kind(),
            std::io::ErrorKind::WouldBlock
        );

        // Closing the owned writer produces EOF, not proof of child success.
        drop(writer);
        let hung_up = poll_git_output(reader.as_raw_fd());
        assert_eq!(hung_up.0, 1);
        assert_ne!(hung_up.1 & (libc::POLLIN | libc::POLLHUP), 0);
        assert_eq!(git_output_wait_duration(true, || hung_up), Duration::ZERO);
        assert_eq!(reader.read(&mut buffer).unwrap(), 0);
        assert_eq!(
            git_output_wait_duration(false, || panic!("Do not poll EOF again")),
            Duration::from_millis(15)
        );
    }

    #[test]
    fn tracked_descendant_disqualifies_the_whole_artifact() {
        let (_temp, root, project) = fixture();
        assert!(
            Command::new("/usr/bin/git")
                .args(["init", "-q"])
                .arg(&project)
                .status()
                .unwrap()
                .success()
        );
        assert!(
            Command::new("/usr/bin/git")
                .arg("-C")
                .arg(&project)
                .args(["add", "node_modules/payload"])
                .status()
                .unwrap()
                .success()
        );
        assert!(
            git_untracked(
                &root,
                &project,
                &project.join("node_modules"),
                &AtomicBool::new(false)
            )
            .unwrap_err()
            .contains("tracks")
        );
    }

    fn fixture_git(directory: &Path, args: &[&str]) {
        let output = Command::new("/usr/bin/git")
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .args([
                "-c",
                "user.name=chippytea test",
                "-c",
                "user.email=test@example.invalid",
            ])
            .arg("-C")
            .arg(directory)
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn linked_worktree_fixture() -> (tempfile::TempDir, Root, PathBuf, PathBuf) {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        let main = base.join("main");
        let linked = base.join("linked");
        std::fs::create_dir(&main).unwrap();
        fixture_git(&main, &["init", "--quiet"]);
        std::fs::write(main.join("source"), b"keep source").unwrap();
        fixture_git(&main, &["add", "source"]);
        fixture_git(
            &main,
            &["commit", "--quiet", "--no-gpg-sign", "-m", "fixture"],
        );
        fixture_git(
            &main,
            &[
                "worktree",
                "add",
                "--quiet",
                "--detach",
                linked.to_str().unwrap(),
            ],
        );
        let artifact = linked.join("target");
        std::fs::create_dir_all(artifact.join("debug")).unwrap();
        std::fs::write(artifact.join("debug/binary"), b"disposable build output").unwrap();
        (temp, root, linked, artifact)
    }

    fn assert_case_renamed_artifact_is_tracked(root: &Root, project: &Path) {
        let original = project.join("Node_Modules");
        std::fs::create_dir(&original).unwrap();
        std::fs::write(original.join("tracked-source"), b"preserve tracked source").unwrap();
        fixture_git(project, &["add", "--", "Node_Modules/tracked-source"]);
        let intermediate = project.join("case-rename-intermediate");
        let artifact = project.join("node_modules");
        std::fs::rename(&original, &intermediate).unwrap();
        std::fs::rename(&intermediate, &artifact).unwrap();
        let reason = git_untracked(root, project, &artifact, &AtomicBool::new(false)).unwrap_err();
        assert!(reason.contains("tracks content"), "{reason}");
        assert_eq!(
            std::fs::read(artifact.join("tracked-source")).unwrap(),
            b"preserve tracked source"
        );
    }

    #[test]
    fn git_tracking_rejects_case_renamed_artifacts_in_normal_repositories() {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        let project = base.join("project");
        std::fs::create_dir(&project).unwrap();
        fixture_git(&project, &["init", "--quiet"]);
        assert_case_renamed_artifact_is_tracked(&root, &project);
    }

    #[test]
    fn git_tracking_rejects_case_renamed_artifacts_in_linked_worktrees() {
        let (_temp, root, linked, _) = linked_worktree_fixture();
        assert_case_renamed_artifact_is_tracked(&root, &linked);
    }

    #[test]
    fn git_tracking_treats_wildcard_characters_in_artifact_paths_literally() {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        fixture_git(&base, &["init", "--quiet"]);
        for (literal, sibling) in [
            ("project[ab]", "projecta"),
            ("project*", "project-other"),
            ("project?", "projectx"),
        ] {
            let sibling_artifact = base.join(sibling).join("node_modules");
            std::fs::create_dir_all(&sibling_artifact).unwrap();
            std::fs::write(sibling_artifact.join("source"), b"tracked sibling").unwrap();
            let pathspec = format!(":(literal){sibling}/node_modules/source");
            fixture_git(&base, &["add", "--", &pathspec]);
            let project = base.join(literal);
            let artifact = project.join("node_modules");
            std::fs::create_dir_all(&artifact).unwrap();
            std::fs::write(artifact.join("output"), b"generated fixture").unwrap();
            assert!(git_untracked(&root, &project, &artifact, &AtomicBool::new(false)).is_ok());
            let pathspec = format!(":(literal){literal}/node_modules/output");
            fixture_git(&base, &["add", "--", &pathspec]);
            let reason =
                git_untracked(&root, &project, &artifact, &AtomicBool::new(false)).unwrap_err();
            assert!(reason.contains("tracks content"), "{reason}");
        }
    }

    #[test]
    fn linked_worktree_tracking_uses_validated_local_evidence() {
        let (_temp, root, linked, artifact) = linked_worktree_fixture();
        let cancel = AtomicBool::new(false);
        let evidence = git_untracked(&root, &linked, &artifact, &cancel)
            .unwrap()
            .unwrap();
        assert_eq!(evidence.work_tree, linked);
        assert!(
            evidence
                .directory
                .starts_with(root.path.join("main/.git/worktrees"))
        );
        evidence.unchanged(&root, &cancel).unwrap();
        assert_eq!(
            std::fs::read(linked.join("source")).unwrap(),
            b"keep source"
        );
    }

    #[test]
    fn linked_worktree_metadata_must_share_the_authorization() {
        let (_temp, _root, linked, artifact) = linked_worktree_fixture();
        let narrow = safety::authorize(&linked, "projects").unwrap();
        let reason =
            git_untracked(&narrow, &linked, &artifact, &AtomicBool::new(false)).unwrap_err();
        assert!(
            reason.contains("outside this folder's authorization"),
            "{reason}"
        );
        assert!(artifact.join("debug/binary").exists());
        assert!(git_pointer_path(&narrow, &linked, b"target/../.git").is_err());
    }

    #[test]
    fn linked_worktree_symlinked_metadata_is_rejected() {
        let (_temp, root, linked, artifact) = linked_worktree_fixture();
        let cancel = AtomicBool::new(false);
        let evidence = GitEvidence::capture(&root, &linked, &cancel).unwrap();
        let preserved = evidence.directory.with_file_name("preserved-metadata");
        std::fs::rename(&evidence.directory, &preserved).unwrap();
        symlink(&preserved, &evidence.directory).unwrap();
        assert!(git_untracked(&root, &linked, &artifact, &cancel).is_err());
        assert!(preserved.join("index").exists());
        assert!(artifact.join("debug/binary").exists());
    }

    #[test]
    fn linked_worktree_requires_a_reciprocal_backpointer() {
        let (_temp, root, linked, artifact) = linked_worktree_fixture();
        let cancel = AtomicBool::new(false);
        let evidence = GitEvidence::capture(&root, &linked, &cancel).unwrap();
        std::fs::write(
            evidence.directory.join("gitdir"),
            root.path.join("other/.git").as_os_str().as_bytes(),
        )
        .unwrap();
        let reason = git_untracked(&root, &linked, &artifact, &cancel).unwrap_err();
        assert!(reason.contains("backpointer"), "{reason}");
        assert!(artifact.join("debug/binary").exists());
    }

    #[test]
    fn linked_worktree_index_changes_and_tracked_artifacts_are_rejected() {
        let (_temp, root, linked, artifact) = linked_worktree_fixture();
        let cancel = AtomicBool::new(false);
        let evidence = git_untracked(&root, &linked, &artifact, &cancel)
            .unwrap()
            .unwrap();
        fixture_git(&linked, &["add", "target/debug/binary"]);
        assert!(
            evidence
                .unchanged(&root, &cancel)
                .unwrap_err()
                .contains("changed")
        );
        let reason = git_untracked(&root, &linked, &artifact, &cancel).unwrap_err();
        assert!(reason.contains("tracks content"), "{reason}");
        assert_eq!(
            std::fs::read(artifact.join("debug/binary")).unwrap(),
            b"disposable build output"
        );
    }

    #[test]
    fn linked_worktree_split_indexes_and_config_includes_stay_excluded() {
        let (_temp, root, linked, artifact) = linked_worktree_fixture();
        let cancel = AtomicBool::new(false);
        fixture_git(&linked, &["update-index", "--split-index"]);
        assert!(git_untracked(&root, &linked, &artifact, &cancel).is_err());
        fixture_git(&linked, &["update-index", "--no-split-index"]);
        let evidence = git_untracked(&root, &linked, &artifact, &cancel)
            .unwrap()
            .unwrap();
        std::fs::write(
            evidence.directory.join("config.worktree"),
            b"[include]\n path = /outside/authorization\n",
        )
        .unwrap();
        let reason = git_untracked(&root, &linked, &artifact, &cancel).unwrap_err();
        assert!(reason.contains("includes"), "{reason}");
        for config in [
            b"[IncludeIf \"gitdir:/tmp/\"]\npath = /outside\n".as_slice(),
            b"[includeIf.gitdir:/tmp/]\npath = /outside\n",
            b"# a comment ending with \\\n[include]\npath = /outside\n",
        ] {
            assert!(validate_git_config(config).is_err());
        }
        assert!(validate_git_config(b"[core]\nrepositoryformatversion = 0\n[remote \"origin\"]\nurl = https://example.invalid/include\n").is_ok());
    }

    #[test]
    fn git_index_validation_bounds_truncated_and_malformed_evidence() {
        let (_temp, root, linked, _artifact) = linked_worktree_fixture();
        let evidence = GitEvidence::capture(&root, &linked, &AtomicBool::new(false)).unwrap();
        let bytes = std::fs::read(evidence.directory.join("index")).unwrap();
        validate_git_index(&bytes).unwrap();
        for length in 0..bytes.len() {
            assert!(std::panic::catch_unwind(|| validate_git_index(&bytes[..length])).is_ok());
        }
        assert!(validate_git_index(&bytes[..31]).is_err());
        assert!(validate_git_index(&bytes[..bytes.len() - 1]).is_err());
        let mut invalid = bytes.clone();
        invalid[8..12].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(validate_git_index(&invalid).is_err());
        invalid = bytes;
        invalid[4..8].copy_from_slice(&4u32.to_be_bytes());
        assert!(validate_git_index(&invalid).is_err());
    }

    #[test]
    fn git_config_bom_cannot_hide_includes() {
        for config in [
            b"\xef\xbb\xbf[include]\npath = /outside/authorization\n".as_slice(),
            b"\xef\xbb\xbf[includeIf \"gitdir:/tmp/\"]\npath = /outside/authorization\n",
        ] {
            let reason = validate_git_config(config).unwrap_err();
            assert!(reason.contains("includes"), "{reason}");
        }
        assert!(validate_git_config(b"\xef\xbb\xbf[core]\nrepositoryformatversion = 0\n").is_ok());
    }

    #[test]
    fn revalidation_rejects_changed_contents_and_new_links() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 8);
        let (_, rows) = candidates(&root);
        let mut candidate = rows[0].clone();
        // This test isolates identity/fingerprint checks from host processes.
        candidate.blocked_reason = None;
        std::fs::write(project.join("node_modules/payload"), b"changed").unwrap();
        assert!(revalidate(&root, &candidate, &AtomicBool::new(false)).is_err());
    }

    #[test]
    fn fallible_revalidation_observer_propagates_failure_and_keeps_identity_checks() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 8);
        let (_, rows) = candidates(&root);
        let candidate = &rows[0];
        let cancel = AtomicBool::new(false);
        let mut visits = 0;
        let reason = revalidate_observing(&root, candidate, &cancel, |_, _| {
            visits += 1;
            Err("Manifest persistence failed".into())
        })
        .unwrap_err();
        assert_eq!(reason, "Manifest persistence failed");
        assert_eq!(visits, 1);

        let preserved = project.join("preserved-artifact");
        std::fs::rename(&candidate.path, &preserved).unwrap();
        std::fs::create_dir(&candidate.path).unwrap();
        let mut visits = 0;
        let reason = revalidate_observing(&root, candidate, &cancel, |_, _| {
            visits += 1;
            Ok(())
        })
        .unwrap_err();
        assert!(reason.contains("changed"), "{reason}");
        assert_eq!(
            visits, 0,
            "Changed root identity must fail before streaming entries"
        );
        assert_eq!(
            std::fs::read(preserved.join("payload")).unwrap(),
            [7u8; 4096]
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn revalidation_rejects_ownership_changes_during_the_measurement() {
        let (_temp, root, project, candidate) = eligible_revalidation_fixture();
        let mut changed = false;
        let reason = revalidate_observing(&root, &candidate, &AtomicBool::new(false), |_, _| {
            if !changed {
                std::fs::write(
                    project.join("package.json"),
                    br#"{"name":"changed-project","dependencies":{"x":"2"}}"#,
                )
                .unwrap();
                changed = true;
            }
            Ok(())
        })
        .unwrap_err();
        assert!(changed);
        assert!(
            reason.contains("configuration changed during verification"),
            "{reason}"
        );
        assert!(candidate.path.join("payload").is_file());
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn revalidation_rejects_new_or_nearer_git_tracking_during_measurement() {
        for existing_outer_repository in [false, true] {
            let (_temp, root, project, candidate) = eligible_revalidation_fixture();
            if existing_outer_repository {
                fixture_git(&root.path, &["init", "--quiet"]);
            }
            let mut created = false;
            let reason =
                revalidate_observing(&root, &candidate, &AtomicBool::new(false), |_, _| {
                    if !created {
                        fixture_git(&project, &["init", "--quiet"]);
                        fixture_git(&project, &["add", "node_modules/payload"]);
                        created = true;
                    }
                    Ok(())
                })
                .unwrap_err();
            assert!(created);
            assert!(
                reason.contains("tracks content")
                    || reason.contains("Repository ownership changed"),
                "{reason}"
            );
            assert!(candidate.path.join("payload").is_file());
            assert!(project.join(".git/index").is_file());
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn revalidation_rejects_project_activity_started_during_measurement() {
        struct RunningChild(std::process::Child);
        impl Drop for RunningChild {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        let (_temp, root, project, candidate) = eligible_revalidation_fixture();
        let mut child = None;
        let reason = revalidate_observing(&root, &candidate, &AtomicBool::new(false), |_, _| {
            if child.is_none() {
                child = Some(RunningChild(
                    Command::new("/bin/sleep")
                        .arg("30")
                        .current_dir(&project)
                        .stdin(Stdio::null())
                        .stdout(Stdio::null())
                        .stderr(Stdio::null())
                        .spawn()
                        .unwrap(),
                ));
            }
            Ok(())
        })
        .unwrap_err();
        assert!(reason.contains("running process"), "{reason}");
        assert!(candidate.path.join("payload").is_file());
    }

    #[test]
    fn download_rows_never_offer_permanent_cleanup() {
        let (_temp, mut root, project) = fixture();
        root.kind = "downloads".into();
        let file = std::fs::File::create(project.join("review.dmg")).unwrap();
        file.set_len(LARGE_FILE_BYTES).unwrap();
        let (_, rows) = candidates(&root);
        let download = rows.iter().find(|row| row.kind == "installer").unwrap();
        assert!(!download.eligible_permanent);
        assert!(download.consequence.contains("never earn chips"));
    }
    #[test]
    fn scoped_refresh_remeasures_the_parent_artifact() {
        let (_temp, root, project) = fixture();
        let scope = project.join("node_modules/payload");
        assert_eq!(
            scoped_start(&root, Some(&scope)).unwrap(),
            project.join("node_modules")
        );
        assert!(scoped_start(&root, Some(Path::new("/"))).is_err());
    }

    #[test]
    fn protected_incremental_scope_is_rejected_before_artifact_probes() {
        let (_temp, root, project) = fixture();
        let protected = project.join("node_modules/Library/preserved");
        std::fs::create_dir_all(protected.parent().unwrap()).unwrap();
        std::fs::write(&protected, b"preserved protected contents").unwrap();
        for mode in [ScanMode::Suggestions, ScanMode::MetadataCoverage] {
            let result = safety::tests::with_scope_metadata_observer(
                |_| panic!("Protected input must not reach a scope metadata probe"),
                || {
                    scan_with_checkpoint_mode(
                        &root,
                        Some(&protected),
                        &[],
                        &AtomicBool::new(false),
                        mode,
                        || panic!("Protected input must not start traversal"),
                        |_| panic!("Protected input must not publish a batch"),
                    )
                },
            );
            assert!(result.is_err());
        }
        assert_eq!(
            std::fs::read(protected).unwrap(),
            b"preserved protected contents"
        );
    }

    #[test]
    fn cargo_requires_standard_evidence_and_blocks_custom_output_paths() {
        let (_temp, root, project) = fixture();
        let artifact = project.join("target");
        std::fs::create_dir(&artifact).unwrap();
        std::fs::write(
            project.join("Cargo.toml"),
            "[package]\nname = 'fixture'\nversion = '0.1.0'\n",
        )
        .unwrap();
        assert!(
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .is_none()
        );
        std::fs::write(
            artifact.join("CACHEDIR.TAG"),
            b"Signature: 8a477f597d28d172789f06886806bc55\n",
        )
        .unwrap();
        assert!(
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .is_some()
        );
        std::fs::create_dir(project.join(".cargo")).unwrap();
        std::fs::write(
            project.join(".cargo/config.toml"),
            "[build]\ntarget-dir = '../shared-output'\n",
        )
        .unwrap();
        assert!(
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .unwrap()
                .blocked
                .is_some()
        );
    }

    #[test]
    fn nested_cargo_workspace_owns_its_default_output() {
        let (_temp, root, project) = fixture();
        let artifact = project.join("target");
        std::fs::create_dir(&artifact).unwrap();
        std::fs::write(
            artifact.join("CACHEDIR.TAG"),
            b"Signature: 8a477f597d28d172789f06886806bc55\n",
        )
        .unwrap();
        std::fs::write(
            root.path.join("Cargo.toml"),
            "[workspace]\nmembers = ['other']\n",
        )
        .unwrap();
        std::fs::write(
            project.join("Cargo.toml"),
            "[package]\nname = 'fixture'\nversion = '0.1.0'\n[workspace]\n",
        )
        .unwrap();
        let first = cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
            .unwrap()
            .unwrap();
        assert!(first.blocked.is_none());
        std::fs::write(
            root.path.join("Cargo.toml"),
            "[workspace]\nmembers = ['different']\n",
        )
        .unwrap();
        let changed_outer =
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .unwrap();
        assert_eq!(changed_outer.fingerprint, first.fingerprint);
        assert_eq!(changed_outer.latest_modified_ns, first.latest_modified_ns);
        std::fs::write(
            project.join("Cargo.toml"),
            "[package]\nname = 'fixture'\nversion = '0.1.0'\n",
        )
        .unwrap();
        assert!(
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .unwrap()
                .blocked
                .unwrap()
                .contains("ancestor workspace")
        );
        std::fs::write(
            project.join("Cargo.toml"),
            "[package]\nname = 'fixture'\nversion = '0.1.0'\n[workspace]\n",
        )
        .unwrap();
        std::fs::create_dir(root.path.join(".cargo")).unwrap();
        std::fs::write(
            root.path.join(".cargo/config.toml"),
            "[build]\ntarget-dir = 'shared'\n",
        )
        .unwrap();
        assert!(
            cargo_evidence(&root, &project, &artifact, &AtomicBool::new(false), None)
                .unwrap()
                .unwrap()
                .blocked
                .unwrap()
                .contains("nonstandard")
        );
    }

    #[test]
    fn bun_text_lock_is_recognized_and_all_evidence_is_revalidated() {
        let (_temp, root, project) = fixture();
        std::fs::remove_file(project.join("package-lock.json")).unwrap();
        let lock = project.join("bun.lock");
        std::fs::write(
            &lock,
            br#"{
          // Generated lock, with the JSONC extensions Bun writes.
          "lockfileVersion": 1,
          "workspaces": {"": {"name": "fixture",},},
          "packages": {"example": ["https://example.invalid/a//b",],},
        }"#,
        )
        .unwrap();
        let first = node_evidence(&root, &project, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        assert!(first.blocked.is_none());
        assert_eq!(first.activity_root.as_deref(), Some(project.as_path()));
        age_tree(&project, 8);
        let (_, rows) = candidates(&root);
        assert_eq!(rows.len(), 1);
        assert!(rows[0].blocked_reason.is_none());
        assert!(
            !rows[0].suggestion_eligible,
            "Tiny fixtures remain diagnostic"
        );
        std::fs::write(
            project.join("bunfig.toml"),
            "[install]\nlinker = 'hoisted'\n",
        )
        .unwrap();
        let changed = node_evidence(&root, &project, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        assert_ne!(first.fingerprint, changed.fingerprint);
        std::fs::write(&lock, b"{\"lockfileVersion\":1,/*unfinished").unwrap();
        assert!(node_evidence(&root, &project, &AtomicBool::new(false)).is_err());
        assert!(
            node_lock_owns(
                "bun.lock",
                br#"{"lockfileVersion":1,"packages":{},"workspaces":{"":{"name":"https://x.invalid//a",},},}"#,
                "",
                &serde_json::json!({"name":"https://x.invalid//a"}),
                &AtomicBool::new(false),
            )
            .unwrap()
        );
    }

    #[test]
    fn bun_binary_evidence_rejects_truncation_and_oversized_files() {
        let (_temp, root, project) = fixture();
        std::fs::remove_file(project.join("package-lock.json")).unwrap();
        let mut bytes = b"#!/usr/bin/env bun\nbun-lockfile-format-v0\n".to_vec();
        let offset = bytes.len();
        bytes.extend_from_slice(&2u32.to_le_bytes());
        bytes.extend_from_slice(&[7u8; 32]);
        bytes.extend_from_slice(&((offset + 68) as u64).to_le_bytes());
        bytes.extend_from_slice(&[0u8; 24]);
        std::fs::write(project.join("bun.lockb"), &bytes).unwrap();
        assert!(
            node_evidence(&root, &project, &AtomicBool::new(false))
                .unwrap()
                .unwrap()
                .blocked
                .is_none()
        );
        assert!(
            !node_lock_owns(
                "bun.lockb",
                &bytes,
                "apps/member",
                &serde_json::json!({"name":"fixture"}),
                &AtomicBool::new(false),
            )
            .unwrap()
        );
        bytes.truncate(offset + 43);
        std::fs::write(project.join("bun.lockb"), &bytes).unwrap();
        assert!(node_evidence(&root, &project, &AtomicBool::new(false)).is_err());
        std::fs::File::create(project.join("bun.lockb"))
            .unwrap()
            .set_len(4 * 1024 * 1024 + 1)
            .unwrap();
        assert!(
            node_evidence(&root, &project, &AtomicBool::new(false))
                .err()
                .unwrap()
                .contains("small")
        );
    }

    fn workspace_fixture() -> (tempfile::TempDir, Root, PathBuf, PathBuf) {
        let (temp, root, owner) = fixture();
        std::fs::remove_file(owner.join("package-lock.json")).unwrap();
        std::fs::write(
            owner.join("package.json"),
            br#"{"name":"fixture","workspaces":["apps/*"]}"#,
        )
        .unwrap();
        let member = owner.join("apps/member");
        std::fs::create_dir_all(member.join("node_modules")).unwrap();
        std::fs::write(
            member.join("package.json"),
            br#"{"name":"member","dependencies":{"example":"1"}}"#,
        )
        .unwrap();
        std::fs::write(member.join("node_modules/payload"), [5u8; 4096]).unwrap();
        (temp, root, owner, member)
    }

    #[test]
    fn workspace_component_globs_keep_literal_order_and_path_boundaries() {
        for (pattern, relative, expected) in [
            ("crates/plugin-*", "crates/plugin-a", true),
            ("crates/plugin-*", "crates/plugin-", true),
            ("crates/plugin-*", "crates/plugin-a/nested", false),
            ("crates/*-plugin", "crates/a-plugin", true),
            ("crates/*-plugin", "crates/plugin-a", false),
            ("crates/ad*pt*r", "crates/adapter", true),
            ("packages/*ab*bc", "packages/abc", false),
            ("packages/pre*mid*suf", "packages/pre-suf-mid-suf", true),
            ("packages/pre*mid*suf", "packages/pre-suf-mid", false),
            ("packages/é*-工具", "packages/éx-工具", true),
            ("packages/*-plugin", "packages/.hidden-plugin", false),
            ("packages/.*-plugin", "packages/.hidden-plugin", true),
            ("packages/*", "packages/.hidden", false),
            ("src/**/plugin-*", "src/deep/nested/plugin-a", true),
            ("src/**/plugin-*", "src/plugin-a", true),
            ("src/**/plugin-*", "src/.hidden/plugin-a", false),
            ("src/.hidden/**/plugin-*", "src/.hidden/plugin-a", true),
            (
                "src/**/.hidden/plugin-*",
                "src/outer/.hidden/plugin-a",
                true,
            ),
            ("./packages/*-ui/", "packages/example-ui", true),
        ] {
            assert_eq!(
                workspace_pattern(pattern, relative).unwrap(),
                expected,
                "{pattern:?} against {relative:?}"
            );
        }
    }

    #[test]
    fn workspace_globs_keep_root_only_membership_negations_and_syntax_limits() {
        for pattern in [".", "./"] {
            assert!(workspace_pattern(pattern, "").unwrap());
            for nested in ["apps/member", ".", ".."] {
                assert!(!workspace_pattern(pattern, nested).unwrap());
            }
        }
        let patterns = [
            ".",
            "apps/*",
            "crates/plugin-*",
            "!apps/private-*",
            "!crates/*-internal",
        ]
        .map(str::to_owned);
        for relative in ["", "apps/public", "crates/plugin-browser"] {
            assert!(workspace_includes(&patterns, relative).unwrap());
        }
        for relative in [
            "apps/private-console",
            "crates/plugin-internal",
            "crates/other",
            "apps/public/nested",
            "other/member",
        ] {
            assert!(!workspace_includes(&patterns, relative).unwrap());
        }
        let patterns = ["apps/**".to_owned(), "!apps/*private".to_owned()];
        assert!(workspace_includes(&patterns, "apps/public").unwrap());
        assert!(!workspace_includes(&patterns, "apps/team-private").unwrap());
        assert!(!workspace_includes(&patterns, "apps/.private").unwrap());
        for unsupported in [
            "crates/pre**post",
            "crates/***",
            "crates/plugin-?",
            "crates/plugin-[ab]",
            "crates/{a,b}",
            "crates/plugin-!a",
            "crates/plugin-\\*",
            "crates/@(plugin)*",
            "crates/+(plugin)*",
            "crates/plugin(a)*",
            "crates/a|b*",
            "crates/../*",
            "crates/./*",
        ] {
            let patterns = ["apps/*".to_owned(), unsupported.to_owned()];
            assert!(
                workspace_includes(&patterns, "apps/member").is_err(),
                "An earlier match must not hide unsupported syntax: {unsupported}"
            );
        }
    }

    fn manifest_cacheable(source: &[u8]) -> Vec<u8> {
        let mut bytes = source.to_vec();
        bytes.resize(bytes.len().max(MIN_MANIFEST_CACHE_BYTES), b' ');
        bytes
    }

    fn manifest_cache_document(patterns: &[&str]) -> Vec<u8> {
        manifest_cacheable(
            &serde_json::to_vec(&serde_json::json!({ "workspaces": patterns })).unwrap(),
        )
    }

    // Reference the unchanged, uncached pipeline instead of another cache path.
    fn uncached_manifest_patterns(bytes: &[u8], relative: &str) -> Result<(Vec<String>, bool)> {
        let manifest = node_manifest(bytes)?;
        let patterns = manifest_workspaces(&manifest)?;
        let included = workspace_includes(&patterns, relative)?;
        Ok((patterns, included))
    }

    fn assert_manifest_budget(cache: &ManifestWorkspaceCache) {
        let pattern_bytes: usize = cache
            .entries
            .iter()
            .map(|entry| {
                entry.patterns.capacity() * size_of::<String>()
                    + entry.patterns.iter().map(String::capacity).sum::<usize>()
            })
            .sum();
        assert_eq!(
            cache.retained_bytes,
            cache.entries.capacity() * size_of::<CachedManifestWorkspaces>() + pattern_bytes
        );
        assert!(cache.entries.len() <= cache.entry_limit);
        assert!(cache.entry_limit <= MAX_MANIFEST_CACHE_ENTRIES);
        assert!(cache.retained_bytes <= cache.byte_limit);
        assert!(cache.byte_limit <= MAX_MANIFEST_CACHE_BYTES);
    }

    fn assert_manifest_parity(source: &[u8], expected: Result<bool>) {
        assert_eq!(
            uncached_manifest_patterns(source, "apps/member").map(|(_, included)| included),
            expected,
            "unexpected uncached result: {source:?}"
        );
        let padded = manifest_cacheable(source);
        let cancel = AtomicBool::new(false);
        for mut cache in [
            ManifestWorkspaceCache::default(),
            ManifestWorkspaceCache::with_limits(0, 0),
        ] {
            for _ in 0..2 {
                assert_eq!(
                    cache.includes_captured(blake3::hash(&padded), &padded, "apps/member", &cancel),
                    expected,
                );
                assert_manifest_budget(&cache);
            }
            assert_eq!(
                cache.entries.len(),
                usize::from(expected.is_ok() && cache.entry_limit > 0)
            );
        }
    }

    #[test]
    fn manifest_workspace_cache_preserves_json_recognition_and_error_priority() {
        let invalid = "package.json is not valid JSON";
        let object = "package.json is not an object";
        let project = "The package manifest does not identify a project";
        let list = "Workspace membership is not a supported list";
        let paths = "Workspace membership is not a list of paths";
        let local = "Workspace paths are not supported local relative patterns";
        let complex = "Complex workspace patterns need manual inspection";
        let limit = "Workspace membership exceeds the bounded evidence limit";
        let cases: &[(&[u8], std::result::Result<bool, &str>)] = &[
            (b"{", Err(invalid)),
            (b"[]", Err(object)),
            (b"null", Err(object)),
            (br#""name""#, Err(object)),
            (b"{}", Err(project)),
            (
                br#"{"peerDependencies":{},"scripts":{},"private":true}"#,
                Err(project),
            ),
            (br#"{"name":""}"#, Err(project)),
            (br#"{"name":" \t\u2003"}"#, Err(project)),
            (br#"{"name":"owner"}"#, Ok(false)),
            (br#"{"dependencies":{}}"#, Ok(false)),
            (br#"{"devDependencies":{}}"#, Ok(false)),
            (br#"{"optionalDependencies":{}}"#, Ok(false)),
            (br#"{"dependencies":[]}"#, Err(project)),
            (br#"{"workspaces":[]}"#, Ok(false)),
            (br#"{"workspaces":{}}"#, Err(list)),
            (br#"{"name":"owner","workspaces":null}"#, Err(list)),
            (br#"{"name":42,"workspaces":["apps/*"]}"#, Ok(true)),
            (
                br#"{"workspaces":{"packages":["apps/*"],"nohoist":7}}"#,
                Ok(true),
            ),
            (
                br#"{"workspaces":[false],"work\u0073paces":["apps/*"]}"#,
                Ok(true),
            ),
            (
                br#"{"workspaces":["apps/*"],"workspaces":["other/*"]}"#,
                Ok(false),
            ),
            (
                br#"{"workspaces":{"packages":[false],"pack\u0061ges":["apps/*"]}}"#,
                Ok(true),
            ),
            (
                br#"{"name":"owner","name":"","workspaces":null}"#,
                Err(project),
            ),
            (br#"{"dependencies":{},"dependencies":null}"#, Err(project)),
            (
                br#"{"name":"owner","metadata":[},"metadata":0}"#,
                Err(invalid),
            ),
            (br#"{"name":"owner","metadata":1e999}"#, Err(invalid)),
            (br#"{"name":"owner","metadata":"\ud800"}"#, Err(invalid)),
            (b"{\"name\":\"owner\",\"metadata\":\"\xff\"}", Err(invalid)),
            (br#"{"name":"owner"} trailing"#, Err(invalid)),
            (br#"{"workspaces":["bad?",7]}"#, Err(paths)),
            (br#"{"workspaces":["apps/*","bad?"]}"#, Err(complex)),
            (br#"{"workspaces":["!apps/*","bad?"]}"#, Err(complex)),
            (br#"{"workspaces":["/bad","bad?"]}"#, Err(local)),
            (br#"{"workspaces":["bad?","/bad"]}"#, Err(complex)),
        ];
        for (source, expected) in cases {
            assert_manifest_parity(source, expected.map_err(str::to_owned));
        }
        let mut patterns = vec![serde_json::json!("apps/*"); 513];
        patterns[0] = serde_json::json!("bad?");
        let encoded = |patterns: &[Value]| {
            serde_json::to_vec(&serde_json::json!({ "workspaces": patterns })).unwrap()
        };
        assert_manifest_parity(&encoded(&patterns), Err(limit.into()));
        patterns[512] = serde_json::json!(false);
        assert_manifest_parity(&encoded(&patterns), Err(paths.into()));
        let deep = format!(
            "{{\"name\":\"owner\",\"metadata\":{}0{}}}",
            "[".repeat(256),
            "]".repeat(256)
        );
        assert_manifest_parity(deep.as_bytes(), Err(invalid.into()));
    }

    #[test]
    fn manifest_workspace_cache_rechecks_relative_paths_and_changed_digests() {
        let source = manifest_cache_document(&[
            ".",
            "apps/*",
            "!apps/private-*",
            "src/**/plugin-*",
            "packages/é*-工具",
            "visible/.hidden/*",
        ]);
        let digest = blake3::hash(&source);
        let cancel = AtomicBool::new(false);
        let mut cache = ManifestWorkspaceCache::default();
        for (relative, expected) in [
            ("unrelated", false), // An Ok(false) miss still admits reusable facts.
            ("apps/member", true),
            ("apps/private-tool", false),
            ("apps/.hidden", false),
            ("apps/member/nested", false),
            ("", true),
            (".", false),
            ("src/deep/plugin-example", true),
            ("src/.hidden/plugin-example", false),
            ("packages/éx-工具", true),
            ("packages/e\u{301}x-工具", false),
            ("visible/.hidden/member", true),
        ] {
            assert_eq!(
                cache.includes_captured(digest, &source, relative, &cancel),
                Ok(expected)
            );
            assert_eq!(
                uncached_manifest_patterns(&source, relative).unwrap().1,
                expected
            );
            assert_eq!(cache.entries.len(), 1);
            assert_manifest_budget(&cache);
        }
        assert_eq!(
            cache.entries[0].patterns,
            manifest_workspaces(&node_manifest(&source).unwrap()).unwrap()
        );
        let changed = String::from_utf8(source.clone())
            .unwrap()
            .replace("apps/*", "else/*")
            .into_bytes();
        assert_eq!(source.len(), changed.len());
        assert_eq!(
            cache.includes_captured(blake3::hash(&changed), &changed, "apps/member", &cancel),
            Ok(false)
        );
        assert_eq!(
            cache.includes_captured(digest, &source, "apps/member", &cancel),
            Ok(true)
        );
        assert_eq!(cache.entries.len(), 2);
        assert_manifest_budget(&cache);
    }

    #[test]
    fn manifest_workspace_cache_charges_capacities_and_evicts_lru_entries() {
        let cancel = AtomicBool::new(false);
        let [a, b, c] = ["a/*", "b/*", "c/*"].map(|pattern| manifest_cache_document(&[pattern]));
        let mut cache = ManifestWorkspaceCache::with_limits(2, 4096);
        for source in [&a, &b, &a, &c] {
            assert_eq!(
                cache.includes_captured(blake3::hash(source), source, "missing", &cancel),
                Ok(false)
            );
            assert_manifest_budget(&cache);
        }
        assert_eq!(cache.entries.len(), 2);
        assert_eq!(cache.entries[0].digest, blake3::hash(&a));
        assert_eq!(cache.entries[1].digest, blake3::hash(&c));

        let inflate = || {
            let mut pattern = String::with_capacity(128);
            pattern.push_str("apps/*");
            let mut patterns = Vec::with_capacity(8);
            patterns.push(pattern);
            patterns
        };
        let patterns = inflate();
        let heap_bytes = patterns.capacity() * size_of::<String>() + patterns[0].capacity();
        let budget = size_of::<CachedManifestWorkspaces>() + heap_bytes;
        let mut exact = ManifestWorkspaceCache::with_limits(1, budget);
        assert_eq!(
            exact.finish_miss(
                blake3::hash(&a),
                MIN_MANIFEST_CACHE_BYTES,
                Ok((patterns, true)),
                &cancel
            ),
            Ok(true)
        );
        assert_eq!(exact.retained_bytes, budget);
        assert_manifest_budget(&exact);
        let mut too_small = ManifestWorkspaceCache::with_limits(1, budget - 1);
        assert_eq!(
            too_small.finish_miss(
                blake3::hash(&a),
                MIN_MANIFEST_CACHE_BYTES,
                Ok((inflate(), true)),
                &cancel
            ),
            Ok(true)
        );
        assert!(too_small.entries.is_empty());
        assert_manifest_budget(&too_small);

        let entry = CachedManifestWorkspaces {
            digest: blake3::hash(&a),
            patterns: uncached_manifest_patterns(&a, "a/member").unwrap().0,
        };
        let mut bytes_limited = ManifestWorkspaceCache::with_limits(
            2,
            2 * size_of::<CachedManifestWorkspaces>() + entry.heap_bytes().unwrap(),
        );
        for source in [&a, &b] {
            assert_eq!(
                bytes_limited.includes_captured(blake3::hash(source), source, "missing", &cancel),
                Ok(false)
            );
            assert_manifest_budget(&bytes_limited);
        }
        assert_eq!(bytes_limited.entries.len(), 1);
        assert_eq!(bytes_limited.entries[0].digest, blake3::hash(&b));
    }

    #[test]
    fn manifest_workspace_cache_oversized_valid_patterns_never_evict() {
        let cancel = AtomicBool::new(false);
        let small = manifest_cache_document(&["apps/*"]);
        let mut cache = ManifestWorkspaceCache::default();
        assert!(
            cache
                .includes_captured(blake3::hash(&small), &small, "apps/member", &cancel)
                .unwrap()
        );
        let retained = cache.retained_bytes;
        // The existing matcher trims trailing slashes before its length check.
        let long = format!("apps/*{}", "/".repeat(MAX_MANIFEST_CACHE_BYTES + 1));
        let oversized = manifest_cache_document(&[&long]);
        for (relative, expected) in [("apps/member", true), ("other/member", false)] {
            assert_eq!(
                uncached_manifest_patterns(&oversized, relative).unwrap().1,
                expected
            );
            assert_eq!(
                cache.includes_captured(blake3::hash(&oversized), &oversized, relative, &cancel),
                Ok(expected)
            );
            assert_eq!(cache.retained_bytes, retained);
            assert_eq!(cache.entries.len(), 1);
            assert_eq!(cache.entries[0].digest, blake3::hash(&small));
        }
        let invalid = manifest_cache_document(&[&long, "bad?"]);
        assert_eq!(
            cache.includes_captured(blake3::hash(&invalid), &invalid, "apps/member", &cancel),
            Err("Complex workspace patterns need manual inspection".into())
        );
        assert_eq!(cache.retained_bytes, retained);
        assert_eq!(cache.entries[0].digest, blake3::hash(&small));
        assert_manifest_budget(&cache);
    }

    #[test]
    fn manifest_workspace_cache_bypasses_small_inputs_and_disabled_budgets() {
        let source = br#"{"workspaces":["apps/*"]}"#;
        let cancel = AtomicBool::new(false);
        for length in [
            MIN_MANIFEST_CACHE_BYTES - 1,
            MIN_MANIFEST_CACHE_BYTES,
            MIN_MANIFEST_CACHE_BYTES + 1,
        ] {
            let mut bytes = source.to_vec();
            bytes.resize(length, b' ');
            let mut cache = ManifestWorkspaceCache::default();
            for _ in 0..2 {
                assert_eq!(
                    cache.includes_captured(blake3::hash(&bytes), &bytes, "apps/member", &cancel),
                    Ok(true)
                );
            }
            assert_eq!(
                cache.entries.len(),
                usize::from(length >= MIN_MANIFEST_CACHE_BYTES)
            );
            assert_manifest_budget(&cache);
        }
        let large = manifest_cacheable(source);
        for (entries, bytes) in [
            (0, 4096),
            (8, 0),
            (8, size_of::<CachedManifestWorkspaces>() - 1),
        ] {
            let mut cache = ManifestWorkspaceCache::with_limits(entries, bytes);
            assert_eq!(
                cache.includes_captured(blake3::hash(&large), &large, "apps/member", &cancel),
                Ok(true)
            );
            assert!(cache.entries.is_empty());
            assert_manifest_budget(&cache);
        }
        assert_manifest_budget(&ManifestWorkspaceCache::with_limits(usize::MAX, usize::MAX));
    }

    #[test]
    fn manifest_workspace_cache_cancellation_preserves_error_priority_and_state() {
        use std::sync::atomic::Ordering;
        let cancel = AtomicBool::new(false);
        let [a, b, c] = ["a/*", "b/*", "c/*"].map(|pattern| manifest_cache_document(&[pattern]));
        let mut cache = ManifestWorkspaceCache::default();
        for source in [&a, &b] {
            cache
                .includes_captured(blake3::hash(source), source, "missing", &cancel)
                .unwrap();
        }
        let digests: Vec<_> = cache.entries.iter().map(|entry| entry.digest).collect();
        let retained = cache.retained_bytes;
        cancel.store(true, Ordering::Relaxed);
        for source in [&a[..], &b[..], &c[..], b"\xff"] {
            assert_eq!(
                cache.includes_captured(blake3::hash(source), source, "a/member", &cancel),
                Err("Cancelled".into())
            );
        }
        // Feed the actual completed uncached pipeline to the admission boundary,
        // with cancellation requested after evaluation instead of a racy timer.
        for source in [
            a.as_slice(),
            c.as_slice(),
            b"\xff",
            br#"{"workspaces":{}}"#,
            br#"{"workspaces":["bad?",7]}"#,
            br#"{"workspaces":["a/*","bad?"]}"#,
        ] {
            cancel.store(false, Ordering::Relaxed);
            let parsed = uncached_manifest_patterns(source, "a/member");
            let expected = match &parsed {
                Ok(_) => Err("Cancelled".into()),
                Err(error) => Err(error.clone()),
            };
            cancel.store(true, Ordering::Relaxed);
            assert_eq!(
                cache.finish_miss(blake3::hash(source), source.len(), parsed, &cancel),
                expected
            );
        }
        assert_eq!(cache.retained_bytes, retained);
        assert_eq!(
            cache
                .entries
                .iter()
                .map(|entry| entry.digest)
                .collect::<Vec<_>>(),
            digests
        );
        assert_manifest_budget(&cache);
    }

    // Frozen pre-cache oracle. Keep its scalar rules and ownership walk
    // independent from the shared importer visitor and fact compaction.
    fn original_pnpm_scalar(value: &str) -> Result<&str> {
        let value = value.trim();
        let value = if value.len() >= 2
            && ((value.starts_with('\'') && value.ends_with('\''))
                || (value.starts_with('"') && value.ends_with('"')))
        {
            &value[1..value.len() - 1]
        } else {
            if value.starts_with(['*', '!']) {
                return Err("YAML aliases and tags cannot establish workspace ownership".into());
            }
            value
        };
        if value.is_empty()
            || value.contains(['\'', '"', '\\', '#', '&', '|', '>', '{', '}', '[', ']'])
        {
            return Err("Complex pnpm workspace evidence needs manual inspection".into());
        }
        Ok(value)
    }

    fn original_pnpm_lock_owns(bytes: &[u8], relative: &str) -> Result<bool> {
        let text = std::str::from_utf8(bytes).map_err(|_| "The pnpm lockfile is not UTF-8")?;
        let mut version = false;
        let mut importers = false;
        let mut saw_importers = false;
        let mut owns = false;
        let mut packages = false;
        for line in text.lines() {
            if line.trim().is_empty() || line.trim_start().starts_with('#') {
                continue;
            }
            if let Some(value) = line.strip_prefix("lockfileVersion:") {
                if version {
                    return Err("Duplicate pnpm lockfile version is ambiguous".into());
                }
                if !matches!(original_pnpm_scalar(value)?, "6.0" | "9.0") {
                    return Err("This pnpm lockfile version needs manual inspection".into());
                }
                version = true;
            }
            if !line.starts_with(' ') {
                importers = line == "importers:";
                if importers {
                    if saw_importers {
                        return Err("Duplicate pnpm importers are ambiguous".into());
                    }
                    saw_importers = true;
                }
                packages |= line == "packages:" || line == "packages: {}";
            } else if importers && line.starts_with("  ") && !line.starts_with("   ") {
                let key = line
                    .trim()
                    .strip_suffix(": {}")
                    .or_else(|| line.trim().strip_suffix(':'))
                    .ok_or("Complex pnpm importer evidence needs manual inspection")?;
                owns |=
                    original_pnpm_scalar(key)? == if relative.is_empty() { "." } else { relative };
            }
        }
        if !version || !saw_importers || !packages {
            return Err("The pnpm lockfile lacks recognized importer and package evidence".into());
        }
        Ok(owns)
    }

    fn pnpm_cacheable(source: &[u8]) -> Vec<u8> {
        // Prefix an ignored blank line instead of changing the last line's
        // exact whitespace or turning a final lone CR into a CRLF terminator.
        let mut bytes = Vec::new();
        if source.len() < MIN_PNPM_CACHE_BYTES {
            bytes.resize(MIN_PNPM_CACHE_BYTES - source.len() - 1, b' ');
            bytes.push(b'\n');
        }
        bytes.extend_from_slice(source);
        bytes
    }

    fn pnpm_cache_document(key: &str) -> Vec<u8> {
        pnpm_cacheable(
            format!("lockfileVersion: '9.0'\nimporters:\n  '{key}': {{}}\npackages: {{}}\n")
                .as_bytes(),
        )
    }

    fn assert_pnpm_budget(cache: &PnpmLockCache) {
        let actual = cache.entries.capacity() * size_of::<CachedPnpm>()
            + cache
                .entries
                .iter()
                .map(|entry| entry.facts.heap_bytes())
                .sum::<usize>();
        assert_eq!(cache.retained_bytes, actual);
        assert!(actual <= cache.byte_limit);
        assert!(cache.entries.len() <= cache.entry_limit);
    }

    fn assert_pnpm_parity(source: &[u8]) {
        let cancel = AtomicBool::new(false);
        let padded = pnpm_cacheable(source);
        let digest = blake3::hash(&padded);
        let mut cache = PnpmLockCache::default();
        let mut disabled = PnpmLockCache::with_limits(0, 0);
        for relative in [
            "", ".", "./", "a", "b", "a/b", "a/", "é", "e\u{301}", "a\0b", "missing",
        ] {
            let expected = original_pnpm_lock_owns(source, relative);
            assert_eq!(original_pnpm_lock_owns(&padded, relative), expected);
            assert_eq!(pnpm_lock_owns(source, relative), expected);
            assert_eq!(
                disabled.owns_captured(digest, &padded, relative, &cancel),
                expected,
            );
            for _ in 0..2 {
                assert_eq!(
                    cache.owns_captured(digest, &padded, relative, &cancel),
                    expected,
                    "pnpm cache parity for {relative:?}: {source:?}",
                );
            }
        }
        assert_pnpm_budget(&cache);
        assert_pnpm_budget(&disabled);
        assert!(disabled.entries.is_empty());
        if original_pnpm_lock_owns(source, "").is_err() {
            assert!(cache.entries.is_empty());
        } else {
            assert_eq!(cache.entries.len(), 1);
        }
    }

    #[test]
    fn pnpm_fact_cache_preserves_original_grammar_and_error_order() {
        let shape = "The pnpm lockfile lacks recognized importer and package evidence";
        let scalar = "Complex pnpm workspace evidence needs manual inspection";
        let importer = "Complex pnpm importer evidence needs manual inspection";
        let alias = "YAML aliases and tags cannot establish workspace ownership";
        let duplicate_version = "Duplicate pnpm lockfile version is ambiguous";
        let duplicate_importers = "Duplicate pnpm importers are ambiguous";
        let cases: &[(&[u8], std::result::Result<bool, &str>)] = &[
            (b"lockfileVersion: '9.0'\nimporters:\n  .: {}\n  a: {}\npackages: {}\n", Ok(true)),
            (b"packages:\nlockfileVersion: \"6.0\"\nimporters:\n  a:\n    dependencies: {}\n", Ok(true)),
            (b"lockfileVersion: 9.0\r\nimporters:\r\n  a: {}\r\npackages: {}\r\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  a:\npackages: {}\npackages:\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n  b: {}\npackages: {}\n", Ok(false)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  # preserve section\n\n  b: {}\npackages:\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n  \ta: {}\npackages:\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n a: {}\n   a: {}\npackages:\n", Ok(false)),
            (b"lockfileVersion: 9.0\nimporters:\n\tother:\n  a: {}\npackages:\n", Ok(false)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\npackages:\nnot generally valid YAML: [\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n   malformed: [\npackages:\n", Ok(true)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\npackages: {}", Ok(true)),
            (b"", Err(shape)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n", Err(shape)),
            (b"lockfileVersion: 9.0\nimporters: \n  a: {}\npackages:\n", Err(shape)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\npackages: {} \n", Err(shape)),
            (b"lockfileVersion: 8.0\nimporters:\n  a: {}\npackages:\n", Err("This pnpm lockfile version needs manual inspection")),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\nlockfileVersion: *broken\npackages:\n", Err(duplicate_version)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\nimporters:\npackages:\n", Err(duplicate_importers)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  *alias: {}\npackages:\n", Err(alias)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  !tag: {}\npackages:\n", Err(alias)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  '': {}\npackages:\n", Err(scalar)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  'a\\b': {}\npackages:\n", Err(scalar)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  b: null\npackages:\n", Err(importer)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  b:{}\npackages:\n", Err(importer)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  b: { }\npackages:\n", Err(importer)),
            (b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  b: {} # inline\npackages:\n", Err(importer)),
            (b"lockfileVersion: 8.0\nimporters:\n  a: {}\npackages:\n\xff", Err("The pnpm lockfile is not UTF-8")),
        ];
        for (source, expected) in cases {
            assert_eq!(
                original_pnpm_lock_owns(source, "a"),
                expected.map_err(str::to_owned),
                "unexpected frozen pnpm oracle result: {source:?}",
            );
            assert_pnpm_parity(source);
        }
        // Adding cache padding must not normalize unsupported final lone CRs.
        assert_pnpm_parity(b"lockfileVersion: 9.0\nimporters:\n  a: {}\npackages:\r");
    }

    #[test]
    fn pnpm_fact_cache_preserves_scalar_bytes_roots_and_duplicate_or_semantics() {
        let source = concat!(
            "lockfileVersion: 9.0\nimporters:\n",
            "  '.': {}\n  './': {}\n  a: {}\n  a:\n",
            "  'a/b': {}\n  'a: b': {}\n  ' padded ': {}\n",
            "  '*literal': {}\n  '!literal': {}\n  'tab\tkey': {}\n",
            "  'é': {}\n  'e\u{301}': {}\n  'a\0b': {}\npackages:\n",
        );
        let padded = pnpm_cacheable(source.as_bytes());
        let digest = blake3::hash(&padded);
        let cancel = AtomicBool::new(false);
        let mut cache = PnpmLockCache::default();
        for (relative, expected) in [
            ("", true),
            (".", true),
            ("./", true),
            ("a", true),
            ("a/b", true),
            ("a: b", true),
            (" padded ", true),
            ("padded", false),
            ("*literal", true),
            ("!literal", true),
            ("tab\tkey", true),
            ("é", true),
            ("e\u{301}", true),
            ("a\0b", true),
            ("a\0", false),
            ("a/b/c", false),
            ("missing", false),
        ] {
            assert_eq!(
                original_pnpm_lock_owns(source.as_bytes(), relative),
                Ok(expected)
            );
            assert_eq!(pnpm_lock_owns(source.as_bytes(), relative), Ok(expected));
            for _ in 0..2 {
                assert_eq!(
                    cache.owns_captured(digest, &padded, relative, &cancel),
                    Ok(expected)
                );
            }
        }
        assert_eq!(cache.entries[0].facts.keys.len(), 12);
        assert_pnpm_budget(&cache);
        let without_root = pnpm_cache_document("a");
        assert!(
            !cache
                .owns_captured(blake3::hash(&without_root), &without_root, "", &cancel)
                .unwrap()
        );
    }

    #[test]
    fn pnpm_fact_cache_budgets_lru_and_oversized_evidence() {
        let cancel = AtomicBool::new(false);
        let [a, b, c] = ["a", "b", "c"].map(pnpm_cache_document);
        let mut cache = PnpmLockCache::with_limits(2, 4096);
        for (source, key) in [(&a, "a"), (&b, "b"), (&a, "a"), (&c, "c")] {
            assert!(
                cache
                    .owns_captured(blake3::hash(source), source, key, &cancel)
                    .unwrap()
            );
            assert_pnpm_budget(&cache);
        }
        assert_eq!(cache.entries.len(), 2);
        assert_eq!(cache.entries[0].digest, blake3::hash(&a));
        assert_eq!(cache.entries[1].digest, blake3::hash(&c));

        let budget = 2 * size_of::<CachedPnpm>() + size_of::<PnpmKeyRange>() + 1;
        let mut cache = PnpmLockCache::with_limits(2, budget);
        for (source, key) in [(&a, "a"), (&b, "b")] {
            assert!(
                cache
                    .owns_captured(blake3::hash(source), source, key, &cancel)
                    .unwrap()
            );
            assert_pnpm_budget(&cache);
        }
        assert_eq!(cache.entries.len(), 1);
        let retained = cache.retained_bytes;
        let long = "x".repeat(2048);
        let oversized = pnpm_cacheable(
            format!("lockfileVersion: 9.0\nimporters:\n  {long}: {{}}\n  later: {{}}\npackages:\n")
                .as_bytes(),
        );
        for relative in [long.as_str(), "later", "", "missing"] {
            assert_eq!(
                cache.owns_captured(blake3::hash(&oversized), &oversized, relative, &cancel),
                original_pnpm_lock_owns(&oversized, relative),
            );
            assert_eq!(cache.retained_bytes, retained);
            assert_eq!(cache.entries.len(), 1);
            assert_eq!(cache.entries[0].digest, blake3::hash(&b));
        }
        let invalid = [oversized.as_slice(), b"importers:\n"].concat();
        assert_eq!(
            cache.owns_captured(blake3::hash(&invalid), &invalid, "later", &cancel),
            original_pnpm_lock_owns(&invalid, "later"),
        );
        assert!(original_pnpm_lock_owns(&invalid, "later").is_err());
        assert_eq!(cache.retained_bytes, retained);
        assert_eq!(cache.entries[0].digest, blake3::hash(&b));
        assert_pnpm_budget(&cache);
    }

    #[test]
    fn pnpm_fact_cache_bounded_collection_keeps_late_members_and_errors() {
        let cancel = AtomicBool::new(false);
        let mut source = String::from("lockfileVersion: 9.0\nimporters:\n");
        for _ in 0..=MAX_PNPM_CACHE_BYTES / size_of::<&str>() {
            source.push_str("  a: {}\n");
        }
        source.push_str("  later: {}\npackages:\n");
        let mut cache = PnpmLockCache::default();
        let retained = cache.retained_bytes;
        for relative in ["a", "later", "", "missing"] {
            assert_eq!(
                cache.owns_captured(
                    blake3::hash(source.as_bytes()),
                    source.as_bytes(),
                    relative,
                    &cancel
                ),
                original_pnpm_lock_owns(source.as_bytes(), relative),
            );
            assert!(cache.entries.is_empty());
            assert_eq!(cache.retained_bytes, retained);
        }
        source.push_str("lockfileVersion: broken\n");
        assert_eq!(
            cache.owns_captured(
                blake3::hash(source.as_bytes()),
                source.as_bytes(),
                "a",
                &cancel
            ),
            Err("Duplicate pnpm lockfile version is ambiguous".into()),
        );
        assert!(cache.entries.is_empty());
        assert_pnpm_budget(&cache);
    }

    #[test]
    fn pnpm_fact_cache_small_inputs_disabled_budgets_and_cancellation() {
        use std::sync::atomic::Ordering;
        let cancel = AtomicBool::new(false);
        let large = pnpm_cache_document("a");
        let small = b"lockfileVersion: 9.0\nimporters:\n  a: {}\npackages:\n";
        let mut cache = PnpmLockCache::default();
        for source in [small.as_slice(), &large[1..]] {
            assert!(
                cache
                    .owns_captured(blake3::hash(source), source, "a", &cancel)
                    .unwrap()
            );
            assert!(cache.entries.is_empty());
        }
        assert!(
            cache
                .owns_captured(blake3::hash(&large), &large, "a", &cancel)
                .unwrap()
        );
        let b = pnpm_cache_document("b");
        assert!(
            cache
                .owns_captured(blake3::hash(&b), &b, "b", &cancel)
                .unwrap()
        );
        let digests: Vec<_> = cache.entries.iter().map(|entry| entry.digest).collect();
        let retained = cache.retained_bytes;
        cancel.store(true, Ordering::Relaxed);
        for source in [small.as_slice(), large.as_slice(), b.as_slice(), b"\xff"] {
            assert_eq!(
                cache.owns_captured(blake3::hash(source), source, "a", &cancel),
                Err("Cancelled".into()),
            );
        }
        assert_eq!(cache.retained_bytes, retained);
        assert_eq!(
            cache
                .entries
                .iter()
                .map(|entry| entry.digest)
                .collect::<Vec<_>>(),
            digests
        );
        cancel.store(false, Ordering::Relaxed);
        assert!(
            cache
                .owns_captured(blake3::hash(&large), &large, "a", &cancel)
                .unwrap()
        );
        assert_pnpm_budget(&cache);
        for (entries, bytes) in [(0, 4096), (8, 0), (8, size_of::<CachedPnpm>() - 1)] {
            let mut disabled = PnpmLockCache::with_limits(entries, bytes);
            for source in [small.as_slice(), large.as_slice(), b"\xff"] {
                assert_eq!(
                    disabled.owns_captured(blake3::hash(source), source, "a", &cancel),
                    original_pnpm_lock_owns(source, "a"),
                );
            }
            assert!(disabled.entries.is_empty());
            assert_pnpm_budget(&disabled);
        }
    }

    #[test]
    fn pnpm_importer_visitor_finishes_validation_after_cancellation_is_requested() {
        use std::sync::atomic::Ordering;
        let cancel = AtomicBool::new(false);
        let source =
            b"lockfileVersion: 9.0\nimporters:\n  a: {}\n  b: {}\n  invalid: null\npackages:\n";
        let mut visited = Vec::new();
        let result = visit_pnpm_importers(source, |key| {
            visited.push(key);
            cancel.store(true, Ordering::Relaxed);
        });
        assert_eq!(visited, ["a", "b"]);
        assert_eq!(result, original_pnpm_lock_owns(source, "a").map(|_| ()),);
        assert_eq!(
            result,
            Err("Complex pnpm importer evidence needs manual inspection".into())
        );
        let mut cache = PnpmLockCache::default();
        assert_eq!(
            cache.owns_captured(blake3::hash(source), source, "a", &cancel),
            Err("Cancelled".into()),
        );
        assert!(cache.entries.is_empty());
    }

    #[test]
    fn pnpm_component_globs_require_exact_importers_and_fresh_membership() {
        let (_temp, root, owner, member) = workspace_fixture();
        std::fs::write(owner.join("package.json"), br#"{"name":"fixture"}"#).unwrap();
        let workspace = owner.join("pnpm-workspace.yaml");
        let patterns = "packages:\n  - 'apps/*'\n  - 'crates/plugin-*'\n";
        std::fs::write(&workspace, patterns).unwrap();
        let plugin = owner.join("crates/plugin-example");
        std::fs::create_dir_all(plugin.join("node_modules")).unwrap();
        std::fs::write(plugin.join("package.json"), br#"{"name":"plugin-example"}"#).unwrap();
        let lock = owner.join("pnpm-lock.yaml");
        let locked = "lockfileVersion: '9.0'\nimporters:\n  .: {}\n  apps/member: {}\n  crates/plugin-example: {}\npackages: {}\n";
        std::fs::write(&lock, locked).unwrap();
        let cancel = AtomicBool::new(false);
        for project in [&member, &plugin] {
            let found = node_evidence(&root, project, &cancel).unwrap().unwrap();
            assert!(found.blocked.is_none());
            assert_eq!(found.activity_root.as_deref(), Some(owner.as_path()));
        }
        let first = node_evidence(&root, &member, &cancel).unwrap().unwrap();
        std::fs::write(
            &workspace,
            "packages:\n  - 'apps/m*'\n  - 'crates/*-example'\n",
        )
        .unwrap();
        let changed = node_evidence(&root, &member, &cancel).unwrap().unwrap();
        assert_ne!(first.fingerprint, changed.fingerprint);
        std::fs::write(
            &workspace,
            "packages:\n  - 'apps/*'\n  - 'crates/plugin-*'\n  - '!apps/m*'\n",
        )
        .unwrap();
        assert!(node_evidence(&root, &member, &cancel).is_err());
        std::fs::write(&workspace, patterns).unwrap();
        std::fs::write(
            &lock,
            "lockfileVersion: '9.0'\nimporters:\n  .: {}\n  apps/other: {}\n  crates/plugin-other: {}\npackages: {}\n",
        )
        .unwrap();
        for project in [&member, &plugin] {
            let reason = node_evidence(&root, project, &cancel).err().unwrap();
            assert!(reason.contains("No supported lockfile"), "{reason}");
        }
        assert_eq!(
            std::fs::read(member.join("node_modules/payload")).unwrap(),
            [5u8; 4096]
        );
    }

    #[test]
    fn pnpm_root_only_pattern_never_borrows_ownership_for_nested_projects() {
        let (_temp, root, owner, member) = workspace_fixture();
        std::fs::write(owner.join("package.json"), br#"{"name":"fixture"}"#).unwrap();
        std::fs::write(owner.join("pnpm-workspace.yaml"), "packages:\n  - '.'\n").unwrap();
        // Even a stale member importer cannot override root-only membership.
        std::fs::write(
            owner.join("pnpm-lock.yaml"),
            "lockfileVersion: '9.0'\nimporters:\n  .: {}\n  apps/member: {}\npackages: {}\n",
        )
        .unwrap();
        let cancel = AtomicBool::new(false);
        let found = node_evidence(&root, &owner, &cancel).unwrap().unwrap();
        assert!(found.blocked.is_none());
        assert_eq!(found.activity_root.as_deref(), Some(owner.as_path()));
        let reason = node_evidence(&root, &member, &cancel).err().unwrap();
        assert!(reason.contains("No supported lockfile"), "{reason}");
    }

    #[test]
    fn shared_lock_cache_keeps_live_identity_membership_and_configuration_checks() {
        for (name, original, replacement) in [
            (
                "package-lock.json",
                br#"{"lockfileVersion":3,"packages":{"apps/member":{}}}"#.as_slice(),
                br#"{"lockfileVersion":3,"packages":{"apps/absent":{}}}"#.as_slice(),
            ),
            (
                "bun.lock",
                br#"{"lockfileVersion":1,"packages":{},"workspaces":{"":{"name":"fixture"},"apps/member":{"name":"member"}}}"#.as_slice(),
                br#"{"lockfileVersion":1,"packages":{},"workspaces":{"":{"name":"fixture"},"apps/absent":{"name":"member"}}}"#.as_slice(),
            ),
            (
                "pnpm-lock.yaml",
                b"lockfileVersion: 9.0\nimporters:\n  .: {}\n  apps/member: {}\npackages:\n".as_slice(),
                b"lockfileVersion: 9.0\nimporters:\n  .: {}\n  apps/absent: {}\npackages:\n".as_slice(),
            ),
        ] {
        let (_temp, root, owner, member) = workspace_fixture();
        let owner_manifest = owner.join("package.json");
        let owner_bytes = manifest_cacheable(&std::fs::read(&owner_manifest).unwrap());
        std::fs::write(&owner_manifest, &owner_bytes).unwrap();
        if name == "pnpm-lock.yaml" {
            std::fs::write(
                owner.join("pnpm-workspace.yaml"),
                b"packages:\n  - 'apps/*'\n",
            ).unwrap();
        }
        let lock = owner.join(name);
        let mut bytes = original.to_vec();
        bytes.resize(32 * 1024, b' ');
        std::fs::write(&lock, &bytes).unwrap();
        let cancel = AtomicBool::new(false);
        let mut cache = EvidenceCaches::default();
        let first = node_evidence_cached(&root, &member, &cancel, Some(&mut cache))
            .unwrap()
            .unwrap();
        assert_eq!(cache.manifest_workspaces.entries.len(), 1);
        assert_manifest_budget(&cache.manifest_workspaces);
        if name == "pnpm-lock.yaml" {
            assert_eq!(cache.pnpm_locks.entries.len(), 1);
            assert_pnpm_budget(&cache.pnpm_locks);
        }
        for project in [&owner, &member] {
            let cached = node_evidence_cached(&root, project, &cancel, Some(&mut cache))
                .unwrap()
                .unwrap();
            let fresh = node_evidence(&root, project, &cancel).unwrap().unwrap();
            assert_eq!(cached.fingerprint, fresh.fingerprint);
            assert_eq!(cached.latest_modified_ns, fresh.latest_modified_ns);
            assert_eq!(cached.activity_root, fresh.activity_root);
            assert_eq!(cached.blocked, fresh.blocked);
        }

        if name == "bun.lock" {
            // A fact-cache hit still compares the freshly verified member name.
            let member_manifest = member.join("package.json");
            let saved = std::fs::read(&member_manifest).unwrap();
            std::fs::write(&member_manifest, br#"{"name":"renamed"}"#).unwrap();
            assert!(node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).is_err());
            std::fs::write(&member_manifest, saved).unwrap();
        }
        let mut changed = replacement.to_vec();
        changed.resize(bytes.len(), b' ');
        std::fs::write(&lock, &changed).unwrap();
        assert!(node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).is_err());
        let changed_owner = node_evidence_cached(&root, &owner, &cancel, Some(&mut cache))
            .unwrap()
            .unwrap();
        assert_eq!(
            changed_owner.fingerprint,
            node_evidence(&root, &owner, &cancel)
                .unwrap()
                .unwrap()
                .fingerprint
        );
        std::fs::write(&lock, &bytes).unwrap();

        // An old content-cache hit must still use the current workspace declaration.
        let (membership, replacement_membership): (PathBuf, &[u8]) = if name == "pnpm-lock.yaml" {
            (owner.join("pnpm-workspace.yaml"), b"packages:\n  - 'apps/*'\n  - '!apps/member'\n")
        } else {
            (owner.join("package.json"), br#"{"name":"fixture","workspaces":["other/*"]}"#)
        };
        let original_membership = std::fs::read(&membership).unwrap();
        let replacement_membership = if membership == owner_manifest {
            let padded = manifest_cacheable(replacement_membership);
            assert_eq!(padded.len(), original_membership.len());
            padded
        } else {
            replacement_membership.to_vec()
        };
        std::fs::write(&membership, &replacement_membership).unwrap();
        assert!(node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).is_err());
        std::fs::write(&membership, original_membership).unwrap();

        // Warm parsed patterns cannot authorize a substituted ancestor manifest.
        let outside_manifest = tempfile::tempdir().unwrap();
        let target_manifest = outside_manifest.path().join("package.json");
        std::fs::write(&target_manifest, &owner_bytes).unwrap();
        std::fs::remove_file(&owner_manifest).unwrap();
        std::os::unix::fs::symlink(&target_manifest, &owner_manifest).unwrap();
        assert!(node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).is_err());
        assert_eq!(std::fs::read(&target_manifest).unwrap(), owner_bytes);
        std::fs::remove_file(&owner_manifest).unwrap();
        std::fs::write(&owner_manifest, &owner_bytes).unwrap();

        std::fs::write(owner.join(".yarnrc.yml"), b"nodeLinker: node-modules\n").unwrap();
        let configured = node_evidence_cached(&root, &member, &cancel, Some(&mut cache))
            .unwrap()
            .unwrap();
        assert!(configured.blocked.is_some());
        assert_ne!(configured.fingerprint, first.fingerprint);
        assert_eq!(
            configured.fingerprint,
            node_evidence(&root, &member, &cancel)
                .unwrap()
                .unwrap()
                .fingerprint
        );

        // Even identical cached bytes cannot authorize reading a substituted link.
        let outside = tempfile::tempdir().unwrap();
        let target = outside.path().join("lock.json");
        std::fs::write(&target, &bytes).unwrap();
        std::fs::remove_file(&lock).unwrap();
        std::os::unix::fs::symlink(&target, &lock).unwrap();
        assert!(node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).is_err());
        assert_eq!(std::fs::read(&target).unwrap(), bytes);
        assert_eq!(
            std::fs::read(member.join("node_modules/payload")).unwrap(),
            [5u8; 4096]
        );
        }
    }

    #[test]
    fn manifest_workspace_cache_is_ancestor_only_and_preserves_bun_names() {
        let (_temp, root, owner, member) = workspace_fixture();
        let owner_manifest = owner.join("package.json");
        std::fs::write(
            &owner_manifest,
            manifest_cacheable(&std::fs::read(&owner_manifest).unwrap()),
        )
        .unwrap();
        std::fs::write(
            owner.join("bun.lock"),
            br#"{"lockfileVersion":1,"packages":{},"workspaces":{"":{"name":"fixture"},"apps/member":{"name":"member"}}}"#,
        )
        .unwrap();
        let cancel = AtomicBool::new(false);
        let mut cache = EvidenceCaches::default();
        node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).unwrap();
        assert_eq!(cache.manifest_workspaces.entries.len(), 1);
        for (source, recognized) in [
            (br#"{"name":"member","workspaces":null}"#.as_slice(), true),
            (
                br#"{"name":"","dependencies":{},"workspaces":null}"#.as_slice(),
                false,
            ),
            (
                br#"{"name":" \t","dependencies":{},"workspaces":null}"#.as_slice(),
                false,
            ),
            (
                br#"{"name":null,"dependencies":{},"workspaces":null}"#.as_slice(),
                true,
            ),
            (
                br#"{"dependencies":{},"workspaces":{"packages":false}}"#.as_slice(),
                true,
            ),
        ] {
            std::fs::write(member.join("package.json"), source).unwrap();
            let cached = node_evidence_cached(&root, &member, &cancel, Some(&mut cache));
            assert_eq!(cached.is_ok(), recognized);
            assert_eq!(
                cached.map(|found| found.map(|evidence| evidence.fingerprint)),
                node_evidence(&root, &member, &cancel)
                    .map(|found| found.map(|evidence| evidence.fingerprint))
            );
            assert_eq!(cache.manifest_workspaces.entries.len(), 1);
        }
        std::fs::write(
            &owner_manifest,
            manifest_cacheable(br#"{"name":"fixture","workspaces":false}"#),
        )
        .unwrap();
        assert_eq!(
            node_evidence_cached(&root, &member, &cancel, Some(&mut cache)).err(),
            Some("Workspace membership is not a supported list".into())
        );
        // The same manifest is valid locally: its workspace shape is unused.
        let cached = node_evidence_cached(&root, &owner, &cancel, Some(&mut cache))
            .unwrap()
            .unwrap();
        let fresh = node_evidence(&root, &owner, &cancel).unwrap().unwrap();
        assert_eq!(cached.fingerprint, fresh.fingerprint);
        assert_eq!(cached.blocked, fresh.blocked);
        assert_eq!(cache.manifest_workspaces.entries.len(), 1);
        assert_manifest_budget(&cache.manifest_workspaces);
    }

    #[test]
    fn ancestor_bun_lock_requires_declared_exact_member_and_authorization() {
        let (_temp, root, owner, member) = workspace_fixture();
        let lock = owner.join("bun.lock");
        std::fs::write(&lock, br#"{"lockfileVersion":1,"workspaces":{"":{"name":"fixture"},"apps/member":{"name":"member"}},"packages":{}}"#).unwrap();
        let first = node_evidence(&root, &member, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        assert_eq!(first.activity_root.as_deref(), Some(owner.as_path()));
        let narrow = safety::authorize(&member, "projects").unwrap();
        assert!(
            node_evidence(&narrow, &member, &AtomicBool::new(false)).is_err(),
            "Outside authorization is never borrowed"
        );
        std::fs::write(
            owner.join("package.json"),
            br#"{"name":"fixture","workspaces":["apps/*","!apps/member"]}"#,
        )
        .unwrap();
        assert!(node_evidence(&root, &member, &AtomicBool::new(false)).is_err());
        std::fs::write(
            owner.join("package.json"),
            br#"{"name":"fixture","workspaces":["apps/*"]}"#,
        )
        .unwrap();
        std::fs::write(
            &lock,
            br#"{"lockfileVersion":1,"workspaces":{"":{"name":"fixture"}},"packages":{}}"#,
        )
        .unwrap();
        assert!(
            node_evidence(&root, &member, &AtomicBool::new(false)).is_err(),
            "A glob alone cannot invent a lockfile importer"
        );
        std::fs::write(&lock, br#"{"lockfileVersion":1,"workspaces":{"":{"name":"fixture"},"apps/member":{"name":"member"}},"packages":{}}"#).unwrap();
        std::fs::create_dir(member.join(".git")).unwrap();
        assert!(
            node_evidence(&root, &member, &AtomicBool::new(false)).is_err(),
            "Nested repositories are separate ownership boundaries"
        );
    }

    #[test]
    fn pnpm_workspace_importer_is_recognized_but_shared_store_stays_blocked() {
        let (_temp, root, owner, member) = workspace_fixture();
        std::fs::write(owner.join("package.json"), br#"{"name":"fixture"}"#).unwrap();
        std::fs::write(
            owner.join("pnpm-workspace.yaml"),
            "packages:\n  - 'apps/*'\n  - 'crates/plugin-*'\n",
        )
        .unwrap();
        let lock = owner.join("pnpm-lock.yaml");
        std::fs::write(&lock, pnpm_cacheable(b"lockfileVersion: '9.0'\nimporters:\n  .:\n    dependencies: {}\n  apps/member:\n    dependencies: {}\npackages: {}\n")).unwrap();
        let first = node_evidence(&root, &member, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        assert!(first.blocked.is_none());
        assert_eq!(first.activity_root.as_deref(), Some(owner.as_path()));
        std::fs::create_dir(member.join("node_modules/.pnpm")).unwrap();
        age_tree(&owner, 8);
        let (_, rows) = candidates(&root);
        let row = rows
            .iter()
            .find(|row| row.path == member.join("node_modules"))
            .unwrap();
        assert!(
            row.blocked_reason
                .as_deref()
                .unwrap()
                .contains("shared-store")
        );
        assert!(!row.suggestion_eligible && !row.eligible_permanent);
        std::fs::write(
            owner.join("pnpm-workspace.yaml"),
            "packages:\n  - 'other/*'\n",
        )
        .unwrap();
        assert!(node_evidence(&root, &member, &AtomicBool::new(false)).is_err());
    }

    #[test]
    fn pnpm_workspace_globs_require_quotes_for_yaml_alias_and_tag_prefixes() {
        assert!(pnpm_workspace_patterns(b"packages:\n  - *\n").is_err());
        assert!(pnpm_workspace_patterns(b"packages:\n  - !apps/private\n").is_err());
        let patterns =
            pnpm_workspace_patterns(b"packages:\n  - 'apps/*'\n  - '!apps/private'\n").unwrap();
        assert!(workspace_includes(&patterns, "apps/public").unwrap());
        assert!(!workspace_includes(&patterns, "apps/private").unwrap());
        assert_eq!(yaml_scalar("'*'").unwrap(), "*");
    }

    #[test]
    fn unsupported_install_evidence_has_a_completed_diagnostic_row() {
        let (_temp, root, project) = fixture();
        std::fs::remove_file(project.join("package-lock.json")).unwrap();
        age_tree(&project, 8);
        let (stats, rows) = candidates(&root);
        assert_eq!(rows.len(), 1);
        assert!(
            rows[0]
                .blocked_reason
                .as_deref()
                .unwrap()
                .contains("lockfile")
        );
        assert!(!rows[0].suggestion_eligible && !rows[0].provisional);
        assert_eq!(stats.files, 1);
        assert_eq!(stats.excluded_artifacts, 1);
        assert!(stats.complete);
        assert_eq!(stats.candidates, 0);
    }

    #[test]
    fn checkpoint_is_cooperative_and_cancellation_retains_partial_coverage() {
        let (_temp, root, _) = fixture();
        let calls = std::cell::Cell::new(0);
        let cancel = AtomicBool::new(false);
        let stats = scan_with_checkpoint(
            &root,
            None,
            &[],
            &cancel,
            || {
                calls.set(calls.get() + 1);
                if calls.get() == 3 {
                    cancel.store(true, std::sync::atomic::Ordering::Release);
                }
            },
            |_| {},
        )
        .unwrap();
        assert_eq!(calls.get(), 3);
        assert!(stats.cancelled && !stats.complete);
        assert!(stats.entries > 0);
    }

    fn add_fresh_project(base: &Path, index: usize) -> PathBuf {
        let project = base.join(format!("fresh-{index}"));
        std::fs::create_dir_all(project.join("node_modules")).unwrap();
        std::fs::write(
            project.join("package.json"),
            br#"{"name":"fixture","dependencies":{"x":"1"}}"#,
        )
        .unwrap();
        std::fs::write(
            project.join("package-lock.json"),
            br#"{"lockfileVersion":3,"packages":{}}"#,
        )
        .unwrap();
        std::fs::write(project.join("node_modules/payload"), [7u8; 4096]).unwrap();
        project
    }

    #[test]
    fn deferred_overflow_drains_all_metadata_with_exact_counts() {
        let (_temp, root, _) = fixture();
        for index in 0..=MAX_DEFERRED_ARTIFACTS {
            add_fresh_project(&root.path, index);
        }
        let expected = safety::traverse_metadata(&root.path, &AtomicBool::new(false)).unwrap();
        let (stats, rows) = candidates_in_mode(&root, ScanMode::MetadataCoverage);
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(
            (
                stats.entries,
                stats.files,
                stats.directories,
                stats.logical_bytes
            ),
            (
                expected.entries,
                expected.files,
                expected.directories,
                expected.logical_bytes
            )
        );
        assert_eq!(rows.len(), MAX_DEFERRED_ARTIFACTS + 2);
        assert!(
            rows.iter()
                .all(|row| !row.provisional && !row.suggestion_eligible)
        );
        assert_eq!(stats.candidates, 0);
    }

    #[test]
    fn deferred_artifacts_share_global_hardlink_accounting() {
        let (_temp, root, first) = fixture();
        let second = add_fresh_project(&root.path, 0);
        std::fs::remove_file(second.join("node_modules/payload")).unwrap();
        std::fs::hard_link(
            first.join("node_modules/payload"),
            second.join("node_modules/payload"),
        )
        .unwrap();
        let expected = safety::traverse_metadata(&root.path, &AtomicBool::new(false)).unwrap();
        let (stats, rows) = candidates_in_mode(&root, ScanMode::MetadataCoverage);
        assert!(stats.complete);
        assert_eq!(
            (
                stats.entries,
                stats.files,
                stats.directories,
                stats.logical_bytes
            ),
            (
                expected.entries,
                expected.files,
                expected.directories,
                expected.logical_bytes
            )
        );
        assert_eq!(rows.len(), 2);
        assert!(rows.iter().all(|row| {
            row.blocked_reason
                .as_deref()
                .unwrap()
                .contains("hard-linked")
        }));
        assert!(rows.iter().all(|row| !row.suggestion_eligible));
    }

    #[test]
    fn logical_lanes_share_exact_hardlink_accounting_without_duplicate_bytes() {
        let (_temp, root, first) = fixture();
        let second = add_fresh_project(&root.path, 0);
        let shared = first.join("node_modules/payload");
        let alias = second.join("node_modules/payload");
        std::fs::remove_file(&alias).unwrap();
        std::fs::hard_link(&shared, &alias).unwrap();
        let first_stats = safety::traverse_metadata(&first, &AtomicBool::new(false)).unwrap();
        let second_stats = safety::traverse_metadata(&second, &AtomicBool::new(false)).unwrap();
        let shared_meta = safety::metadata(&shared).unwrap();
        let starts = [first.clone(), second.clone()];
        let mut rows = Vec::new();
        let stats = ScanSession::new(ScanMode::MetadataCoverage)
            .scan(
                &root,
                ScanScope {
                    path: Some(&root.path),
                    expected: None,
                    recent_files: None,
                    starts: Some(&starts),
                },
                &[],
                &AtomicBool::new(false),
                || {},
                |batch| rows.extend(batch.candidates),
            )
            .unwrap();
        assert!(stats.complete, "{stats:?}; rows={rows:?}");
        assert_eq!(stats.entries, first_stats.entries + second_stats.entries);
        assert_eq!(stats.files, first_stats.files + second_stats.files);
        assert_eq!(
            stats.directories,
            first_stats.directories + second_stats.directories
        );
        assert_eq!(
            stats.logical_bytes,
            first_stats
                .logical_bytes
                .saturating_add(second_stats.logical_bytes)
                .saturating_sub(shared_meta.identity.size)
        );
        let dir_allocated = safety::metadata(&first).unwrap().allocated
            + safety::metadata(&first.join("node_modules"))
                .unwrap()
                .allocated
            + safety::metadata(&second).unwrap().allocated
            + safety::metadata(&second.join("node_modules"))
                .unwrap()
                .allocated;
        assert_eq!(
            stats.allocated_bytes,
            first_stats
                .allocated_bytes
                .saturating_add(second_stats.allocated_bytes)
                .saturating_sub(shared_meta.allocated)
                .saturating_sub(dir_allocated)
        );
        assert_eq!(rows.iter().filter(|row| !row.provisional).count(), 2);
        assert!(rows.iter().filter(|row| !row.provisional).all(|row| {
            row.blocked_reason
                .as_deref()
                .is_some_and(|reason| reason.contains("hard-linked"))
        }));
    }

    #[test]
    fn changed_deferred_evidence_is_diagnostic_and_coverage_stays_partial() {
        let (_temp, root, _) = fixture();
        for index in 0..MAX_BATCH {
            add_fresh_project(&root.path, index);
        }
        let mut changed = None;
        let mut rows = std::collections::BTreeMap::new();
        let stats = scan_with_checkpoint_mode(
            &root,
            None,
            &[],
            &AtomicBool::new(false),
            ScanMode::MetadataCoverage,
            || {},
            |batch| {
                for candidate in batch.candidates {
                    if changed.is_none() && candidate.provisional {
                        std::fs::write(
                            candidate.path.parent().unwrap().join("package-lock.json"),
                            br#"{"lockfileVersion":3,"packages":{"new-evidence":{}}}"#,
                        )
                        .unwrap();
                        changed = Some(candidate.id.clone());
                    }
                    rows.insert(candidate.id.clone(), candidate);
                }
            },
        )
        .unwrap();
        let changed =
            changed.expect("Bounded provisional batches must be published during discovery");
        let row = &rows[&changed];
        assert!(!row.provisional && !row.suggestion_eligible);
        assert!(
            row.blocked_reason
                .as_deref()
                .unwrap()
                .contains("evidence changed while waiting")
        );
        assert!(!stats.complete && stats.errors > 0);
    }

    #[test]
    fn replacement_of_a_deferred_artifact_is_rejected() {
        let (_temp, root, project) = fixture();
        let path = project.join("node_modules");
        let entry = Entry {
            path: path.clone(),
            meta: safety::metadata(&path).unwrap(),
        };
        let found = node_evidence(&root, &project, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        std::fs::rename(&path, project.join("preserved-old-output")).unwrap();
        std::fs::create_dir(&path).unwrap();
        std::fs::write(path.join("personal"), b"preserve replacement").unwrap();
        assert!(
            verify_deferred_artifact(&root, &entry, &found, None, &AtomicBool::new(false))
                .unwrap_err()
                .contains("artifact changed while waiting")
        );
        assert_eq!(
            std::fs::read(path.join("personal")).unwrap(),
            b"preserve replacement"
        );
    }

    #[test]
    fn project_activity_is_conservative_without_blocking_unrelated_projects() {
        let snapshot = ActivitySnapshot {
            working_directories: vec![PathBuf::from(
                "/Users/developer/projects/active/subdirectory",
            )],
            executable_paths: vec![PathBuf::from(
                "/Users/developer/projects/running/target/debug/app",
            )],
            running_app_bundle_ids: Default::default(),
        };
        assert!(
            snapshot
                .blocked(Path::new("/Users/developer/projects/active"))
                .is_some()
        );
        assert!(
            snapshot
                .blocked(Path::new("/Users/developer/projects/other"))
                .is_none()
        );
        assert!(
            snapshot
                .blocked(Path::new("/Users/developer/projects/active-sibling"))
                .is_none()
        );
        assert!(
            snapshot
                .blocked(Path::new("/Users/developer/projects/running"))
                .is_some()
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_running_project_process_blocks_a_disposable_artifact() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 8);
        let mut child = Command::new("/bin/sleep")
            .arg("60")
            .current_dir(&project)
            .spawn()
            .unwrap();
        let mut final_row = None;
        let result = scan(&root, None, &AtomicBool::new(false), |batch| {
            for candidate in batch.candidates {
                final_row = Some(candidate);
            }
        });
        let activity = ActivitySnapshot::capture(&AtomicBool::new(false));
        let _ = child.kill();
        let _ = child.wait();
        assert!(result.unwrap().complete);
        assert!(activity.unwrap().blocked(&project).is_some());
        let candidate = final_row.unwrap();
        assert!(!candidate.eligible_permanent);
        assert!(!candidate.suggestion_eligible);
        assert!(
            candidate
                .blocked_reason
                .unwrap()
                .contains("running process")
        );
    }

    #[test]
    fn newly_tracked_content_is_rechecked_before_mutation() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 8);
        let (_, rows) = candidates(&root);
        let candidate = &rows[0];
        assert!(candidate.blocked_reason.is_none());
        assert!(
            Command::new("/usr/bin/git")
                .args(["init", "-q"])
                .arg(&project)
                .status()
                .unwrap()
                .success()
        );
        assert!(
            Command::new("/usr/bin/git")
                .arg("-C")
                .arg(&project)
                .args(["add", "node_modules/payload"])
                .status()
                .unwrap()
                .success()
        );
        let reason = revalidate(&root, candidate, &AtomicBool::new(false)).unwrap_err();
        assert!(reason.contains("tracks"), "{reason}");
        assert_eq!(
            std::fs::read(project.join("node_modules/payload")).unwrap(),
            [7u8; 4096]
        );
    }

    #[test]
    fn recommendation_cutoffs_use_allocated_bytes_and_latest_activity() {
        let now = 100 * DAY_NS;
        let cutoff = now - DEVELOPER_QUIET_DAYS * DAY_NS;
        assert!(quiet_for(cutoff, now, DEVELOPER_QUIET_DAYS));
        assert!(!quiet_for(cutoff + 1, now, DEVELOPER_QUIET_DAYS));
        assert!(!quiet_for(now + DAY_NS, now, DEVELOPER_QUIET_DAYS));
        let mut measured = Measurement {
            allocated_bytes: LARGE_FILE_BYTES,
            logical_bytes: LARGE_FILE_BYTES,
            latest_modified_ns: now - 7 * DAY_NS,
            ..Measurement::default()
        };
        let mut found = policy_evidence("node", 7);
        assert!(suggestion_reason(&found, &measured, now).is_none());
        measured.allocated_bytes = LARGE_FILE_BYTES - 1;
        assert!(
            suggestion_reason(&found, &measured, now)
                .unwrap()
                .contains("100 MB")
        );
        measured.logical_bytes = 1_000_000_000_000;
        measured.allocated_bytes = 0;
        assert!(
            suggestion_reason(&found, &measured, now).is_some(),
            "Sparse logical length is not an opportunity"
        );
        measured.allocated_bytes = LARGE_FILE_BYTES;
        measured.latest_modified_ns += 1;
        assert!(
            suggestion_reason(&found, &measured, now)
                .unwrap()
                .contains("quiet")
        );
        measured.latest_modified_ns = now - 8 * DAY_NS;
        found.latest_modified_ns = now - DAY_NS;
        assert!(
            suggestion_reason(&found, &measured, now).is_some(),
            "A recently edited manifest keeps the project active"
        );
        found.latest_modified_ns = now + DAY_NS;
        assert!(
            suggestion_reason(&found, &measured, now).is_some(),
            "Future timestamps are not quiet"
        );
        for days in [INSTALLER_QUIET_DAYS, DOWNLOAD_QUIET_DAYS] {
            let found = policy_evidence("download", days);
            measured.latest_modified_ns = now - days * DAY_NS;
            assert!(suggestion_reason(&found, &measured, now).is_none());
            measured.latest_modified_ns += 1;
            assert!(suggestion_reason(&found, &measured, now).is_some());
        }
        for kind in [
            "cache",
            "log",
            "crashreport",
            "xcode",
            "installer",
            "archive",
            "largefile",
        ] {
            let days = recommendations::quiet_days(kind);
            let found = policy_evidence(kind, days);
            measured.allocated_bytes = recommendations::minimum_bytes(kind);
            measured.latest_modified_ns = now - days * DAY_NS;
            assert!(
                suggestion_reason(&found, &measured, now).is_none(),
                "{kind}"
            );
            measured.allocated_bytes -= 1;
            assert!(
                suggestion_reason(&found, &measured, now).is_some(),
                "{kind}"
            );
            measured.allocated_bytes += 1;
            measured.latest_modified_ns += 1;
            assert!(
                suggestion_reason(&found, &measured, now).is_some(),
                "{kind}"
            );
        }
    }

    #[test]
    fn a_recent_descendant_blocks_an_old_artifact_root() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 9);
        let artifact = project.join("node_modules");
        std::fs::File::open(artifact.join("payload"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let mut measured =
            safety::measure(&artifact, root.identity.device, &AtomicBool::new(false)).unwrap();
        assert!(measured.latest_modified_ns > safety::identity(&artifact).unwrap().modified_ns);
        measured.allocated_bytes = LARGE_FILE_BYTES; // Isolate age policy from this small safety fixture.
        let found = node_evidence(&root, &project, &AtomicBool::new(false))
            .unwrap()
            .unwrap();
        assert!(
            suggestion_reason(&found, &measured, clock_ns())
                .unwrap()
                .contains("quiet")
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn recent_file_hint_excludes_only_suggestion_measurement() {
        let (_temp, root, project) = fixture();
        let artifact = project.join("node_modules");
        let leaf = artifact.join("deep/nested/changed");
        std::fs::create_dir_all(leaf.parent().unwrap()).unwrap();
        std::fs::write(&leaf, b"disposable output").unwrap();
        age_tree(&project, 9);
        std::fs::File::open(&leaf)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let mut hints = RecentFileHints::default();
        hints.remember(&root, &artifact, &leaf);
        let mut last = None;
        let suggested = scan_with_options(
            &root,
            Some(&artifact),
            &[],
            &AtomicBool::new(false),
            ScanOptions {
                mode: ScanMode::Suggestions,
                recent_files: Some(&mut hints),
            },
            || {},
            |batch| {
                for candidate in batch.candidates {
                    last = Some(candidate);
                }
            },
        )
        .unwrap();
        assert!(suggested.complete && !suggested.cancelled);
        assert_eq!(
            (suggested.entries, suggested.errors, suggested.candidates),
            (1, 0, 0)
        );
        assert_eq!(suggested.excluded_artifacts, 1);
        let diagnostic = last.unwrap();
        assert!(
            !diagnostic.provisional
                && !diagnostic.suggestion_eligible
                && !diagnostic.eligible_permanent
        );
        assert_eq!(
            (
                diagnostic.file_count,
                diagnostic.allocated_bytes,
                diagnostic.logical_bytes
            ),
            (0, 0, 0)
        );
        assert!(diagnostic.fingerprint.is_empty());
        assert!(diagnostic.blocked_reason.unwrap().contains("quiet days"));
        assert!(diagnostic.explanation.contains("not traversed or measured"));
        assert_eq!(diagnostic.identity, safety::identity(&artifact).unwrap());
        let covered = scan_with_options(
            &root,
            Some(&artifact),
            &[],
            &AtomicBool::new(false),
            ScanOptions {
                mode: ScanMode::MetadataCoverage,
                recent_files: Some(&mut hints),
            },
            || {},
            |_| {},
        )
        .unwrap();
        assert!(covered.complete);
        assert_eq!((covered.entries, covered.files, covered.errors), (5, 2, 0));
        hints.clear();
        scan_with_options(
            &root,
            None,
            &[],
            &AtomicBool::new(false),
            ScanOptions {
                mode: ScanMode::MetadataCoverage,
                recent_files: Some(&mut hints),
            },
            || {},
            |_| {},
        )
        .unwrap();
        assert!(hints.get(&root.id, &artifact).is_none());
        assert_eq!(std::fs::read(&leaf).unwrap(), b"disposable output");
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn invalid_hints_fall_back_but_kept_descendants_exclude_the_artifact() {
        let (_temp, root, project) = fixture();
        age_tree(&project, 9);
        let artifact = project.join("node_modules");
        let leaf = artifact.join("payload");
        let run = |hint: Option<&Path>, kept: &[PathBuf]| {
            let mut hints = RecentFileHints::default();
            if let Some(path) = hint {
                hints.remember(&root, &artifact, path);
            }
            let mut rows = Vec::new();
            let stats = scan_with_options(
                &root,
                Some(&artifact),
                kept,
                &AtomicBool::new(false),
                ScanOptions {
                    mode: ScanMode::Suggestions,
                    recent_files: Some(&mut hints),
                },
                || {},
                |batch| rows.extend(batch.candidates),
            )
            .unwrap();
            (stats, rows.pop())
        };
        let (expected, row) = run(None, &[]);
        assert!(row.is_some());
        for hint in [
            &leaf,
            &artifact.join("absent"),
            &project.join("package.json"),
            &artifact,
        ] {
            let (stats, actual) = run(Some(hint), &[]);
            assert_eq!(actual, row);
            assert_eq!(
                (stats.entries, stats.files, stats.errors),
                (expected.entries, expected.files, expected.errors)
            );
        }
        std::fs::File::open(&leaf)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let kept = [leaf.clone()];
        let (expected, row) = run(None, &kept);
        let (actual, hinted) = run(Some(&leaf), &kept);
        assert_eq!(hinted, row);
        assert!(
            row.is_none(),
            "A kept descendant excludes its whole artifact"
        );
        assert_eq!(actual.entries, expected.entries);
        assert_eq!(actual.entries, 1, "The kept artifact must not be measured");
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn learned_recent_hints_skip_full_and_parent_repeats_without_changing_suggestions() {
        let (_temp, root, _project, expected) = eligible_revalidation_fixture();
        let active = root.path.join("active");
        let artifact = active.join("node_modules");
        let deep = artifact.join("deep");
        std::fs::create_dir_all(&deep).unwrap();
        std::fs::write(active.join("package.json"), br#"{"name":"active"}"#).unwrap();
        std::fs::write(
            active.join("package-lock.json"),
            br#"{"lockfileVersion":3,"packages":{}}"#,
        )
        .unwrap();
        let leaf = deep.join("recent");
        std::fs::write(&leaf, b"preserve this active output").unwrap();
        age_tree(&active, 9);
        std::fs::File::open(&leaf)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let run = |scope, hints: &mut RecentFileHints| {
            let mut rows = std::collections::BTreeMap::new();
            let stats = scan_with_options(
                &root,
                scope,
                &[],
                &AtomicBool::new(false),
                ScanOptions {
                    mode: ScanMode::Suggestions,
                    recent_files: Some(hints),
                },
                || {},
                |batch| {
                    for row in batch.candidates {
                        rows.insert(row.path.clone(), row);
                    }
                },
            )
            .unwrap();
            assert!(stats.complete && !stats.cancelled && stats.errors == 0);
            (stats, rows)
        };
        let mut hints = RecentFileHints::default();
        let (first, before) = run(None, &mut hints);
        assert_eq!(hints.get(&root.id, &artifact), Some(leaf.as_path()));
        let (second, after) = run(None, &mut hints);
        assert!(second.entries < first.entries);
        assert_eq!(before.get(&expected.path), Some(&expected));
        assert_eq!(after.get(&expected.path), Some(&expected));
        assert_eq!((first.candidates, second.candidates), (1, 1));
        assert!(!after[&artifact].suggestion_eligible);
        assert!(after[&artifact].fingerprint.is_empty());

        let (ordinary, _) = run(Some(active.as_path()), &mut RecentFileHints::default());
        let (parent, rows) = run(Some(active.as_path()), &mut hints);
        assert!(parent.entries < ordinary.entries);
        assert_eq!(rows[&artifact].file_count, 0);
        assert_eq!(
            std::fs::read(&leaf).unwrap(),
            b"preserve this active output"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn unsafe_recent_hints_fall_back_without_learning() {
        for linked in [false, true] {
            let (_temp, root, project) = fixture();
            let artifact = project.join("node_modules");
            let leaf = artifact.join("payload");
            let preserved = project.join("preserved");
            if linked {
                std::fs::hard_link(&leaf, &preserved).unwrap();
            } else {
                std::fs::rename(&leaf, &preserved).unwrap();
                symlink("../preserved", &leaf).unwrap();
            }
            age_tree(&project, 9);
            std::fs::write(&preserved, b"preserve this active output").unwrap();
            let mut hints = RecentFileHints::default();
            hints.remember(&root, &artifact, &leaf);
            let mut rows = Vec::new();
            let stats = scan_with_options(
                &root,
                Some(&artifact),
                &[],
                &AtomicBool::new(false),
                ScanOptions {
                    mode: ScanMode::Suggestions,
                    recent_files: Some(&mut hints),
                },
                || {},
                |batch| rows.extend(batch.candidates),
            )
            .unwrap();
            assert!(stats.complete && stats.entries > 1);
            assert!(hints.get(&root.id, &artifact).is_none());
            assert!(!rows.last().unwrap().suggestion_eligible);
            assert_eq!(
                std::fs::read(&preserved).unwrap(),
                b"preserve this active output"
            );
        }
    }

    #[test]
    fn recent_file_proof_requires_an_owned_single_link_regular_leaf_above_cutoff() {
        let (_temp, root, project) = fixture();
        let artifact = project.join("node_modules");
        let leaf = artifact.join("payload");
        let entry = Entry {
            meta: safety::metadata(&artifact).unwrap(),
            path: artifact,
        };
        let modified = safety::identity(&leaf).unwrap().modified_ns;
        let cancel = AtomicBool::new(false);
        assert_eq!(
            recent_file_modified(&root, &entry, &leaf, &cancel, &|| {}, modified).unwrap(),
            None
        );
        assert_eq!(
            recent_file_modified(&root, &entry, &leaf, &cancel, &|| {}, modified - 1).unwrap(),
            Some(modified)
        );
        std::fs::hard_link(&leaf, project.join("shared-copy")).unwrap();
        assert_eq!(
            recent_file_modified(&root, &entry, &leaf, &cancel, &|| {}, modified - 1).unwrap(),
            None
        );
        cancel.store(true, std::sync::atomic::Ordering::Release);
        assert!(recent_file_modified(&root, &entry, &leaf, &cancel, &|| {}, modified - 1).is_err());
    }

    #[test]
    fn a_downloads_child_in_a_generic_folder_keeps_personal_file_rules() {
        let (_temp, mut root, _) = fixture();
        root.kind = "folder".into();
        let downloads = root.path.join("Downloads");
        std::fs::create_dir(&downloads).unwrap();
        for (name, size, folder_kind, home_kind) in [
            ("data.bin", 100_000_000, None, "download"),
            ("archive.zip", 50_000_000, None, "archive"),
            ("recording.MOV", 500_000_000, Some("largefile"), "download"),
        ] {
            let path = downloads.join(name);
            std::fs::File::create(&path).unwrap().set_len(size).unwrap();
            let meta = safety::metadata(&path).unwrap();
            root.kind = "folder".into();
            assert_eq!(
                evidence(&root, &path, &meta, &AtomicBool::new(false))
                    .unwrap()
                    .map(|e| e.kind),
                folder_kind
            );
            assert!(!in_downloads(&root, &path));
            root.kind = "home".into();
            assert_eq!(
                evidence(&root, &path, &meta, &AtomicBool::new(false))
                    .unwrap()
                    .unwrap()
                    .kind,
                home_kind
            );
        }
    }

    #[test]
    fn small_personal_files_and_unfinished_downloads_are_not_suggestions() {
        let (_temp, mut root, project) = fixture();
        root.kind = "home".into();
        let documents = root.path.join("Documents");
        let downloads = root.path.join("Downloads");
        std::fs::create_dir(&documents).unwrap();
        std::fs::create_dir_all(downloads.join("unfinished.download")).unwrap();
        for path in [
            documents.join("important.pdf"),
            project.join("personal.dmg"),
            downloads.join("review.dmg"),
            downloads.join("incomplete.crdownload"),
            downloads.join("unfinished.download/payload.dmg"),
        ] {
            std::fs::File::create(path)
                .unwrap()
                .set_len(LARGE_FILE_BYTES)
                .unwrap();
        }
        for (name, bytes) in [
            ("below-floor.pdf", 499_999_999),
            ("at-floor.pdf", 500_000_000),
        ] {
            std::fs::File::create(documents.join(name))
                .unwrap()
                .set_len(bytes)
                .unwrap();
        }
        let (stats, rows) = candidates(&root);
        let personal_rows: Vec<_> = rows.iter().filter(|row| row.kind == "largefile").collect();
        assert_eq!(personal_rows.len(), 1);
        assert_eq!(personal_rows[0].path, documents.join("at-floor.pdf"));
        let downloads_rows: Vec<_> = rows.iter().filter(|row| row.kind == "installer").collect();
        assert_eq!(downloads_rows.len(), 1);
        assert_eq!(downloads_rows[0].path, downloads.join("review.dmg"));
        assert!(
            !downloads_rows[0].suggestion_eligible,
            "A sparse fresh image must remain diagnostic"
        );
        assert!(rows.iter().all(|row| !row.suggestion_eligible));
        assert_eq!(stats.candidates, 0);
        assert!(stats.skipped >= 3);
        assert!(std::fs::metadata(documents.join("important.pdf")).is_ok());
        assert!(!in_downloads(
            &root,
            &root.path.join("Other/Downloads/file.pkg")
        ));
        assert!(!in_downloads(
            &root,
            &root.path.join("Downloads-old/file.pkg")
        ));
    }

    #[test]
    fn home_discovery_excludes_media_but_retains_projects_and_downloads() {
        let (_temp, mut root, project) = fixture();
        root.kind = "home".into();
        let nested_project = root.path.join("Projects/Music");
        std::fs::create_dir(nested_project.parent().unwrap()).unwrap();
        std::fs::rename(project, &nested_project).unwrap();
        age_tree(&nested_project, 8);
        for name in ["Music", "Pictures", "Movies"] {
            let media = root.path.join(name);
            std::fs::create_dir_all(media.join("node_modules")).unwrap();
            std::fs::write(media.join("package.json"), br#"{"name":"personal-media"}"#).unwrap();
            std::fs::write(
                media.join("package-lock.json"),
                br#"{"lockfileVersion":3,"packages":{}}"#,
            )
            .unwrap();
            std::fs::write(media.join("node_modules/preserve"), b"personal media").unwrap();
        }
        let downloads = root.path.join("Downloads");
        std::fs::create_dir(&downloads).unwrap();
        let download = downloads.join("review.dmg");
        std::fs::File::create(&download)
            .unwrap()
            .set_len(LARGE_FILE_BYTES)
            .unwrap();
        let (stats, rows) = candidates(&root);
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.errors, 0);
        assert!(
            rows.iter()
                .all(|row| !safety::excluded_home_media(&root, &row.path))
        );
        let artifact = rows
            .iter()
            .find(|row| row.path == nested_project.join("node_modules"))
            .expect("A project named Music must remain discoverable");
        assert!(
            rows.iter()
                .any(|row| row.path == download && row.kind == "installer")
        );
        let mut stale = artifact.clone();
        stale.path = root.path.join("Music/node_modules");
        let error = revalidate(&root, &stale, &AtomicBool::new(false)).unwrap_err();
        assert!(error.contains("Personal media"), "{error}");
        for name in ["Music", "Pictures", "Movies"] {
            assert_eq!(
                std::fs::read(root.path.join(name).join("node_modules/preserve")).unwrap(),
                b"personal media"
            );
        }
        assert!(!in_downloads(
            &root,
            &root.path.join("Projects/Downloads/file.dmg")
        ));
        assert!(!safety::excluded_home_media(
            &root,
            &root.path.join("Music-project/target")
        ));
    }

    #[test]
    fn keep_excludes_the_whole_artifact_before_measurement() {
        use std::os::unix::fs::PermissionsExt;
        let (_temp, root, project) = fixture();
        let kept = [project.join("node_modules")];
        std::fs::set_permissions(&kept[0], std::fs::Permissions::from_mode(0o000)).unwrap();
        let excluded = kept[0].clone();
        let mut rows = Vec::new();
        let scanned = safety::tests::with_directory_read_observer(
            move |path| assert!(!path.starts_with(&excluded)),
            || {
                scan_with_exclusions(&root, None, &kept, &AtomicBool::new(false), |batch| {
                    rows.extend(batch.candidates)
                })
            },
        );
        std::fs::set_permissions(&kept[0], std::fs::Permissions::from_mode(0o700)).unwrap();
        let stats = scanned.unwrap();
        assert!(rows.is_empty());
        assert_eq!(stats.files, 2);
        assert_eq!(stats.skipped, 1);
        assert!(stats.complete);
        assert_eq!(std::fs::read(kept[0].join("payload")).unwrap(), [7u8; 4096]);
    }

    #[test]
    fn newly_recognized_artifacts_containing_keep_are_not_measured() {
        for name in [".venv", ".next"] {
            let (_temp, root, project) = fixture();
            let container = root.path.join("container");
            let artifact = container.join(name);
            let nested = artifact.join("nested");
            let sibling = container.join("sibling");
            std::fs::create_dir_all(nested.join("node_modules")).unwrap();
            std::fs::rename(project, &sibling).unwrap();
            for relative in ["package.json", "package-lock.json", "node_modules/payload"] {
                std::fs::copy(sibling.join(relative), nested.join(relative)).unwrap();
            }
            age_tree(&container, 9);
            let (_, before) = candidates(&root);
            let kept = [before
                .iter()
                .find(|row| row.path == nested.join("node_modules"))
                .expect("An unmarked wrapper must expose its nested artifact")
                .path
                .clone()];

            if name == ".venv" {
                std::fs::write(artifact.join("pyvenv.cfg"), b"home = /usr/local/bin\n").unwrap();
            } else {
                std::fs::copy(sibling.join("package.json"), container.join("package.json"))
                    .unwrap();
            }
            age_tree(&container, 9);

            for mode in [ScanMode::Suggestions, ScanMode::MetadataCoverage] {
                let excluded = artifact.clone();
                let mut rows = std::collections::BTreeMap::new();
                let stats = safety::tests::with_directory_read_observer(
                    move |path| {
                        assert!(
                            !path.starts_with(&excluded),
                            "An artifact containing Keep must not be traversed"
                        );
                    },
                    || {
                        scan_with_checkpoint_mode(
                            &root,
                            None,
                            &kept,
                            &AtomicBool::new(false),
                            mode,
                            || {},
                            |batch| {
                                for row in batch.candidates {
                                    rows.insert(row.id.clone(), row);
                                }
                            },
                        )
                    },
                )
                .unwrap();
                assert!(stats.complete, "{name}: {}", stats.message);
                assert_eq!(
                    rows.len(),
                    1,
                    "Ordinary ancestors must retain their siblings"
                );
                assert_eq!(
                    rows.values().next().unwrap().path,
                    sibling.join("node_modules")
                );
                assert!(rows.values().all(|row| !kept[0].starts_with(&row.path)));
                assert!(stats.excluded_artifacts >= 1);
            }
            assert_eq!(std::fs::read(kept[0].join("payload")).unwrap(), [7u8; 4096]);
        }
    }

    #[test]
    fn suggestion_pruning_never_initializes_excluded_directory_readers() {
        let (_temp, mut root, project) = fixture();
        root.kind = "home".into();
        let artifact = project.join("node_modules");
        let mut excluded = vec![artifact.clone()];
        for name in [
            "Music",
            "Pictures",
            "Movies",
            "Dropbox",
            "Collection.musiclibrary",
        ] {
            let path = root.path.join(name);
            std::fs::create_dir(&path).unwrap();
            std::fs::write(path.join("preserve"), b"personal data").unwrap();
            excluded.push(path);
        }
        let never_read = excluded.clone();
        let (stats, rows) = safety::tests::with_directory_read_observer(
            move |path| {
                assert!(
                    never_read
                        .iter()
                        .all(|excluded| !path.starts_with(excluded))
                )
            },
            || candidates(&root),
        );
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.excluded_artifacts, 1);
        assert!(rows.is_empty());
        for path in &excluded[1..] {
            assert_eq!(
                std::fs::read(path.join("preserve")).unwrap(),
                b"personal data"
            );
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn home_lanes_publish_quick_project_before_huge_cache_finishes() {
        let (_temp, mut root, project) = fixture();
        root.kind = "home".into();
        let mut capacity: libc::statfs = unsafe { std::mem::zeroed() };
        let root_name = CString::new(root.path.as_os_str().as_bytes()).unwrap();
        assert_eq!(
            unsafe { libc::statfs(root_name.as_ptr(), &mut capacity) },
            0
        );
        assert!(
            capacity.f_bavail.saturating_mul(capacity.f_bsize as u64) >= 512 * 1024 * 1024,
            "The disposable lane-fairness test requires a 512 MiB reserve"
        );

        let quick = root.path.join("Projects/quick");
        std::fs::create_dir_all(quick.parent().unwrap()).unwrap();
        std::fs::rename(&project, &quick).unwrap();
        {
            let mut payload = std::fs::File::create(quick.join("node_modules/payload")).unwrap();
            let block = vec![0x31; 1024 * 1024];
            for _ in 0..100 {
                payload.write_all(&block).unwrap();
            }
            payload.sync_all().unwrap();
        }

        let cache = root.path.join("Library/Caches/SlowFixture");
        std::fs::create_dir_all(&cache).unwrap();
        const SLOW_FILES: u64 = 2_048;
        let block = vec![0x52; 28 * 1024];
        for index in 0..SLOW_FILES {
            std::fs::write(cache.join(format!("payload-{index:04}")), &block).unwrap();
        }
        age_tree(&quick, 31);
        age_tree(&cache, 31);

        let cache_reads = Rc::new(std::cell::Cell::new(0u64));
        let observed_reads = cache_reads.clone();
        let cache_for_observer = cache.clone();
        let terminal = Rc::new(std::cell::RefCell::new(Vec::new()));
        let published_terminal = terminal.clone();
        let reads_at_quick = Rc::new(std::cell::Cell::new(None));
        let published_reads_at_quick = reads_at_quick.clone();
        let cache_for_publish = cache.clone();
        let quick_artifact = quick.join("node_modules");
        let quick_for_publish = quick_artifact.clone();
        let stats = safety::tests::with_directory_read_observer(
            move |path| {
                if path == cache_for_observer {
                    observed_reads.set(observed_reads.get() + 1);
                }
            },
            || {
                scan(&root, None, &AtomicBool::new(false), |batch| {
                    for candidate in batch.candidates {
                        if candidate.provisional {
                            continue;
                        }
                        if candidate.path == quick_for_publish {
                            published_reads_at_quick.set(Some(cache_reads.get()));
                        }
                        published_terminal.borrow_mut().push(candidate.path);
                    }
                })
            },
        )
        .unwrap();
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.candidates, 2);
        let terminal = terminal.borrow();
        let quick_index = terminal
            .iter()
            .position(|path| path == &quick_artifact)
            .expect("the quick project must reach terminal eligibility");
        let cache_index = terminal
            .iter()
            .position(|path| path == &cache_for_publish)
            .expect("the cache must reach terminal eligibility");
        assert!(quick_index < cache_index, "terminal order was {terminal:?}");
        let reads = reads_at_quick
            .get()
            .expect("the quick result must observe the in-progress cache cursor");
        assert!(
            reads > 0 && reads < SLOW_FILES,
            "the quick result arrived after {reads} of {SLOW_FILES} cache reads"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn aged_allocated_artifact_is_useful_before_deep_coverage_finishes_and_rechecks_activity() {
        let (_temp, root, project) = fixture();
        let mut statfs: libc::statfs = unsafe { std::mem::zeroed() };
        let root_name = std::ffi::CString::new(root.path.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::statfs(root_name.as_ptr(), &mut statfs) }, 0);
        assert!(
            (statfs.f_bavail as u64).saturating_mul(statfs.f_bsize as u64)
                >= 3 * 1024 * 1024 * 1024 + LARGE_FILE_BYTES,
            "The disposable allocated-file test requires a 3 GiB reserve"
        );
        let artifact = project.join("node_modules");
        let payload = artifact.join("payload");
        {
            let mut file = std::fs::File::create(&payload).unwrap();
            let chunk = vec![0x5au8; 1024 * 1024];
            let mut remaining = LARGE_FILE_BYTES;
            while remaining > 0 {
                let count = remaining.min(chunk.len() as u64) as usize;
                file.write_all(&chunk[..count]).unwrap();
                remaining -= count as u64;
            }
            file.sync_all().unwrap();
        }
        age_tree(&project, 9);
        // This fresh artifact is one level shallower than the useful project,
        // so eager measurement would consume all its payload metadata first.
        let fresh = root.path.join("node_modules");
        std::fs::create_dir(&fresh).unwrap();
        std::fs::write(
            root.path.join("package.json"),
            br#"{"name":"fresh-fixture"}"#,
        )
        .unwrap();
        std::fs::write(
            root.path.join("package-lock.json"),
            br#"{"lockfileVersion":3,"packages":{}}"#,
        )
        .unwrap();
        const FRESH_FILES: u64 = 2048;
        for index in 0..FRESH_FILES {
            std::fs::write(fresh.join(format!("payload-{index}")), [3u8; 1024]).unwrap();
        }
        let mut deep = root.path.join("unrelated");
        for _ in 0..40 {
            std::fs::create_dir(&deep).unwrap();
            std::fs::write(deep.join("small"), b"x").unwrap();
            deep = deep.join("nested");
        }
        let mut first_useful_entries = None;
        let mut suggestion = None;
        let stats = scan(&root, None, &AtomicBool::new(false), |batch| {
            for candidate in batch.candidates {
                if candidate.suggestion_eligible {
                    assert!(candidate.blocked_reason.is_none());
                    assert!(candidate.allocated_bytes >= LARGE_FILE_BYTES);
                    assert!(!candidate.fingerprint.is_empty());
                    first_useful_entries.get_or_insert(batch.stats.entries);
                    suggestion = Some(candidate);
                }
            }
        })
        .unwrap();
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.candidates, 1);
        assert!(stats.first_finding_ms.is_some());
        assert_eq!(stats.excluded_artifacts, 1);
        assert!(
            stats.entries < FRESH_FILES,
            "Interactive discovery must not enumerate the excluded fresh artifact"
        );
        assert!(
            first_useful_entries.unwrap() < stats.entries,
            "Shallow recommendations should precede the deep unrelated branch"
        );
        assert!(
            first_useful_entries.unwrap() < FRESH_FILES,
            "The shallower fresh artifact must not delay useful findings"
        );
        let candidate =
            suggestion.expect("An old, allocated, idle 100 MB artifact must be suggested");
        assert!(candidate.eligible_permanent);
        revalidate(&root, &candidate, &AtomicBool::new(false)).unwrap();
        std::fs::File::open(&payload)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let error = revalidate(&root, &candidate, &AtomicBool::new(false)).unwrap_err();
        assert!(error.contains("quiet"), "{error}");
        assert_eq!(std::fs::metadata(payload).unwrap().len(), LARGE_FILE_BYTES);
    }

    /// Date the symbolic link itself, never its target.
    fn date_symlink(path: &Path, days: u64) {
        let old = SystemTime::now() - Duration::from_secs(days * 86_400);
        let seconds = old.duration_since(UNIX_EPOCH).unwrap().as_secs() as i64;
        let encoded = CString::new(path.as_os_str().as_bytes()).unwrap();
        let times = [libc::timespec {
            tv_sec: seconds,
            tv_nsec: 0,
        }; 2];
        assert_eq!(
            unsafe {
                libc::utimensat(
                    libc::AT_FDCWD,
                    encoded.as_ptr(),
                    times.as_ptr(),
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            },
            0
        );
    }

    fn venv_fixture() -> (tempfile::TempDir, Root, PathBuf, PathBuf) {
        let temp = tempfile::tempdir().unwrap();
        let base = std::fs::canonicalize(temp.path()).unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        let project = base.join("api");
        let venv = project.join(".venv");
        std::fs::create_dir_all(venv.join("lib")).unwrap();
        std::fs::write(venv.join("lib/payload"), [9u8; 4096]).unwrap();
        (temp, root, project, venv)
    }

    #[test]
    fn venv_recognition_requires_a_direct_regular_pyvenv_cfg() {
        let (_temp, _root, project, venv) = venv_fixture();
        let cancel = AtomicBool::new(false);
        // No marker: not an artifact and not a diagnostic.
        assert!(
            venv_evidence(&project, &venv, &cancel, None)
                .unwrap()
                .is_none()
        );
        // A marker reachable only through a link is not positive recognition.
        std::fs::write(project.join("shared-config"), b"home = /usr/local/bin\n").unwrap();
        symlink(project.join("shared-config"), venv.join("pyvenv.cfg")).unwrap();
        assert!(
            venv_evidence(&project, &venv, &cancel, None)
                .unwrap()
                .is_none()
        );
        std::fs::remove_file(venv.join("pyvenv.cfg")).unwrap();
        std::fs::write(
            venv.join("pyvenv.cfg"),
            b"home = /usr/local/bin\nversion = 3.12.1\n",
        )
        .unwrap();
        let first = venv_evidence(&project, &venv, &cancel, None)
            .unwrap()
            .unwrap();
        assert_eq!(first.kind, "venv");
        assert_eq!(first.title, "api Python environment");
        assert_eq!(first.quiet_days, DEVELOPER_QUIET_DAYS);
        assert_eq!(first.activity_root.as_deref(), Some(project.as_path()));
        assert!(first.blocked.is_none());
        // A changed configuration invalidates the reviewed evidence.
        std::fs::write(
            venv.join("pyvenv.cfg"),
            b"home = /opt/python/bin\nversion = 3.13.0\n",
        )
        .unwrap();
        let changed = venv_evidence(&project, &venv, &cancel, None)
            .unwrap()
            .unwrap();
        assert_ne!(first.fingerprint, changed.fingerprint);
    }

    #[test]
    fn venv_dispatch_covers_both_spellings_but_not_lookalikes() {
        let (_temp, root, project, _venv) = venv_fixture();
        let cancel = AtomicBool::new(false);
        for name in ["venv", "virtualenv"] {
            let directory = project.join(name);
            std::fs::create_dir(&directory).unwrap();
            std::fs::write(directory.join("pyvenv.cfg"), b"home = /usr/local/bin\n").unwrap();
            let meta = safety::metadata(&directory).unwrap();
            let found = evidence(&root, &directory, &meta, &cancel).unwrap();
            if name == "venv" {
                assert_eq!(found.unwrap().kind, "venv");
            } else {
                assert!(found.is_none(), "Lookalike names are never artifacts");
            }
        }
    }

    #[test]
    fn tracked_descendant_disqualifies_a_python_environment() {
        let (_temp, root, project, venv) = venv_fixture();
        std::fs::write(venv.join("pyvenv.cfg"), b"home = /usr/local/bin\n").unwrap();
        fixture_git(&project, &["init", "--quiet"]);
        fixture_git(&project, &["add", "--", ".venv/lib/payload"]);
        let reason = git_untracked(&root, &project, &venv, &AtomicBool::new(false)).unwrap_err();
        assert!(reason.contains("tracks"), "{reason}");
        assert_eq!(
            std::fs::read(venv.join("lib/payload")).unwrap(),
            [9u8; 4096]
        );
    }

    #[test]
    fn unmarked_venv_directory_stays_ordinary_and_traversed() {
        let (_temp, root, project, venv) = venv_fixture();
        age_tree(&project, 8);
        let (stats, rows) = candidates(&root);
        assert!(stats.complete, "{}", stats.message);
        assert!(rows.is_empty());
        assert_eq!(stats.excluded_artifacts, 0);
        assert_eq!(stats.files, 1, "The unrecognized contents remain covered");
        assert!(stats.entries >= 4);
        assert_eq!(
            std::fs::read(venv.join("lib/payload")).unwrap(),
            [9u8; 4096]
        );

        // With its marker the same quiet directory becomes a completed
        // diagnostic row; this tiny fixture is still below the size policy.
        std::fs::write(venv.join("pyvenv.cfg"), b"home = /usr/local/bin\n").unwrap();
        age_tree(&project, 8);
        let (marked, rows) = candidates(&root);
        assert!(marked.complete, "{}", marked.message);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].kind, "venv");
        assert_eq!(rows[0].path, venv);
        assert!(rows[0].blocked_reason.is_none());
        assert!(!rows[0].suggestion_eligible && !rows[0].eligible_permanent);
    }

    #[test]
    fn recent_unmarked_conditional_directories_still_discover_nested_projects() {
        for name in [".venv", "venv", ".next", ".nuxt", ".turbo", ".parcel-cache"] {
            let (_temp, root, project) = fixture();
            let ordinary = root.path.join(name);
            let nested = ordinary.join("project");
            std::fs::create_dir(&ordinary).unwrap();
            std::fs::rename(project, &nested).unwrap();
            age_tree(&ordinary, 9);
            std::fs::File::open(&ordinary)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
                .unwrap();

            let (stats, rows) = candidates(&root);
            assert!(stats.complete, "{name}: {}", stats.message);
            assert_eq!(
                rows.len(),
                1,
                "A fresh unmarked {name} must remain ordinary"
            );
            assert_eq!(rows[0].path, nested.join("node_modules"));
            assert_eq!(rows[0].kind, "node");
        }
    }

    #[test]
    fn recent_venv_boundary_is_pruned_without_reading_its_contents() {
        let (_temp, root, project, venv) = venv_fixture();
        std::fs::write(venv.join("pyvenv.cfg"), b"home = /usr/local/bin\n").unwrap();
        age_tree(&project, 8);
        // Only the boundary is fresh; its marker identifies it without a walk.
        std::fs::File::open(&venv)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(SystemTime::now()))
            .unwrap();
        let excluded = venv.clone();
        let (stats, rows) = safety::tests::with_directory_read_observer(
            move |path| assert!(!path.starts_with(&excluded)),
            || candidates(&root),
        );
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(stats.excluded_artifacts, 1);
        assert!(rows.is_empty());
        assert_eq!(
            std::fs::read(venv.join("lib/payload")).unwrap(),
            [9u8; 4096]
        );
    }

    #[test]
    fn webcache_requires_a_sibling_manifest_and_distinguishes_cache_directories() {
        let temp = tempfile::tempdir().unwrap();
        let base = std::fs::canonicalize(temp.path()).unwrap();
        let _root = safety::authorize(&base, "projects").unwrap();
        let project = base.join("site");
        let names = [".next", ".nuxt", ".turbo", ".parcel-cache"];
        for name in names {
            std::fs::create_dir_all(project.join(name)).unwrap();
            std::fs::write(project.join(name).join("payload"), [4u8; 1024]).unwrap();
        }
        let cancel = AtomicBool::new(false);
        for name in names {
            assert!(
                webcache_evidence(&project, &project.join(name), &cancel, None)
                    .unwrap()
                    .is_none(),
                "{name} without a sibling manifest stays an ordinary folder"
            );
        }
        std::fs::write(project.join("package.json"), br#"{"name":"site"}"#).unwrap();
        let mut fingerprints = std::collections::BTreeSet::new();
        for name in names {
            let found = webcache_evidence(&project, &project.join(name), &cancel, None)
                .unwrap()
                .unwrap();
            assert_eq!(found.kind, "webcache");
            assert_eq!(found.title, "site build cache");
            assert!(found.explanation.contains(name), "{}", found.explanation);
            assert_eq!(found.quiet_days, DEVELOPER_QUIET_DAYS);
            assert_eq!(found.activity_root.as_deref(), Some(project.as_path()));
            assert!(found.blocked.is_none());
            fingerprints.insert(found.fingerprint);
        }
        assert_eq!(
            fingerprints.len(),
            names.len(),
            "Sibling caches sharing one manifest keep distinct evidence"
        );
        // A manifest reachable only through a link is not positive recognition.
        let manifest = project.join("package.json");
        std::fs::rename(&manifest, project.join("real-manifest")).unwrap();
        symlink(project.join("real-manifest"), &manifest).unwrap();
        assert!(
            webcache_evidence(&project, &project.join(".next"), &cancel, None)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn web_caches_scan_only_beside_their_manifest() {
        let temp = tempfile::tempdir().unwrap();
        let base = std::fs::canonicalize(temp.path()).unwrap();
        let root = safety::authorize(&base, "projects").unwrap();
        let with = base.join("with-manifest");
        let without = base.join("no-manifest");
        for project in [&with, &without] {
            std::fs::create_dir_all(project.join(".next/cache")).unwrap();
            std::fs::write(project.join(".next/cache/payload"), [6u8; 2048]).unwrap();
        }
        std::fs::write(with.join("package.json"), br#"{"name":"site"}"#).unwrap();
        age_tree(&base, 8);
        let (stats, rows) = candidates(&root);
        assert!(stats.complete, "{}", stats.message);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].path, with.join(".next"));
        assert_eq!(rows[0].kind, "webcache");
        assert_eq!(rows[0].title, "with-manifest build cache");
        assert!(rows[0].blocked_reason.is_none());
        assert!(
            !rows[0].suggestion_eligible,
            "Tiny fixtures remain diagnostic"
        );
        // The manifest and both payloads are ordinary coverage; the cache
        // without a manifest was traversed rather than excluded.
        assert!(stats.files >= 2);
        assert_eq!(
            std::fs::read(without.join(".next/cache/payload")).unwrap(),
            [6u8; 2048]
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn aged_allocated_venv_with_internal_symlink_is_suggested_and_revalidates() {
        let (_temp, root, project, venv) = venv_fixture();
        let path = CString::new(root.path.as_os_str().as_bytes()).unwrap();
        let mut capacity: libc::statfs = unsafe { std::mem::zeroed() };
        assert_eq!(unsafe { libc::statfs(path.as_ptr(), &mut capacity) }, 0);
        assert!(
            capacity.f_bavail.saturating_mul(capacity.f_bsize as u64)
                >= 3 * 1024 * 1024 * 1024 + LARGE_FILE_BYTES,
            "The disposable allocated-file test requires a 3 GiB reserve"
        );
        std::fs::write(
            venv.join("pyvenv.cfg"),
            b"home = /usr/local/bin\nversion = 3.12.1\n",
        )
        .unwrap();
        std::fs::create_dir(venv.join("bin")).unwrap();
        let interpreter = project.join("interpreter");
        std::fs::write(&interpreter, b"preserve the linked interpreter").unwrap();
        {
            let mut payload = std::fs::File::create(venv.join("lib/payload")).unwrap();
            let block = vec![0x2eu8; 1024 * 1024];
            let mut remaining = LARGE_FILE_BYTES;
            while remaining > 0 {
                let size = remaining.min(block.len() as u64) as usize;
                payload.write_all(&block[..size]).unwrap();
                remaining -= size as u64;
            }
            payload.sync_all().unwrap();
        }
        age_tree(&project, 9);
        // Environments carry internal links such as bin/python. Add one after
        // aging (aging follows links), then date the link and its parents.
        let link = venv.join("bin/python");
        symlink("../../interpreter", &link).unwrap();
        date_symlink(&link, 9);
        age_tree(&venv.join("bin"), 9);
        age_tree(&venv.join("pyvenv.cfg"), 9);
        std::fs::File::open(&venv)
            .unwrap()
            .set_times(
                std::fs::FileTimes::new()
                    .set_modified(SystemTime::now() - Duration::from_secs(9 * 86_400)),
            )
            .unwrap();
        let (stats, rows) = candidates(&root);
        assert!(stats.complete, "{}", stats.message);
        let candidate = rows
            .iter()
            .find(|row| row.path == venv)
            .expect("The aged, allocated environment must be discovered");
        assert!(candidate.suggestion_eligible, "{candidate:?}");
        assert!(candidate.eligible_permanent);
        assert_eq!(candidate.kind, "venv");
        assert_eq!(candidate.title, "api Python environment");
        assert!(candidate.allocated_bytes >= LARGE_FILE_BYTES);
        revalidate(&root, candidate, &AtomicBool::new(false)).unwrap();
        assert_eq!(
            std::fs::read_link(&link).unwrap(),
            Path::new("../../interpreter")
        );
        assert_eq!(
            std::fs::read(&interpreter).unwrap(),
            b"preserve the linked interpreter"
        );
    }

    #[test]
    fn evidence_content_cache_reuses_unchanged_files_and_rereads_changed_identities() {
        let (_temp, root, project) = fixture();
        let cancel = AtomicBool::new(false);
        let reads = std::rc::Rc::new(std::cell::Cell::new(0usize));
        let counter = std::rc::Rc::clone(&reads);
        safety::tests::with_regular_read_observer(
            move |phase| {
                if phase == safety::tests::RegularReadPhase::BeforeOpen {
                    counter.set(counter.get() + 1);
                }
            },
            || {
                let mut caches = EvidenceCaches::default();
                let fresh = node_evidence(&root, &project, &cancel).unwrap().unwrap();
                let uncached_reads = reads.get();
                assert!(uncached_reads > 0);
                let first = node_evidence_cached(&root, &project, &cancel, Some(&mut caches))
                    .unwrap()
                    .unwrap();
                assert_eq!(reads.get(), 2 * uncached_reads, "A cold cache reads fully");
                let second = node_evidence_cached(&root, &project, &cancel, Some(&mut caches))
                    .unwrap()
                    .unwrap();
                assert_eq!(
                    reads.get(),
                    2 * uncached_reads,
                    "Unchanged identities are served without rereading"
                );
                for cached in [&first, &second] {
                    assert_eq!(cached.fingerprint, fresh.fingerprint);
                    assert_eq!(cached.latest_modified_ns, fresh.latest_modified_ns);
                    assert_eq!(cached.blocked, fresh.blocked);
                    assert_eq!(cached.activity_root, fresh.activity_root);
                }
                // A modified manifest has a new identity and must be reread.
                std::fs::write(
                    project.join("package-lock.json"),
                    br#"{"lockfileVersion":3,"packages":{},"name":"rewritten"}"#,
                )
                .unwrap();
                let changed = node_evidence_cached(&root, &project, &cancel, Some(&mut caches))
                    .unwrap()
                    .unwrap();
                assert!(reads.get() > 2 * uncached_reads);
                assert_ne!(changed.fingerprint, fresh.fingerprint);
                assert_eq!(
                    changed.fingerprint,
                    node_evidence(&root, &project, &cancel)
                        .unwrap()
                        .unwrap()
                        .fingerprint
                );
            },
        );
    }
}
