#![allow(clippy::unnecessary_cast, clippy::nonminimal_bool)]

pub mod accounting;
mod activity;
pub mod cleanup;
mod docker_read;
mod duplicates;
mod editor_review;
mod lock_facts;
mod managed_providers;
pub mod model;
mod probe;
mod project_providers;
mod recommendations;
mod refresh;
pub mod safety;
#[doc(hidden)]
pub mod scan_worker;
pub mod scanner;
pub mod store;

use model::*;
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    ffi::{CStr, CString},
    fs::{File, OpenOptions},
    os::unix::{fs::OpenOptionsExt, io::AsRawFd},
    path::{Path, PathBuf},
    sync::{
        Arc, Condvar, Mutex,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::{Duration, Instant},
};
use store::Store;

#[derive(Clone)]
struct Review {
    operation: String,
    items: Vec<(Root, Candidate)>,
    created: i64,
    cancel_generation: u64,
    duplicate_keeper: Option<duplicates::Input>,
    duplicate_created: Option<Instant>,
}

#[derive(Clone)]
struct DuplicateReportState {
    token: String,
    groups: Vec<(String, duplicates::Group)>,
    created: Instant,
}

#[derive(Default)]
struct DuplicateState {
    generation: u64,
    active_paths: Vec<(String, PathBuf)>,
    report: Option<DuplicateReportState>,
    sql_active: bool,
}

const DUPLICATE_REVIEW_LIFETIME: Duration = Duration::from_secs(120);
struct Runtime {
    stats: ScanStats,
    error: Option<String>,
    scan_mode: scanner::ScanMode,
    foreground: Option<ForegroundRequest>,
    restored_foreground: Option<ForegroundScan>,
    foreground_generation: u64,
    resume_cancelled_worker: bool,
    recent_files: refresh::RecentFileHints,
}

struct ForegroundRoot {
    path: PathBuf,
    started_ms: Option<u64>,
    terminal: bool,
    stats: ScanStats,
}

struct ForegroundRequest {
    generation: u64,
    context: i64,
    summary_attempted: bool,
    started: Instant,
    roots: HashMap<String, ForegroundRoot>,
    snapshot: ForegroundScan,
}

struct ForegroundTicket {
    generation: u64,
    root_id: String,
}

#[cfg(test)]
struct ScopeOutcome {
    stats: ScanStats,
    error: Option<String>,
}

struct IsolatedScope {
    root: Root,
    resolved: PathBuf,
    cargo_lock: bool,
    ticket: Option<ForegroundTicket>,
    refresh: store::ScopeRefresh,
    handle: scan_worker::Handle,
    stats: ScanStats,
    hints_revision: Option<u64>,
    epoch: u64,
    resolved_received: bool,
    started: Instant,
}

fn candidate_in_read_scope(root: &Root, resolved: &Path, cargo_lock: bool, path: &Path) -> bool {
    if path == root.path
        || !path.starts_with(&root.path)
        || path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return false;
    }
    if cargo_lock {
        path == resolved
            || refresh::cargo_lock_target(root, resolved)
                .ok()
                .flatten()
                .is_some_and(|target| path == target)
    } else {
        path.starts_with(resolved)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScanLaunch {
    Background,
    Immediate,
    Explicit,
}

const BACKGROUND_BATCH_DELAY: Duration = Duration::from_millis(600);
const INTERACTIVE_BACKGROUND_BATCH_DELAY: Duration = Duration::from_millis(300);

impl ForegroundRequest {
    fn new(generation: u64, roots: &[Root], context: i64) -> Self {
        let mut request = Self {
            generation,
            context,
            summary_attempted: false,
            started: Instant::now(),
            roots: roots
                .iter()
                .map(|root| {
                    (
                        root.id.clone(),
                        ForegroundRoot {
                            path: root.path.clone(),
                            started_ms: None,
                            terminal: false,
                            stats: ScanStats::default(),
                        },
                    )
                })
                .collect(),
            snapshot: ForegroundScan {
                active: true,
                stats: ScanStats::default(),
            },
        };
        request.rebuild();
        request
    }

    fn elapsed_ms(&self) -> u64 {
        self.started.elapsed().as_millis().min(u64::MAX as u128) as u64
    }

    fn claim(&mut self, id: &str, path: &Path) -> Option<ForegroundTicket> {
        if !self.snapshot.active {
            return None;
        }
        let elapsed = self.elapsed_ms();
        let root = self.roots.get_mut(id)?;
        if root.path != path || root.started_ms.is_some() || root.terminal {
            return None;
        }
        root.started_ms = Some(elapsed);
        Some(ForegroundTicket {
            generation: self.generation,
            root_id: id.into(),
        })
    }

    fn accepts(&self, ticket: &ForegroundTicket) -> bool {
        self.snapshot.active
            && self.generation == ticket.generation
            && self
                .roots
                .get(&ticket.root_id)
                .is_some_and(|root| !root.terminal && root.started_ms.is_some())
    }

    fn progress(&mut self, ticket: &ForegroundTicket, stats: &ScanStats) {
        if self.accepts(ticket) {
            self.roots.get_mut(&ticket.root_id).unwrap().stats = stats.clone();
            self.rebuild();
            if !stats.complete {
                self.snapshot.stats.message = stats.message.clone();
            }
        }
    }

    fn finish(&mut self, ticket: &ForegroundTicket, result: Result<&ScanStats>) {
        if !self.accepts(ticket) {
            return;
        }
        let root = self.roots.get_mut(&ticket.root_id).unwrap();
        match result {
            Ok(stats) => root.stats = stats.clone(),
            Err(error) => {
                root.stats.complete = false;
                root.stats.errors = root.stats.errors.saturating_add(1);
                root.stats.message = error;
            }
        }
        root.terminal = true;
        self.rebuild();
    }

    fn stop(&mut self, cancelled: bool, message: &str) {
        if !self.snapshot.active {
            return;
        }
        self.rebuild();
        self.snapshot.active = false;
        self.snapshot.stats.complete = false;
        self.snapshot.stats.cancelled |= cancelled;
        if !cancelled {
            self.snapshot.stats.errors = self.snapshot.stats.errors.saturating_add(1);
        }
        self.snapshot.stats.message = message.into();
    }

    fn rebuild(&mut self) {
        let mut stats = ScanStats::default();
        let mut first_finding = None;
        let mut cancelled = false;
        let mut complete = true;
        let mut terminal = true;
        for root in self.roots.values() {
            stats = combine_stats(&stats, &root.stats);
            if let (Some(start), Some(found)) = (root.started_ms, root.stats.first_finding_ms) {
                let found = start.saturating_add(found);
                first_finding = Some(first_finding.map_or(found, |prior: u64| prior.min(found)));
            }
            cancelled |= root.stats.cancelled;
            complete &= root.terminal && root.stats.complete;
            terminal &= root.terminal;
        }
        stats.elapsed_ms = self.elapsed_ms();
        stats.first_finding_ms = first_finding;
        stats.cancelled = cancelled;
        stats.complete = complete && !cancelled && stats.errors == 0;
        stats.message = if !terminal {
            "Looking for useful opportunities…"
        } else if stats.complete {
            "Scan complete. Findings are ready to review."
        } else {
            "Scan finished with incomplete coverage. Completed findings are ready to review."
        }
        .into();
        self.snapshot = ForegroundScan {
            active: !terminal,
            stats,
        };
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DiscoveryStage {
    Claimed,
    Began,
    Scanned,
    Finished,
}
#[cfg(test)]
type DiscoveryObserver = Arc<dyn Fn(DiscoveryStage, &str, &Path) + Send + Sync>;
#[derive(Clone, serde::Serialize)]
struct CleanupProgress {
    phase: cleanup::CleanupPhase,
    completed_entries: u64,
    total_entries: u64,
    item_number: usize,
    item_count: usize,
    title: String,
}
pub struct Engine {
    store: Mutex<Store>,
    snapshot_epoch: String,
    runtime: Mutex<Runtime>,
    reviews: Mutex<HashMap<String, Review>>,
    // Progress never takes the SQLite lock held by a cleanup operation.
    cleanup_progress: Mutex<Option<CleanupProgress>>,
    duplicate_state: Mutex<DuplicateState>,
    duplicate_progress: Mutex<Option<duplicates::Progress>>,
    checking_duplicates: AtomicBool,
    duplicate_cancel: AtomicBool,
    managed_review: Mutex<ManagedReviewState>,
    sql_interrupt: rusqlite::InterruptHandle,
    busy: AtomicBool,
    scanning: AtomicBool,
    cleaning: AtomicBool,
    cancel: AtomicBool,
    scan_paused: AtomicBool,
    mutation_cancel: AtomicBool,
    cancel_generation: AtomicU64,
    read_epoch: AtomicU64,
    discovery_urgency: AtomicU64,
    interactive: AtomicBool,
    pause_requested: AtomicBool,
    parked: Mutex<bool>,
    pause_changed: Condvar,
    #[cfg(test)]
    debounce_wait_observer: Mutex<Option<std::sync::mpsc::Sender<Instant>>>,
    #[cfg(test)]
    discovery_observer: Mutex<Option<DiscoveryObserver>>,
    #[cfg(test)]
    scan_helper_fixture: Mutex<Option<PathBuf>>,
    #[cfg(test)]
    review_admission_observer: Mutex<Option<Arc<dyn Fn() + Send + Sync>>>,
    trash: Option<cleanup::TrashCallback>,
    _lock: File,
}

impl Engine {
    pub fn open(path: &Path, trash: Option<cleanup::TrashCallback>) -> Result<Arc<Self>> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(store::err)?;
        }
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path.with_extension("lock"))
            .map_err(store::err)?;
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("This chippytea library is already open in another process.".into());
        }
        let mut store = Store::open(path)?;
        store.reconcile()?;
        // The library is exclusively owned and no reviews exist during open.
        // Keep migration work bounded; admission prevents further growth even
        // when a legacy index needs more than one idle maintenance slice.
        store.maintain_derived(&[])?;
        let stats = store.latest_stats()?;
        let restored_foreground = store.load_foreground_summary()?;
        let sql_interrupt = store.conn.get_interrupt_handle();
        store.conn.execute_batch("CREATE TABLE IF NOT EXISTS event_cursor(id INTEGER PRIMARY KEY CHECK(id=1),cursor INTEGER NOT NULL); INSERT OR IGNORE INTO event_cursor VALUES(1,0);").map_err(store::err)?;
        Ok(Arc::new(Self {
            store: Mutex::new(store),
            snapshot_epoch: unique_id(),
            runtime: Mutex::new(Runtime {
                stats,
                error: None,
                scan_mode: scanner::ScanMode::Suggestions,
                foreground: None,
                restored_foreground,
                foreground_generation: 0,
                resume_cancelled_worker: false,
                recent_files: refresh::RecentFileHints::default(),
            }),
            reviews: Mutex::new(HashMap::new()),
            cleanup_progress: Mutex::new(None),
            duplicate_state: Mutex::new(DuplicateState::default()),
            duplicate_progress: Mutex::new(None),
            checking_duplicates: AtomicBool::new(false),
            duplicate_cancel: AtomicBool::new(false),
            managed_review: Mutex::new(ManagedReviewState::default()),
            sql_interrupt,
            busy: AtomicBool::new(false),
            scanning: AtomicBool::new(false),
            cleaning: AtomicBool::new(false),
            cancel: AtomicBool::new(false),
            scan_paused: AtomicBool::new(false),
            mutation_cancel: AtomicBool::new(false),
            cancel_generation: AtomicU64::new(0),
            read_epoch: AtomicU64::new(0),
            discovery_urgency: AtomicU64::new(0),
            interactive: AtomicBool::new(false),
            pause_requested: AtomicBool::new(false),
            parked: Mutex::new(false),
            pause_changed: Condvar::new(),
            #[cfg(test)]
            debounce_wait_observer: Mutex::new(None),
            #[cfg(test)]
            discovery_observer: Mutex::new(None),
            #[cfg(test)]
            scan_helper_fixture: Mutex::new(None),
            #[cfg(test)]
            review_admission_observer: Mutex::new(None),
            trash,
            _lock: lock,
        }))
    }
    pub fn snapshot(&self) -> Result<Snapshot> {
        self.snapshot_update(None, None)?
            .snapshot
            .ok_or_else(|| "A full snapshot was not returned".into())
    }

    fn snapshot_update(
        &self,
        after_revision: Option<&str>,
        after_content_revision: Option<&str>,
    ) -> Result<SnapshotUpdate> {
        let runtime = self.runtime.lock().map_err(store::err)?;
        // Capture grants and their presentation under the same lock boundary.
        // Release runtime before decoding indexed rows, keeping cancellation
        // independent of the snapshot's potentially larger serialization work.
        let store = self.store.lock().map_err(store::err)?;
        let mut progress = {
            // Worker transitions use this lock too. Reading flags later could
            // pair an idle worker with the preceding incomplete statistics and
            // make the native client stop polling before its final update.
            SnapshotProgress {
                stats: runtime.stats.clone(),
                foreground_scan: runtime
                    .foreground
                    .as_ref()
                    .map(|request| request.snapshot.clone())
                    .or_else(|| runtime.restored_foreground.clone()),
                error: runtime.error.clone(),
                scanning: self.scanning.load(Ordering::Acquire),
                cleaning: self.cleaning.load(Ordering::Acquire),
            }
        };
        // SQLite owns every persistent snapshot field. The process epoch stops
        // an old client token being reused after a connection/library restart.
        // This counter may invalidate conservatively for journal writes, but
        // cannot miss a wallet, history, grant, Keep or candidate write.
        let content_revision = format!("{}:{}", self.snapshot_epoch, store.conn.total_changes());
        let revision =
            blake3::hash(&serde_json::to_vec(&(&content_revision, &progress)).map_err(store::err)?)
                .to_hex()
                .to_string();
        drop(runtime);
        let content_unchanged = after_content_revision == Some(content_revision.as_str());
        if content_unchanged && after_revision == Some(revision.as_str()) {
            return Ok(SnapshotUpdate {
                revision,
                content_revision,
                changed: false,
                snapshot: None,
                progress: None,
            });
        }
        store.apply_coverage(&mut progress.stats)?;
        if content_unchanged {
            return Ok(SnapshotUpdate {
                revision,
                content_revision,
                changed: true,
                snapshot: None,
                progress: Some(progress),
            });
        }
        let snapshot = Snapshot {
            roots: store.roots()?,
            candidates: store.candidates()?,
            history: store.history()?,
            wallet: store.wallet()?,
            scanning: progress.scanning,
            cleaning: progress.cleaning,
            stats: progress.stats,
            foreground_scan: progress.foreground_scan,
            error: progress.error,
            kept_paths: store.kept()?,
        };
        Ok(SnapshotUpdate {
            revision,
            content_revision,
            changed: true,
            snapshot: Some(snapshot),
            progress: None,
        })
    }
    pub fn request(self: &Arc<Self>, request: Value) -> Result<Value> {
        let action = request
            .get("action")
            .and_then(Value::as_str)
            .ok_or("Missing action")?;
        match action {
            "snapshot" => serde_json::to_value(self.snapshot()?).map_err(store::err),
            "snapshot_if_changed" => serde_json::to_value(
                self.snapshot_update(
                    request.get("after_revision").and_then(Value::as_str),
                    request
                        .get("after_content_revision")
                        .and_then(Value::as_str),
                )?,
            )
            .map_err(store::err),
            "storage_usage" => {
                serde_json::to_value(self.store.lock().map_err(store::err)?.derived_usage()?)
                    .map_err(store::err)
            }
            "maintain_storage" => {
                serde_json::to_value(self.maintain_idle_storage(true)?.ok_or(
                    "Storage maintenance waits for discovery and file operations to finish.",
                )?)
                .map_err(store::err)
            }
            "managed_review" => {
                if request.get("confirmed_read_only").and_then(Value::as_bool) != Some(true) {
                    return Err("Confirm the installed tool's read-only review first.".into());
                }
                let provider = request
                    .get("provider")
                    .and_then(Value::as_str)
                    .ok_or("Choose an installed cache provider")?;
                let request_id = managed_request_id(&request)?;
                let cancel = Arc::new(AtomicBool::new(false));
                {
                    let mut state = self.managed_review.lock().map_err(store::err)?;
                    if state.active.is_some() {
                        return Err("An installed-tool review is already running.".into());
                    }
                    if state.cancelled.as_deref() == Some(request_id) {
                        return Err("The installed-tool review was cancelled.".into());
                    }
                    state.active = Some((request_id.to_owned(), Arc::clone(&cancel)));
                }
                let _review = ManagedReviewGuard(&self.managed_review);
                // No runtime, index, cleanup, or reward lock is held while a
                // bounded, write-restricted owner tool produces its evidence.
                serde_json::to_value(managed_providers::review_installed(provider, &cancel)?)
                    .map_err(store::err)
            }
            "cancel_managed_review" => {
                let request_id = managed_request_id(&request)?;
                let mut state = self.managed_review.lock().map_err(store::err)?;
                if let Some((id, cancel)) = &state.active
                    && id == request_id
                {
                    cancel.store(true, Ordering::Release);
                }
                // At most one native request can be queued. Remember its
                // early cancellation without an unbounded tombstone set.
                state.cancelled = Some(request_id.to_owned());
                Ok(json!({"cancelled":true}))
            }
            "set_interactive" => {
                let active = request
                    .get("active")
                    .and_then(Value::as_bool)
                    .ok_or("set_interactive requires a boolean active")?;
                let was_active = self.interactive.swap(active, Ordering::AcqRel);
                if active && !was_active {
                    // Advisory UI state neither schedules work nor touches an
                    // admission lock. Advancing the existing wait predicate
                    // only wakes a background worker that was already batching.
                    self.expedite_discovery();
                }
                Ok(json!({"ok":true}))
            }
            "cleanup_progress" => {
                serde_json::to_value(&*self.cleanup_progress.lock().map_err(store::err)?)
                    .map_err(store::err)
            }
            "duplicate_progress" => {
                serde_json::to_value(&*self.duplicate_progress.lock().map_err(store::err)?)
                    .map_err(store::err)
            }
            "check_duplicates" => {
                let _checking = self.begin_duplicate_check()?;
                self.check_duplicates()
            }
            "cancel_duplicates" => {
                self.cancel_duplicates();
                Ok(json!({"ok":true}))
            }
            "prepare_duplicate" => self.prepare_duplicate(&request),
            "authorize" => {
                if self.busy.load(Ordering::Acquire) {
                    return Err("Wait for the current operation before adding a folder.".into());
                }
                let root = safety::authorize(
                    Path::new(string(&request, "path")?),
                    string(&request, "kind")?,
                )?;
                let replace_contained = request
                    .get("replace_contained")
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                // Physical validation above may overlap a new worker launch.
                if self.busy.load(Ordering::Acquire) {
                    return Err("Wait for the current operation before adding a folder.".into());
                }
                self.store
                    .lock()
                    .map_err(store::err)?
                    .authorize_root(&root, replace_contained)?;
                runtime.recent_files.clear();
                runtime.foreground = None;
                runtime.restored_foreground = None;
                self.invalidate_duplicates(None, None);
                serde_json::to_value(root).map_err(store::err)
            }
            "forget" => {
                if self.busy.load(Ordering::Acquire) {
                    return Err("Cancel the current operation before removing a folder.".into());
                }
                let id = string(&request, "id")?;
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                if self.busy.load(Ordering::Acquire) {
                    return Err("Cancel the current operation before removing a folder.".into());
                }
                if self.store.lock().map_err(store::err)?.remove_root(id)? {
                    runtime.recent_files.clear();
                    runtime.foreground = None;
                    runtime.restored_foreground = None;
                    self.invalidate_duplicates(Some(id), None);
                }
                Ok(json!({"ok":true}))
            }
            "scan" => {
                let requested = request.get("root_id").and_then(Value::as_str);
                {
                    // Serialize the finite request with job claims, traversal
                    // coalescing, and the worker's final idle transition.
                    let mut runtime = self.runtime.lock().map_err(store::err)?;
                    if runtime
                        .foreground
                        .as_ref()
                        .is_some_and(|scan| scan.snapshot.active)
                    {
                        self.expedite_discovery();
                        return Ok(json!({"ok":true,"already_scanning":true}));
                    }
                    if self.cleaning.load(Ordering::Acquire)
                        || self.checking_duplicates.load(Ordering::Acquire)
                    {
                        return Err(
                            "Wait for the current file operation before starting a scan.".into(),
                        );
                    }
                    self.invalidate_duplicates(requested, None);
                    // A cancelled request may be replaced before its worker
                    // drains. Save its terminal result here on the utility
                    // request queue, never in the synchronous cancel callback.
                    self.persist_foreground_summary(&mut runtime);
                    let mut store = self.store.lock().map_err(store::err)?;
                    let roots = store
                        .roots()?
                        .into_iter()
                        .filter(|root| requested.is_none() || requested == Some(root.id.as_str()))
                        .collect::<Vec<_>>();
                    runtime.foreground_generation = runtime.foreground_generation.wrapping_add(1);
                    runtime.foreground = Some(ForegroundRequest::new(
                        runtime.foreground_generation,
                        &roots,
                        store.foreground_context()?,
                    ));
                    for root in roots {
                        if let Err(error) = store.enqueue_scope(&root.id, &root.path) {
                            runtime.foreground.as_mut().unwrap().stop(false, &error);
                            runtime.error = Some(error.clone());
                            drop(store);
                            self.persist_foreground_summary(&mut runtime);
                            return Err(error);
                        }
                        // Keep disposable paths across full scans, but an older
                        // worker cannot replace this request's runtime state.
                        runtime.recent_files.received_batch();
                    }
                    drop(store);
                    if !self.scanning.load(Ordering::Acquire) {
                        runtime.stats = ScanStats::default();
                    }
                    runtime.error = None;
                    self.persist_foreground_summary(&mut runtime);
                    runtime.resume_cancelled_worker = self.scanning.load(Ordering::Acquire)
                        && self.cancel.load(Ordering::Acquire);
                    self.scan_paused.store(false, Ordering::Release);
                    runtime.scan_mode = if request.get("metadata_coverage").and_then(Value::as_bool)
                        == Some(true)
                    {
                        scanner::ScanMode::MetadataCoverage
                    } else {
                        scanner::ScanMode::Suggestions
                    };
                }
                if let Err(error) = self.launch_scan(ScanLaunch::Explicit) {
                    if let Ok(mut runtime) = self.runtime.lock() {
                        if let Some(scan) = &mut runtime.foreground {
                            scan.stop(false, &error);
                        }
                        self.persist_foreground_summary(&mut runtime);
                    }
                    return Err(error);
                }
                Ok(json!({"ok":true}))
            }
            "resume" => {
                // Restart only durable unfinished work, not every partially covered root.
                {
                    let mut runtime = self.runtime.lock().map_err(store::err)?;
                    runtime.resume_cancelled_worker = self.scanning.load(Ordering::Acquire)
                        && self.cancel.load(Ordering::Acquire);
                    self.scan_paused.store(false, Ordering::Release);
                }
                self.launch_scan(ScanLaunch::Explicit)?;
                Ok(json!({"ok":true}))
            }
            "dirty" => {
                let id = string(&request, "root_id")?.to_string();
                let paths = match request.get("paths") {
                    Some(value) => {
                        let values = value.as_array().ok_or("Event paths must be an array")?;
                        if values.len() > 512 {
                            return Err(
                                "Submit filesystem events in batches of at most 512 paths".into()
                            );
                        }
                        Some(
                            values
                                .iter()
                                .map(|value| {
                                    value
                                        .as_str()
                                        .ok_or_else(|| "Invalid filesystem event path".into())
                                })
                                .collect::<Result<Vec<_>>>()?,
                        )
                    }
                    None => request
                        .get("path")
                        .and_then(Value::as_str)
                        .map(|path| vec![path]),
                };
                // Decode the bounded payload before taking the request lock so
                // synchronous cancellation is not delayed by JSON cloning.
                let events = request
                    .get("events")
                    .map(|value| {
                        let values = value.as_array().ok_or("Events must be an array")?;
                        if values.len() > 512 {
                            return Err("Submit at most 512 filesystem events".into());
                        }
                        values
                            .iter()
                            .map(|event| {
                                serde_json::from_value::<refresh::FsEvent>(event.clone())
                                    .map_err(store::err)
                            })
                            .collect::<Result<Vec<_>>>()
                    })
                    .transpose()?;
                let duplicate_paths = events
                    .as_ref()
                    .map(|events| {
                        events
                            .iter()
                            .map(|event| event.path.clone())
                            .collect::<Vec<_>>()
                    })
                    .or_else(|| {
                        paths.as_ref().map(|paths| {
                            paths
                                .iter()
                                .map(|path| PathBuf::from(*path))
                                .collect::<Vec<_>>()
                        })
                    });
                self.invalidate_duplicates(Some(&id), duplicate_paths.as_deref());
                {
                    // Receipt and traversal begin share runtime→store ordering.
                    // A committed scope can never consume a hint from a later event.
                    let mut runtime = self.runtime.lock().map_err(store::err)?;
                    let mut store = self.store.lock().map_err(store::err)?;
                    let root = store.root(&id)?;
                    if let Some(events) = events {
                        let mut relevant = Vec::with_capacity(events.len());
                        let mut hints = Vec::new();
                        for event in events {
                            if let Some(scope) = refresh::event_scope_with_kind(
                                &root,
                                &event.path,
                                event.kind,
                                event.recursive,
                            )? {
                                hints.push((relevant.len(), event));
                                relevant.push(scope);
                            }
                        }
                        if relevant.is_empty() {
                            return Ok(json!({"ok":true,"ignored":true}));
                        }
                        store.enqueue_scopes(&id, &relevant)?;
                        // The journal is authoritative. Optional hints become visible
                        // only after the complete event batch has committed.
                        for (index, event) in hints {
                            runtime.recent_files.insert(&root, &event, &relevant[index]);
                        }
                    } else if let Some(paths) = paths {
                        let mut relevant = Vec::with_capacity(paths.len());
                        for path in paths {
                            if let Some(scope) = refresh::event_scope(&root, Path::new(path))? {
                                relevant.push(scope);
                            }
                        }
                        if relevant.is_empty() {
                            return Ok(json!({"ok":true,"ignored":true}));
                        }
                        store.enqueue_scopes(&id, &relevant)?;
                    } else {
                        store.enqueue_scope(&id, &root.path)?;
                    }
                    // Structural and legacy path-only batches also invalidate
                    // in-flight writeback, even when they provide no file hint.
                    runtime.recent_files.received_batch();
                }
                self.launch_scan(ScanLaunch::Background)?;
                Ok(json!({"ok":true}))
            }
            "cancel" => {
                self.cancel_scan();
                Ok(json!({"ok":true}))
            }
            "keep" => {
                let id = string(&request, "id")?;
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                let s = self.store.lock().map_err(store::err)?;
                let c = s.candidate(id)?;
                s.keep(&c.path.to_string_lossy(), true)?;
                runtime.recent_files.clear();
                self.invalidate_duplicates(None, None);
                Ok(json!({"ok":true}))
            }
            "unkeep" => {
                let path = PathBuf::from(string(&request, "path")?);
                let root = {
                    let mut runtime = self.runtime.lock().map_err(store::err)?;
                    let store = self.store.lock().map_err(store::err)?;
                    store.keep(&path.to_string_lossy(), false)?;
                    runtime.recent_files.clear();
                    self.invalidate_duplicates(None, None);
                    store
                        .roots()?
                        .into_iter()
                        .find(|root| path.starts_with(&root.path))
                };
                if let Some(root) = root {
                    self.scan_paused.store(false, Ordering::Release);
                    self.store
                        .lock()
                        .map_err(store::err)?
                        .enqueue_scope(&root.id, &path)?;
                    self.launch_scan(ScanLaunch::Immediate)?;
                }
                Ok(json!({"ok":true}))
            }
            "collect" => {
                let (from, to, amount) = self.store.lock().map_err(store::err)?.collect()?;
                Ok(json!({"from":from,"to":to,"amount":amount}))
            }
            "history" => {
                // Read-only ledger paging for the Activity screen. The bounded
                // snapshot history is unchanged; this walks older receipts.
                let before = request.get("before").and_then(Value::as_i64);
                let limit = request
                    .get("limit")
                    .and_then(Value::as_u64)
                    .unwrap_or(100)
                    .clamp(1, 500) as u32;
                let (receipts, next_before, total) = self
                    .store
                    .lock()
                    .map_err(store::err)?
                    .history_page(before, limit)?;
                Ok(json!({"receipts":receipts,"next_before":next_before,"total":total}))
            }
            "prepare" => {
                if self.cleaning.load(Ordering::Acquire)
                    || self.checking_duplicates.load(Ordering::Acquire)
                {
                    return Err(
                        "Wait for the current file operation before reviewing another.".into(),
                    );
                }
                let mode = string(&request, "operation")?;
                if mode != "trash" && mode != "permanent" {
                    return Err("Invalid operation.".into());
                }
                let reviewed: Vec<Candidate> = serde_json::from_value(
                    request
                        .get("items")
                        .cloned()
                        .ok_or("The exact reviewed items are required")?,
                )
                .map_err(store::err)?;
                if reviewed.is_empty() || reviewed.len() > 100 {
                    return Err("Review between 1 and 100 items at a time.".into());
                }
                let mut items = Vec::new();
                let s = self.store.lock().map_err(store::err)?;
                let kept = s.kept()?;
                for mut displayed in reviewed {
                    let c = s.candidate(&displayed.id)?;
                    // This server-owned policy flag is absent from Swift's
                    // projection; every user-reviewed field must still match.
                    displayed.suggestion_eligible = c.suggestion_eligible;
                    if c != displayed {
                        return Err("An item changed while its review was open. Review the refreshed result before cleanup.".into());
                    }
                    if !c.suggestion_eligible
                        || c.blocked_reason.is_some()
                        || (mode == "permanent"
                            && (!c.eligible_permanent || !recommendations::permanent_kind(&c.kind)))
                    {
                        return Err("An item is ineligible for this operation.".into());
                    }
                    // Cleanup removes the whole selected artifact. A Keep
                    // below it protects that descendant just as an ancestor
                    // Keep protects everything inside the kept directory.
                    if kept
                        .iter()
                        .any(|p| c.path.starts_with(p) || Path::new(p).starts_with(&c.path))
                    {
                        return Err("A selected item overlaps a path marked Keep.".into());
                    }
                    if items.iter().any(|(_, other): &(Root, Candidate)| {
                        c.path.starts_with(&other.path) || other.path.starts_with(&c.path)
                    }) {
                        return Err("Overlapping items cannot be cleaned twice.".into());
                    }
                    items.push((s.root(&c.root_id)?, c));
                }
                drop(s);
                let token = unique_id();
                #[cfg(test)]
                self.observe_review_admission();
                let mut reviews = self.reviews.lock().map_err(store::err)?;
                // Mutation admission takes this mutex before setting cleaning.
                // No successful review may be inserted after that cutoff.
                if self.cleaning.load(Ordering::Acquire)
                    || self.checking_duplicates.load(Ordering::Acquire)
                {
                    return Err(
                        "Wait for the current file operation before reviewing another.".into(),
                    );
                }
                reviews.retain(|_, r| {
                    review_is_live(r)
                        && r.cancel_generation == self.cancel_generation.load(Ordering::Acquire)
                });
                if items.iter().any(|(_, item)| {
                    reviews
                        .values()
                        .filter_map(|review| review.duplicate_keeper.as_ref())
                        .any(|keeper| candidates_overlap(item, &keeper.candidate))
                }) {
                    return Err("A selected file is reserved as the kept copy in a duplicate review. Finish or cancel that review first.".into());
                }
                if reviews.len() >= 64 {
                    return Err("Too many pending reviews. Close an earlier review first.".into());
                }
                reviews.insert(
                    token.clone(),
                    Review {
                        operation: mode.into(),
                        items,
                        created: now(),
                        cancel_generation: self.cancel_generation.load(Ordering::Acquire),
                        duplicate_keeper: None,
                        duplicate_created: None,
                    },
                );
                Ok(json!({"token":token}))
            }
            "execute" => {
                if request.get("confirmed").and_then(Value::as_bool) != Some(true) {
                    return Err("Explicit cleanup confirmation is required.".into());
                }
                let _mutation = self.begin_mutation()?;
                let review = self
                    .reviews
                    .lock()
                    .map_err(store::err)?
                    .remove(string(&request, "token")?)
                    .ok_or("Review expired or already consumed")?;
                if review.cancel_generation != self.cancel_generation.load(Ordering::Acquire) {
                    return Err(
                        "Cleanup was cancelled after review. Review again to continue.".into(),
                    );
                }
                if !review_is_live(&review) {
                    return Err("Review expired. Review the current items again.".into());
                }
                {
                    let mut reviews = self.reviews.lock().map_err(store::err)?;
                    reviews.retain(|_, pending| {
                        review_is_live(pending)
                            && pending.cancel_generation
                                == self.cancel_generation.load(Ordering::Acquire)
                    });
                    if review.items.iter().any(|(_, item)| {
                        reviews
                            .values()
                            .filter_map(|pending| pending.duplicate_keeper.as_ref())
                            .any(|keeper| candidates_overlap(item, &keeper.candidate))
                    }) {
                        return Err(
                            "This cleanup overlaps a copy reserved by another duplicate review."
                                .into(),
                        );
                    }
                }
                (|| {
                    let mut s = self.store.lock().map_err(store::err)?;
                    let mut receipts = Vec::new();
                    let item_count = review.items.len();
                    let duplicate_keeper = review.duplicate_keeper;
                    for (index, (root, candidate)) in review.items.into_iter().enumerate() {
                        if self.mutation_cancel.load(Ordering::Acquire) {
                            break;
                        }
                        if s.root(&root.id).is_err()
                            || s.kept()?.iter().any(|path| {
                                candidate.path.starts_with(path)
                                    || Path::new(path).starts_with(&candidate.path)
                            })
                        {
                            return Err("Folder access or Keep preferences changed. Review again before cleanup.".into());
                        }
                        if let Some(keeper) = &duplicate_keeper
                            && (review.operation != "trash"
                                || !same_root(&s.root(&root.id)?, &root)
                                || !same_root(&s.root(&keeper.root.id)?, &keeper.root)
                                || s.candidate(&keeper.candidate.id)? != keeper.candidate
                                || candidates_overlap(&candidate, &keeper.candidate))
                        {
                            return Err("The kept copy or its folder access changed. Check duplicates again.".into());
                        }
                        s.suppress_candidate(&candidate.id)?;
                        s.enqueue_scope(&root.id, &candidate.path)?;
                        *self.cleanup_progress.lock().map_err(store::err)? =
                            Some(CleanupProgress {
                                phase: cleanup::CleanupPhase::Checking,
                                completed_entries: 0,
                                total_entries: 0,
                                item_number: index + 1,
                                item_count,
                                title: candidate.title.clone(),
                            });
                        match cleanup::execute_with_duplicate_guard(
                            &mut s,
                            &root,
                            &candidate,
                            &review.operation,
                            self.trash,
                            &self.mutation_cancel,
                            duplicate_keeper.as_ref(),
                            |phase, completed, total| {
                                if let Ok(mut progress) = self.cleanup_progress.lock()
                                    && let Some(progress) = progress.as_mut()
                                {
                                    progress.phase = phase;
                                    progress.completed_entries = completed;
                                    progress.total_entries = total;
                                }
                            },
                        ) {
                            Ok(r) => receipts.push(r),
                            Err(e) => {
                                let r = Receipt {
                                    id: unique_id(),
                                    path: candidate.path.to_string_lossy().into(),
                                    title: candidate.title.clone(),
                                    operation: review.operation.clone(),
                                    outcome: "skipped".into(),
                                    detail: e,
                                    created_at: now(),
                                    reported_bytes: candidate.allocated_bytes,
                                    observed_bytes: 0,
                                    credited_bytes: 0,
                                    coins: 0,
                                    trash_path: None,
                                    can_restore: false,
                                    seq: None,
                                };
                                s.prepare_operation(&root, &candidate, &r, &candidate.path)?;
                                s.finish_operation(&r, None)?;
                                receipts.push(r);
                            }
                        }
                    }
                    serde_json::to_value(receipts).map_err(store::err)
                })()
            }
            "restore" => {
                let id = string(&request, "id")?;
                let _mutation = self.begin_mutation()?;
                (|| {
                    let mut store = self.store.lock().map_err(store::err)?;
                    cleanup::restore(&mut store, id, &self.mutation_cancel)
                        .and_then(|r| serde_json::to_value(r).map_err(store::err))
                })()
            }
            "reconcile_events" => {
                let cursor = request
                    .get("value")
                    .and_then(Value::as_u64)
                    .ok_or("Event reconciliation requires a cursor")?;
                self.invalidate_duplicates(None, None);
                {
                    let mut runtime = self.runtime.lock().map_err(store::err)?;
                    let mut store = self.store.lock().map_err(store::err)?;
                    store.reconcile_events(cursor)?;
                    runtime.recent_files.clear();
                }
                self.launch_scan(ScanLaunch::Background)?;
                Ok(json!({"cursor": cursor}))
            }
            "cursor" => {
                let s = self.store.lock().map_err(store::err)?;
                if let Some(value) = request.get("value").and_then(Value::as_u64) {
                    // Receipt of events is durable before Swift acknowledges them.
                    // Coverage may remain partial without replaying the entire history.
                    s.conn
                        .execute(
                            "UPDATE event_cursor SET cursor=MAX(cursor,?1) WHERE id=1",
                            [value],
                        )
                        .map_err(store::err)?;
                }
                let cursor: u64 = s
                    .conn
                    .query_row("SELECT cursor FROM event_cursor WHERE id=1", [], |r| {
                        r.get(0)
                    })
                    .map_err(store::err)?;
                Ok(json!({"cursor":cursor}))
            }
            _ => Err("Unknown engine action".into()),
        }
    }

    fn begin_duplicate_check(self: &Arc<Self>) -> Result<DuplicateCheckGuard> {
        let runtime = self.runtime.lock().map_err(store::err)?;
        let reviews = self.reviews.lock().map_err(store::err)?;
        if self.busy.load(Ordering::Acquire) {
            return Err(
                "Wait for scanning or cleanup to finish before checking duplicate files.".into(),
            );
        }
        let generation = self.cancel_generation.load(Ordering::Acquire);
        self.checking_duplicates.store(true, Ordering::Release);
        self.busy.store(true, Ordering::Release);
        self.duplicate_cancel.store(false, Ordering::Release);
        drop(reviews);
        drop(runtime);
        let guard = DuplicateCheckGuard(Arc::clone(self));
        {
            let mut state = self.duplicate_state.lock().map_err(store::err)?;
            state.report = None;
            state.active_paths.clear();
            state.generation = state.generation.wrapping_add(1);
        }
        *self.duplicate_progress.lock().map_err(store::err)? = Some(duplicates::Progress {
            phase: "index".into(),
            ..Default::default()
        });
        if self.cancel_generation.load(Ordering::Acquire) != generation {
            self.duplicate_cancel.store(true, Ordering::Release);
        }
        safety::cancelled(&self.duplicate_cancel)?;
        Ok(guard)
    }

    fn end_duplicate_check(self: &Arc<Self>) {
        if let Ok(_runtime) = self.runtime.lock() {
            // Release this check's paths before another caller can acquire a
            // new check; an older guard must never clear its successor's set.
            if let Ok(mut state) = self.duplicate_state.lock() {
                state.active_paths.clear();
            }
            self.checking_duplicates.store(false, Ordering::Release);
            self.busy.store(
                self.scanning.load(Ordering::Acquire) || self.cleaning.load(Ordering::Acquire),
                Ordering::Release,
            );
        }
        let _ = self.launch_scan(ScanLaunch::Background);
    }

    fn check_duplicates(&self) -> Result<Value> {
        let inputs = {
            let store = self.store.lock().map_err(store::err)?;
            {
                let mut state = self.duplicate_state.lock().map_err(store::err)?;
                safety::cancelled(&self.duplicate_cancel)?;
                state.sql_active = true;
            }
            let result = store.duplicate_inputs(&self.duplicate_cancel);
            // Clear this before releasing Store. Cancellation holds the same
            // state mutex while interrupting, so it cannot interrupt a later,
            // unrelated query on this connection.
            self.duplicate_state.lock().map_err(store::err)?.sql_active = false;
            result?
        };
        let generation = {
            let mut state = self.duplicate_state.lock().map_err(store::err)?;
            state.active_paths = inputs
                .files
                .iter()
                .map(|input| (input.root.id.clone(), input.candidate.path.clone()))
                .collect();
            state.generation
        };
        let mut analysis = duplicates::analyze(inputs.files, &self.duplicate_cancel, |progress| {
            if let Ok(mut current) = self.duplicate_progress.lock() {
                *current = Some(progress.clone());
            }
        })?;
        if inputs.skipped_buckets > 0 || inputs.bucket_limit_reached {
            analysis.progress.limited = true;
            analysis.progress.complete = false;
        }
        *self.duplicate_progress.lock().map_err(store::err)? = Some(analysis.progress.clone());
        let token = unique_id();
        let groups: Vec<_> = analysis
            .groups
            .into_iter()
            .enumerate()
            .map(|(index, group)| (format!("{token}-{index}"), group))
            .collect();
        // In-flight events and preference changes invalidate the entire report.
        // Scanner row changes are checked too, including rows outside the UI page.
        let store = self.store.lock().map_err(store::err)?;
        for (_, group) in &groups {
            for input in &group.items {
                if !same_root(&store.root(&input.root.id)?, &input.root)
                    || store.candidate(&input.candidate.id)? != input.candidate
                {
                    return Err(
                        "An indexed file changed during the check. Refresh and check again.".into(),
                    );
                }
            }
        }
        let mut state = self.duplicate_state.lock().map_err(store::err)?;
        safety::cancelled(&self.duplicate_cancel)?;
        if state.generation != generation {
            return Err(
                "Files or folder preferences changed during the check. Check duplicates again."
                    .into(),
            );
        }
        let value = json!({
            "token":token,
            "groups":groups.iter().map(|(id,group)| json!({
                "id":id,
                "files":group.items.iter().map(|input| json!({
                    "candidate":input.candidate,"keeper_only":input.keeper_only
                })).collect::<Vec<_>>()
            })).collect::<Vec<_>>(),
            "progress":analysis.progress,
            "indexed_files":inputs.indexed_files,
            "skipped_buckets":inputs.skipped_buckets,
            "skipped_bucket_files":inputs.skipped_bucket_files,
            "bucket_limit_reached":inputs.bucket_limit_reached,
            "expires_in_seconds":DUPLICATE_REVIEW_LIFETIME.as_secs(),
        });
        // A cancelled pass is informational only, even if earlier groups matched.
        state.report = (!analysis.progress.cancelled).then_some(DuplicateReportState {
            token,
            groups,
            created: Instant::now(),
        });
        Ok(value)
    }

    fn prepare_duplicate(&self, request: &Value) -> Result<Value> {
        if self.cleaning.load(Ordering::Acquire) || self.checking_duplicates.load(Ordering::Acquire)
        {
            return Err("Wait for the current file operation before reviewing a copy.".into());
        }
        if string(request, "operation")? != "trash" {
            return Err("Verified duplicate copies are review and Trash-only.".into());
        }
        let report_token = string(request, "report_token")?;
        let group_id = string(request, "group_id")?;
        let keeper_id = string(request, "keeper_id")?;
        let copy_id = string(request, "copy_id")?;
        if keeper_id == copy_id {
            return Err("Choose a different copy to keep and a copy to review.".into());
        }
        let (keeper, copy) = {
            let state = self.duplicate_state.lock().map_err(store::err)?;
            let report = state
                .report
                .as_ref()
                .filter(|report| {
                    report.token == report_token
                        && report.created.elapsed() < DUPLICATE_REVIEW_LIFETIME
                })
                .ok_or("Duplicate evidence expired or changed. Check files again.")?;
            let group = report
                .groups
                .iter()
                .find(|(id, _)| id == group_id)
                .map(|(_, group)| group)
                .ok_or("The duplicate group is not in this report.")?;
            let keeper = group
                .items
                .iter()
                .find(|input| input.candidate.id == keeper_id)
                .ok_or("The chosen kept copy is not in this verified group.")?
                .clone();
            let copy = group
                .items
                .iter()
                .find(|input| input.candidate.id == copy_id && !input.keeper_only)
                .ok_or("The chosen copy cannot be cleaned from this verified group.")?
                .clone();
            (keeper, copy)
        };
        if candidates_overlap(&keeper.candidate, &copy.candidate) {
            return Err("The copies must be different, independent files.".into());
        }
        let store = self.store.lock().map_err(store::err)?;
        for input in [&keeper, &copy] {
            if !same_root(&store.root(&input.root.id)?, &input.root)
                || store.candidate(&input.candidate.id)? != input.candidate
                || safety::identity(&input.candidate.path)? != input.candidate.identity
            {
                return Err(
                    "A copy or its folder access changed. Refresh and check files again.".into(),
                );
            }
            safety::validate_root(&input.root)?;
            safety::check_scope_policy(&input.root, &input.candidate.path)?;
        }
        if store
            .kept()?
            .iter()
            .any(|path| path_overlap(&copy.candidate.path, Path::new(path)))
        {
            return Err("The copy selected for cleanup overlaps a path marked Keep.".into());
        }
        drop(store);
        let state = self.duplicate_state.lock().map_err(store::err)?;
        if !state.report.as_ref().is_some_and(|report| {
            report.token == report_token && report.created.elapsed() < DUPLICATE_REVIEW_LIFETIME
        }) {
            return Err(
                "Duplicate evidence changed while preparing the review. Check again.".into(),
            );
        }
        #[cfg(test)]
        self.observe_review_admission();
        let mut reviews = self.reviews.lock().map_err(store::err)?;
        if self.cleaning.load(Ordering::Acquire) || self.checking_duplicates.load(Ordering::Acquire)
        {
            return Err("Wait for the current file operation before reviewing a copy.".into());
        }
        reviews.retain(|_, review| {
            review_is_live(review)
                && review.cancel_generation == self.cancel_generation.load(Ordering::Acquire)
        });
        if reviews.len() >= 64 {
            return Err("Too many pending reviews. Close an earlier review first.".into());
        }
        if reviews.values().any(|review| {
            review
                .items
                .iter()
                .any(|(_, item)| candidates_overlap(item, &keeper.candidate))
                || review.duplicate_keeper.as_ref().is_some_and(|reserved| {
                    candidates_overlap(&reserved.candidate, &copy.candidate)
                })
        }) {
            return Err("One of these copies is reserved by another cleanup review. Finish or cancel that review first.".into());
        }
        let token = unique_id();
        reviews.insert(
            token.clone(),
            Review {
                operation: "trash".into(),
                items: vec![(copy.root, copy.candidate)],
                created: now(),
                cancel_generation: self.cancel_generation.load(Ordering::Acquire),
                duplicate_keeper: Some(keeper),
                duplicate_created: Some(Instant::now()),
            },
        );
        Ok(json!({"token":token}))
    }

    #[cfg(test)]
    fn observe_review_admission(&self) {
        let observer = self.review_admission_observer.lock().unwrap().clone();
        if let Some(observer) = observer {
            observer();
        }
    }

    /// Receives raw event paths before ordinary recommendation filtering, so a
    /// changed retained copy cannot leave an apparently live content report.
    fn invalidate_duplicates(&self, root_id: Option<&str>, paths: Option<&[PathBuf]>) {
        if let Ok(mut state) = self.duplicate_state.lock() {
            let affected = |id: &str, path: &Path| {
                root_id.is_none_or(|root| root == id)
                    && paths.is_none_or(|paths| paths.iter().any(|event| path_overlap(event, path)))
            };
            if state
                .active_paths
                .iter()
                .any(|(id, path)| affected(id, path))
            {
                state.generation = state.generation.wrapping_add(1);
            }
            if state.report.as_ref().is_some_and(|report| {
                report.groups.iter().any(|(_, group)| {
                    group
                        .items
                        .iter()
                        .any(|input| affected(&input.root.id, &input.candidate.path))
                })
            }) {
                state.report = None;
            }
        }
    }

    fn begin_mutation(self: &Arc<Self>) -> Result<MutationGuard> {
        {
            let _runtime = self.runtime.lock().map_err(store::err)?;
            // Both prepare paths hold reviews across their final admission
            // check and insertion. Once cleaning is set, no new keeper promise
            // can race past execute's reservation snapshot.
            let _reviews = self.reviews.lock().map_err(store::err)?;
            if self.checking_duplicates.load(Ordering::Acquire) {
                return Err("Wait for the duplicate check before starting cleanup.".into());
            }
            if self.cleaning.swap(true, Ordering::AcqRel) {
                return Err("Another cleanup is in progress.".into());
            }
            self.busy.store(true, Ordering::Release);
            self.mutation_cancel.store(false, Ordering::Release);
            self.pause_requested.store(true, Ordering::Release);
            // No observation from a preceding read epoch may be published
            // after this mutation admission, even if a killed helper reports
            // late output. The coordinator acknowledges the fence, not reap.
            self.read_epoch.fetch_add(1, Ordering::AcqRel);
        }
        self.invalidate_duplicates(None, None);
        let guard = MutationGuard(Arc::clone(self));
        let mut parked = self.parked.lock().map_err(store::err)?;
        // A debouncing worker sleeps on this condition too. Notify under the
        // same mutex used for its predicate check and wait, then await parking.
        self.pause_changed.notify_all();
        while !*parked && self.scanning.load(Ordering::Acquire) {
            parked = self.pause_changed.wait(parked).map_err(store::err)?;
        }
        drop(parked);
        Ok(guard)
    }

    fn end_mutation(self: &Arc<Self>) {
        if let Ok(mut progress) = self.cleanup_progress.lock() {
            *progress = None;
        }
        if let Ok(_runtime) = self.runtime.lock() {
            self.cleaning.store(false, Ordering::Release);
            self.busy
                .store(self.scanning.load(Ordering::Acquire), Ordering::Release);
            // Use the same mutex as the wait to prevent a lost wakeup.
            let _parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
            self.pause_requested.store(false, Ordering::Release);
            self.pause_changed.notify_all();
        }
        let _ = self.launch_scan(ScanLaunch::Background);
    }

    /// Called outside store/runtime locks. The walker retains its frontier and
    /// open descriptors while cleanup owns the filesystem mutation boundary.
    fn scan_checkpoint(&self) {
        if !self.pause_requested.load(Ordering::Acquire) {
            return;
        }
        let mut parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
        *parked = true;
        self.pause_changed.notify_all();
        while self.pause_requested.load(Ordering::Acquire) {
            parked = self
                .pause_changed
                .wait(parked)
                .unwrap_or_else(|e| e.into_inner());
        }
        *parked = false;
    }

    /// One interruptible wait for the event batch. Spurious notifications never
    /// extend its monotonic deadline; explicit requests, pause and cancellation
    /// wake it without polling.
    /// No store/runtime lock is held while this helper waits or parks.
    fn wait_for_debounce(&self, deadline: Instant, urgency: u64) {
        loop {
            self.scan_checkpoint();
            let parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
            if self.cancel.load(Ordering::Acquire) {
                return;
            }
            if self.pause_requested.load(Ordering::Acquire) {
                // The pause arrived after checkpoint's initial atomic check.
                // Release the mutex before checkpoint acquires it to park.
                drop(parked);
                continue;
            }
            if self.discovery_urgency.load(Ordering::Acquire) != urgency {
                return;
            }
            let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
                return;
            };
            #[cfg(test)]
            if let Some(observer) = self
                .debounce_wait_observer
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .as_ref()
            {
                let _ = observer.send(deadline);
            }
            let (parked, _) = self
                .pause_changed
                .wait_timeout(parked, remaining)
                .unwrap_or_else(|e| e.into_inner());
            drop(parked);
        }
    }

    fn wake_discovery(&self) {
        let _parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
        self.pause_changed.notify_all();
    }

    /// Scan callers hold runtime while changing this predicate. The interactive
    /// hint stays independent of long-running request locks; worker acquisition
    /// captures urgency before the hint, so either it selects the short deadline
    /// or this change remains visible and interrupts the wait. Change the
    /// predicate under the wait mutex so no notification can be lost.
    fn expedite_discovery(&self) {
        let _parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
        self.discovery_urgency.fetch_add(1, Ordering::AcqRel);
        self.pause_changed.notify_all();
    }

    // The caller holds runtime, serializing this transition with launch/mutation.
    fn finish_worker(&self) {
        self.scanning.store(false, Ordering::Release);
        self.busy
            .store(self.cleaning.load(Ordering::Acquire), Ordering::Release);
        let _parked = self.parked.lock().unwrap_or_else(|e| e.into_inner());
        self.pause_changed.notify_all();
    }

    /// One bounded derived-index slice and a non-waiting WAL checkpoint. The
    /// durable cleanup, recovery and reward ledgers are never quota-evicted.
    /// Try-locking avoids queuing maintenance behind foreground work; retaining
    /// the admission/review locks keeps a newly prepared review protected too.
    fn maintain_idle_storage(&self, truncate: bool) -> Result<Option<store::DerivedUsage>> {
        let Ok(_runtime) = self.runtime.try_lock() else {
            return Ok(None);
        };
        if self.busy.load(Ordering::Acquire)
            || self.scanning.load(Ordering::Acquire)
            || self.cleaning.load(Ordering::Acquire)
            || self.checking_duplicates.load(Ordering::Acquire)
        {
            return Ok(None);
        }
        let Ok(reviews) = self.reviews.try_lock() else {
            return Ok(None);
        };
        let protected: Vec<String> = reviews
            .values()
            .flat_map(|review| {
                review.items.iter().map(|(_, item)| item.id.clone()).chain(
                    review
                        .duplicate_keeper
                        .iter()
                        .map(|keeper| keeper.candidate.id.clone()),
                )
            })
            .collect();
        let Ok(mut store) = self.store.try_lock() else {
            return Ok(None);
        };
        let usage = store.maintain_derived(&protected)?;
        // TRUNCATE uses a zero busy timeout. Busy readers leave the WAL intact;
        // they are not waited for or evicted to satisfy a physical-size claim.
        Ok(Some(if truncate || usage.wal_bytes > 4 * 1024 * 1024 {
            store.truncate_wal()?
        } else {
            // Reuse a small WAL instead of creating/truncating it after every
            // ordinary event burst. The size threshold is a hint, not a cap.
            store.passive_checkpoint()?
        }))
    }

    /// Cancellation pauses event refreshes until an explicit Scan or Resume.
    /// Pending scopes stay in SQLite, independently of the event receipt cursor.
    pub fn cancel_scan(&self) {
        self.cancel_generation.fetch_add(1, Ordering::AcqRel);
        self.mutation_cancel.store(true, Ordering::Release);
        self.cancel_duplicates();
        self.cancel.store(true, Ordering::Release);
        self.scan_paused.store(true, Ordering::Release);
        // Drop parked before acquiring runtime: workers and launch/mutation
        // transitions must never acquire those mutexes in the opposite order.
        self.wake_discovery();
        if let Ok(mut runtime) = self.runtime.lock() {
            // Serialize with launch_scan, which may have been acquiring the
            // worker when the immediate cancellation flags were first set.
            self.cancel.store(true, Ordering::Release);
            self.scan_paused.store(true, Ordering::Release);
            runtime.resume_cancelled_worker = false;
            runtime.stats.cancelled = true;
            runtime.stats.complete = false;
            runtime.stats.message = "Scan paused; completed findings are ready to review.".into();
            if let Some(scan) = &mut runtime.foreground {
                scan.stop(true, "Scan paused; completed findings are ready to review.");
            }
        }
        // A launch already holding runtime could have reset cancellation after
        // the first notification. Wake again after the serialized flag update.
        self.wake_discovery();
    }

    /// Stops only an explicit content comparison. Ordinary discovery, pending
    /// reviews and scan completeness retain their own cancellation state.
    pub fn cancel_duplicates(&self) {
        self.duplicate_cancel.store(true, Ordering::Release);
        if let Ok(mut state) = self.duplicate_state.lock() {
            if state.sql_active {
                self.sql_interrupt.interrupt();
            }
            state.generation = state.generation.wrapping_add(1);
            state.report = None;
        }
    }

    fn launch_scan(self: &Arc<Self>, launch: ScanLaunch) -> Result<()> {
        let mut runtime = self.runtime.lock().map_err(store::err)?;
        if self.scan_paused.load(Ordering::Acquire) {
            return Ok(());
        }
        if launch == ScanLaunch::Explicit {
            // Wake an existing worker too. Immediate actions such as unkeep
            // retain their current batching when a worker already owns work.
            self.expedite_discovery();
        }
        {
            let store = self.store.lock().map_err(store::err)?;
            let retry_terminal = launch == ScanLaunch::Explicit
                && !self.scanning.load(Ordering::Acquire)
                && runtime
                    .foreground
                    .as_ref()
                    .is_some_and(|scan| !scan.snapshot.active);
            if runtime.foreground.is_none() || retry_terminal {
                let mut pending = store
                    .conn
                    .prepare_cached(
                        "SELECT EXISTS(SELECT 1 FROM pending_scopes WHERE root_id=?1 AND path=?2)",
                    )
                    .map_err(store::err)?;
                let mut roots = Vec::new();
                for root in store.roots()? {
                    let full: bool = pending
                        .query_row(
                            rusqlite::params![
                                root.id,
                                root.path.to_str().ok_or("Invalid root path")?
                            ],
                            |row| row.get(0),
                        )
                        .map_err(store::err)?;
                    if full {
                        roots.push(root);
                    }
                }
                // Startup recovery/rule refresh may be launched by the watcher
                // before Resume. Capture only already-pending full roots;
                // explicit Resume can replace an idle terminal result, but
                // incremental work never creates or replaces a foreground scan.
                if !roots.is_empty() {
                    runtime.foreground_generation = runtime.foreground_generation.wrapping_add(1);
                    runtime.foreground = Some(ForegroundRequest::new(
                        runtime.foreground_generation,
                        &roots,
                        store.foreground_context()?,
                    ));
                    if !self.scanning.load(Ordering::Acquire) {
                        // This is a new finite pass, not a continuation of the
                        // previous failure's counts, cancellation or errors.
                        runtime.stats = ScanStats::default();
                    }
                    // A full-root recovery can arrive while an incremental
                    // worker is already waiting. Promotion must wake that
                    // worker as well as bypassing a newly spawned wait.
                    self.expedite_discovery();
                }
            }
            if self.busy.load(Ordering::Acquire) || !store.has_pending_scopes()? {
                return Ok(());
            }
        }
        self.busy.store(true, Ordering::Release);
        self.cancel.store(false, Ordering::Release);
        self.scanning.store(true, Ordering::Release);
        runtime.resume_cancelled_worker = false;
        runtime.error = None;
        runtime.stats.cancelled = false;
        runtime.stats.complete = false;
        runtime.stats.message = "Looking for useful opportunities…".into();
        // Capture once at worker acquisition, rather than thread startup. Later
        // event batches neither extend the deadline nor consume user urgency.
        let debounce_urgency = self.discovery_urgency.load(Ordering::Acquire);
        let debounce = (launch == ScanLaunch::Background
            && !runtime
                .foreground
                .as_ref()
                .is_some_and(|scan| scan.snapshot.active))
        .then(|| {
            (
                Instant::now()
                    + if self.interactive.load(Ordering::Acquire) {
                        INTERACTIVE_BACKGROUND_BATCH_DELAY
                    } else {
                        BACKGROUND_BATCH_DELAY
                    },
                debounce_urgency,
            )
        });
        drop(runtime);
        let engine = Arc::clone(self);
        let worker = std::thread::Builder::new()
            .name("chippytea.discovery".into())
            .spawn(move || {
                #[cfg(target_os = "macos")]
                unsafe {
                    libc::pthread_set_qos_class_self_np(libc::qos_class_t::QOS_CLASS_UTILITY, 0);
                }
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if let Some((deadline, urgency)) = debounce {
                        engine.wait_for_debounce(deadline, urgency);
                    }
                    engine.run_discovery()
                }));
                let failure = match result {
                    Ok(Ok(())) => None,
                    Ok(Err(error)) => Some(error),
                    Err(_) => Some(
                        "Discovery stopped after an internal error; coverage is incomplete.".into(),
                    ),
                };
                if let Some(error) = failure {
                    engine.fail_worker(error);
                }
                // Maintenance is opportunistic. Failure must not change a
                // completed traversal into a rescan or repeat filesystem work.
                if let Err(error) = engine.maintain_idle_storage(false)
                    && let Ok(mut runtime) = engine.runtime.lock()
                {
                    runtime.error.get_or_insert_with(|| {
                        format!("Could not finish local storage maintenance: {error}")
                    });
                }
            });
        if let Err(error) = worker {
            let error = error.to_string();
            self.fail_worker(error.clone());
            return Err(error);
        }
        Ok(())
    }

    fn fail_worker(&self, error: String) {
        // Runtime is presentation state. Even a panic while updating it must
        // publish a terminal failure; durable discovery remains in SQLite.
        let mut runtime = self.runtime.lock().unwrap_or_else(|e| e.into_inner());
        let mut error = error;
        // The coordinator has returned (or unwound), so every helper receiver
        // is gone and can no longer publish. Recover *all* durable claims in
        // one transaction, including a claim whose initialization failed and
        // siblings not reached after another scope's database error. If the
        // database is still unavailable, retry at the next worker admission;
        // never require an application restart to make progress again.
        let mut store = self.store.lock().unwrap_or_else(|e| e.into_inner());
        match store.recover_discovery() {
            Ok(()) => self.store.clear_poison(),
            Err(recovery) => {
                error.push_str(&format!(" Replay remains journaled: {recovery}"));
            }
        }
        drop(store);
        runtime.error = Some(error.clone());
        runtime.stats.complete = false;
        runtime.stats.errors = runtime.stats.errors.saturating_add(1);
        runtime.resume_cancelled_worker = false;
        if let Some(scan) = &mut runtime.foreground {
            scan.stop(false, &error);
        }
        self.persist_foreground_summary(&mut runtime);
        self.runtime.clear_poison();
        self.finish_worker();
    }

    /// Terminal presentation is saved once per request, not once per scope or
    /// event. It is historical information, independent of coverage and work
    /// journals. A save failure must not repeat completed filesystem work.
    /// Callers hold runtime, preserving request generation and lock ordering.
    fn persist_foreground_summary(&self, runtime: &mut Runtime) {
        let Some(scan) = &mut runtime.foreground else {
            return;
        };
        if scan.snapshot.active || scan.summary_attempted {
            return;
        }
        scan.summary_attempted = true;
        let result = self
            .store
            .lock()
            .map_err(store::err)
            .and_then(|mut store| store.save_foreground_summary(scan.context, &scan.snapshot));
        if let Err(error) = result {
            runtime
                .error
                .get_or_insert_with(|| format!("Could not save the last scan summary: {error}"));
        }
    }

    #[cfg(test)]
    fn observe_discovery(&self, stage: DiscoveryStage, id: &str, path: &Path) {
        let observer = self.discovery_observer.lock().unwrap().clone();
        if let Some(observer) = observer {
            observer(stage, id, path);
        }
    }

    fn run_discovery(&self) -> Result<()> {
        // Exactly one discovery coordinator owns this boundary. A preceding
        // error may have been unable to requeue its claims while SQLite was
        // unavailable. Retry before admitting any new publication authority.
        {
            let _runtime = self.runtime.lock().map_err(store::err)?;
            let mut store = self.store.lock().unwrap_or_else(|e| e.into_inner());
            store.recover_discovery()?;
            self.store.clear_poison();
        }
        #[cfg(test)]
        {
            let helper = self.scan_helper_fixture.lock().map_err(store::err)?.clone();
            if let Some(helper) = helper {
                return self.run_discovery_isolated(&helper);
            }
        }
        #[cfg(not(test))]
        {
            let helper = scan_worker::bundled_helper()
                .ok_or("The trusted scan helper is unavailable; discovery stopped incomplete.")?;
            self.run_discovery_isolated(&helper)
        }
        #[cfg(test)]
        loop {
            self.scan_checkpoint();
            let job = {
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                if self.cancel.load(Ordering::Acquire) {
                    if runtime.resume_cancelled_worker && !self.scan_paused.load(Ordering::Acquire)
                    {
                        // A new Scan/Resume can arrive while the previous pass
                        // drains. Only reset cancellation between durable jobs.
                        runtime.resume_cancelled_worker = false;
                        self.cancel.store(false, Ordering::Release);
                    } else {
                        runtime.stats.cancelled = true;
                        if let Some(scan) = &mut runtime.foreground {
                            scan.stop(true, "Scan paused; completed findings are ready to review.");
                        }
                        self.persist_foreground_summary(&mut runtime);
                        self.finish_worker();
                        return Ok(());
                    }
                }
                let job = self.store.lock().map_err(store::err)?.take_scope()?;
                let Some((id, path)) = job else {
                    if let Some(scan) = &mut runtime.foreground {
                        scan.stop(
                            false,
                            "Scan stopped before every requested folder was checked.",
                        );
                    }
                    self.persist_foreground_summary(&mut runtime);
                    self.finish_worker();
                    return Ok(());
                };
                let ticket = runtime
                    .foreground
                    .as_mut()
                    .and_then(|scan| scan.claim(&id, &path));
                (id, path, ticket)
            };
            let (id, path, mut ticket) = job;
            #[cfg(test)]
            self.observe_discovery(DiscoveryStage::Claimed, &id, &path);
            // Database/start/finalization failures leave the durable claim in
            // place. Only an atomically acknowledged scope reaches this point.
            let outcome = self.scan_root(&id, &path, &mut ticket)?;
            {
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                if let (Some(scan), Some(ticket)) = (&mut runtime.foreground, &ticket) {
                    scan.finish(ticket, Ok(&outcome.stats));
                }
                if let Some(error) = outcome.error {
                    runtime.error = Some(error);
                }
                self.persist_foreground_summary(&mut runtime);
            }
            #[cfg(test)]
            self.observe_discovery(DiscoveryStage::Finished, &id, &path);
        }
    }

    fn begin_isolated_scope(&self, helper: &Path) -> Result<Option<IsolatedScope>> {
        let mut runtime = self.runtime.lock().map_err(store::err)?;
        if self.cancel.load(Ordering::Acquire) || self.pause_requested.load(Ordering::Acquire) {
            return Ok(None);
        }
        let mut store = self.store.lock().map_err(store::err)?;
        let Some((id, claimed)) = store.take_scope_bounded(scan_worker::ACTIVE_SCANS)? else {
            return Ok(None);
        };
        let root = store.root(&id)?;
        let indexed = store.enclosing_candidate(&root, &claimed)?;
        let enclosing_parent = claimed
            .parent()
            .map(|parent| store.enclosing_candidate(&root, parent))
            .transpose()?
            .flatten();
        let hints = (runtime.scan_mode == scanner::ScanMode::Suggestions)
            .then(|| runtime.recent_files.snapshot());
        let request = scan_worker::ScanRequest {
            root: root.clone(),
            requested: claimed.clone(),
            indexed,
            enclosing_parent,
            kept: store
                .kept()?
                .into_iter()
                .map(PathBuf::from)
                .filter(|path| path_overlap(path, &root.path))
                .collect(),
            metadata_coverage: runtime.scan_mode == scanner::ScanMode::MetadataCoverage,
            recent_files: hints.as_ref().map(|(_, hints)| hints.clone()),
        };
        // This resolver is deliberately lexical. All directory/metadata and
        // ownership probes run in the child, never under the admission lock.
        let (resolved, cargo_lock) = scan_worker::resolve_request(&request)?;
        let scope = (resolved != root.path).then_some(resolved.as_path());
        let ticket = runtime
            .foreground
            .as_mut()
            .and_then(|scan| scan.claim(&id, &resolved));
        let refresh = if cargo_lock {
            store.begin_cargo_lock_refresh(&root, &claimed)?
        } else {
            store.begin_scope_refresh(&root, &claimed, scope)?
        };
        let handle = match scan_worker::start(helper, request) {
            Ok(handle) => handle,
            Err(error) => {
                let stats = ScanStats {
                    errors: 1,
                    message: error.clone(),
                    ..Default::default()
                };
                store.finish_scope_refresh(&refresh, &stats, true)?;
                if let (Some(scan), Some(ticket)) = (&mut runtime.foreground, &ticket) {
                    scan.finish(ticket, Ok(&stats));
                }
                return Err(error);
            }
        };
        Ok(Some(IsolatedScope {
            root,
            resolved,
            cargo_lock,
            ticket,
            refresh,
            handle,
            stats: ScanStats::default(),
            hints_revision: hints.map(|(revision, _)| revision),
            epoch: self.read_epoch.load(Ordering::Acquire),
            resolved_received: false,
            started: Instant::now(),
        }))
    }

    fn isolated_progress(
        &self,
        runtime: &mut Runtime,
        base: &ScanStats,
        settled: &ScanStats,
        active: &[IsolatedScope],
        started: Instant,
        first_finding: Option<u64>,
    ) {
        let mut total = combine_stats(base, settled);
        for scope in active {
            total = combine_stats(&total, &scope.stats);
        }
        total.elapsed_ms = base
            .elapsed_ms
            .saturating_add(started.elapsed().as_millis().min(u64::MAX as u128) as u64);
        total.first_finding_ms = base
            .first_finding_ms
            .or(first_finding.map(|ms| base.elapsed_ms.saturating_add(ms)));
        if !active.is_empty() {
            total.complete = false;
        }
        if total.errors != 0 || total.cancelled {
            total.complete = false;
        }
        runtime.stats = total;
    }

    /// Retire a read epoch before acknowledging mutation parking. Killing a
    /// helper and discarding its receiver never waits for a blocked kernel call;
    /// its fixed supervisor keeps the process slot until it can actually reap.
    fn retire_isolated_scopes(
        &self,
        active: &mut Vec<IsolatedScope>,
        cancelled: bool,
    ) -> Result<()> {
        for scope in active.iter() {
            scope.handle.abort();
        }
        let mut runtime = self.runtime.lock().map_err(store::err)?;
        let mut store = self.store.lock().map_err(store::err)?;
        let mut failure = None;
        for mut scope in active.drain(..) {
            scope.stats.complete = false;
            scope.stats.cancelled = cancelled;
            scope.stats.message = if cancelled {
                "Scan paused; scope queued for reconciliation."
            } else {
                "Read epoch ended for cleanup; scope queued for fresh reconciliation."
            }
            .into();
            if let Err(error) = store.finish_scope_refresh(&scope.refresh, &scope.stats, true) {
                // Keep retiring siblings even if one acknowledgement fails.
                // Their handles are already aborted; none may publish again.
                failure.get_or_insert(error);
            }
            if let (Some(scan), Some(ticket)) = (&mut runtime.foreground, &scope.ticket)
                && scan.accepts(ticket)
            {
                if cancelled {
                    scan.finish(ticket, Ok(&scope.stats));
                } else {
                    // The next read gets a fresh start, not the old helper's
                    // measurements or completion authority. Keep the finite
                    // foreground request active across an intervening cleanup.
                    let root = scan.roots.get_mut(&ticket.root_id).unwrap();
                    root.started_ms = None;
                    root.stats = ScanStats::default();
                    scan.rebuild();
                }
            }
        }
        if let Some(error) = failure {
            // A persistent error remains in the durable journal. fail_worker
            // and the next admission also retry this recovery transaction.
            return match store.recover_discovery() {
                Ok(()) => Err(error),
                Err(recovery) => Err(format!("{error}; replay remains journaled: {recovery}")),
            };
        }
        Ok(())
    }

    fn run_discovery_isolated(&self, helper: &Path) -> Result<()> {
        let base = self.runtime.lock().map_err(store::err)?.stats.clone();
        let started = Instant::now();
        let mut first_finding = None;
        let mut settled = ScanStats::default();
        // A helper failure is durable work, not a reason to immediately launch
        // the same failing helper again. Finish already-admitted siblings, then
        // leave the failed scope queued for an explicit Resume/retry.
        let mut stop_admissions = None::<String>;
        let mut active = Vec::<IsolatedScope>::with_capacity(scan_worker::ACTIVE_SCANS);
        loop {
            if self.cancel.load(Ordering::Acquire) {
                self.retire_isolated_scopes(&mut active, true)?;
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                if runtime.resume_cancelled_worker && !self.scan_paused.load(Ordering::Acquire) {
                    runtime.resume_cancelled_worker = false;
                    self.cancel.store(false, Ordering::Release);
                } else {
                    runtime.stats.cancelled = true;
                    runtime.stats.complete = false;
                    if let Some(scan) = &mut runtime.foreground {
                        scan.stop(true, "Scan paused; completed findings are ready to review.");
                    }
                    self.persist_foreground_summary(&mut runtime);
                    self.finish_worker();
                    return Ok(());
                }
            }
            if self.pause_requested.load(Ordering::Acquire)
                || active
                    .iter()
                    .any(|scope| scope.epoch != self.read_epoch.load(Ordering::Acquire))
            {
                self.retire_isolated_scopes(&mut active, false)?;
                self.scan_checkpoint();
                continue;
            }
            while active.len() < scan_worker::ACTIVE_SCANS && stop_admissions.is_none() {
                match self.begin_isolated_scope(helper) {
                    Ok(Some(scope)) => active.push(scope),
                    Ok(None) => break,
                    Err(error) => {
                        stop_admissions = Some(error);
                        break;
                    }
                }
            }
            if active.is_empty() {
                // Admission and the terminal transition share runtime with
                // event receipt; a new durable event cannot miss its worker.
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                if self.cancel.load(Ordering::Acquire)
                    || self.pause_requested.load(Ordering::Acquire)
                {
                    continue;
                }
                {
                    let mut store = self.store.lock().map_err(store::err)?;
                    if let Some(reason) = stop_admissions.take() {
                        // begin_isolated_scope can fail after claiming a scope
                        // but before it has a receiver. Recover that claim and
                        // any refresh marker in the same durable boundary.
                        store.recover_discovery()?;
                        drop(store);
                        runtime.error = Some(reason.clone());
                        runtime.stats.complete = false;
                        runtime.stats.errors = runtime.stats.errors.max(1);
                        runtime.stats.message = format!(
                            "Scan stopped after a read-only helper failure; pending scopes remain for Resume: {reason}"
                        );
                        let message = runtime.stats.message.clone();
                        if let Some(scan) = &mut runtime.foreground {
                            scan.stop(false, &message);
                            // All already-admitted siblings may have reached
                            // their terminal state before the failure barrier;
                            // preserve the actionable Resume message anyway.
                            scan.snapshot.stats.message = message;
                        }
                        self.persist_foreground_summary(&mut runtime);
                        self.finish_worker();
                        return Ok(());
                    }
                    if store.has_active_scopes()? {
                        return Err("Discovery has an abandoned durable scope claim.".into());
                    }
                    if store.has_pending_scopes()? {
                        // Receipt can enqueue work after the last empty claim
                        // attempt and before this runtime lock. It needs a new
                        // admission pass, not a false terminal failure.
                        continue;
                    }
                }
                self.isolated_progress(
                    &mut runtime,
                    &base,
                    &settled,
                    &active,
                    started,
                    first_finding,
                );
                if let Some(scan) = &mut runtime.foreground {
                    scan.stop(
                        false,
                        "Scan stopped before every requested folder was checked.",
                    );
                }
                self.persist_foreground_summary(&mut runtime);
                self.finish_worker();
                return Ok(());
            }
            let mut progressed = false;
            let mut index = 0;
            while index < active.len() {
                let event = match active[index].handle.try_recv() {
                    Ok(None) => {
                        index += 1;
                        continue;
                    }
                    Ok(Some(event)) => event,
                    Err(error) => scan_worker::ScanEvent::Failed(error),
                };
                progressed = true;
                let mut runtime = self.runtime.lock().map_err(store::err)?;
                // This lock is the publication linearization point shared by
                // mutation admission. Late output from an obsolete read epoch
                // is never written to the index or presented as completed.
                if self.cancel.load(Ordering::Acquire)
                    || self.pause_requested.load(Ordering::Acquire)
                    || active[index].epoch != self.read_epoch.load(Ordering::Acquire)
                {
                    break;
                }
                let scope = &mut active[index];
                let mut terminal = false;
                let mut finished_hints = None;
                let mut error = None;
                match event {
                    scan_worker::ScanEvent::Resolved { path, cargo_lock }
                        if !scope.resolved_received
                            && path == scope.resolved
                            && cargo_lock == scope.cargo_lock =>
                    {
                        scope.resolved_received = true;
                    }
                    scan_worker::ScanEvent::Batch(mut batch) if scope.resolved_received => {
                        if batch.candidates.len() > 512
                            || batch.candidates.iter().any(|candidate| {
                                candidate.root_id != scope.root.id
                                    || !candidate_in_read_scope(
                                        &scope.root,
                                        &scope.resolved,
                                        scope.cargo_lock,
                                        &candidate.path,
                                    )
                            })
                        {
                            error = Some(
                                "The scan helper returned a candidate outside its granted scope."
                                    .into(),
                            );
                            terminal = true;
                        } else {
                            if batch.candidates.iter().any(|candidate| {
                                candidate.suggestion_eligible
                                    && !candidate.provisional
                                    && candidate.blocked_reason.is_none()
                            }) {
                                first_finding.get_or_insert_with(|| {
                                    started.elapsed().as_millis().min(u64::MAX as u128) as u64
                                });
                                batch.stats.first_finding_ms = scope.stats.first_finding_ms.or(
                                    Some(scope.started.elapsed().as_millis().min(u64::MAX as u128)
                                        as u64),
                                );
                            }
                            batch.stats.first_finding_ms = scope
                                .stats
                                .first_finding_ms
                                .or(batch.stats.first_finding_ms);
                            self.store.lock().map_err(store::err)?.save_batch(&batch)?;
                            scope.stats = batch.stats;
                            if let (Some(scan), Some(ticket)) =
                                (&mut runtime.foreground, &scope.ticket)
                            {
                                scan.progress(ticket, &scope.stats);
                            }
                        }
                    }
                    scan_worker::ScanEvent::Finished {
                        mut stats,
                        recent_files,
                    } if scope.resolved_received => {
                        stats.first_finding_ms =
                            scope.stats.first_finding_ms.or(stats.first_finding_ms);
                        scope.stats = stats;
                        finished_hints = recent_files;
                        terminal = true;
                    }
                    scan_worker::ScanEvent::Failed(reason) => {
                        error = Some(reason);
                        terminal = true;
                    }
                    _ => {
                        error = Some("The scan helper returned an invalid event sequence.".into());
                        terminal = true;
                    }
                }
                if terminal {
                    let mut scope = active.remove(index);
                    let failed = error.is_some();
                    if let Some(error) = error {
                        scope.handle.abort();
                        scope.stats.complete = false;
                        scope.stats.errors = scope.stats.errors.saturating_add(1);
                        scope.stats.message = format!("Could not complete this scope: {error}");
                        runtime.error = Some(error.clone());
                        stop_admissions.get_or_insert(error);
                    }
                    let mut store = self.store.lock().map_err(store::err)?;
                    // Failed helper/protocol output must remain replayable. A
                    // successful partial Finished is still acknowledged normally.
                    store.finish_scope_refresh(&scope.refresh, &scope.stats, failed)?;
                    store.apply_root_coverage(&scope.root.id, &mut scope.stats)?;
                    drop(store);
                    if scope.stats.complete
                        && scope.stats.errors == 0
                        && !scope.stats.cancelled
                        && let (Some(revision), Some(hints)) =
                            (scope.hints_revision, finished_hints)
                    {
                        runtime.recent_files.replace_if_unchanged(revision, hints);
                    }
                    if let (Some(scan), Some(ticket)) = (&mut runtime.foreground, &scope.ticket) {
                        scan.finish(ticket, Ok(&scope.stats));
                    }
                    settled = combine_stats(&settled, &scope.stats);
                    if stop_admissions.is_none() {
                        self.persist_foreground_summary(&mut runtime);
                    }
                } else {
                    index += 1;
                }
                self.isolated_progress(
                    &mut runtime,
                    &base,
                    &settled,
                    &active,
                    started,
                    first_finding,
                );
            }
            if !progressed {
                // No per-root waiter threads. One coordinator checks bounded
                // mailboxes, with the same condition used by cancel/mutation.
                let parked = self.parked.lock().map_err(store::err)?;
                if !self.cancel.load(Ordering::Acquire)
                    && !self.pause_requested.load(Ordering::Acquire)
                {
                    let _ = self
                        .pause_changed
                        .wait_timeout(parked, Duration::from_millis(5))
                        .map_err(store::err)?;
                }
            }
        }
    }

    #[cfg(test)]
    fn scan_root(
        &self,
        id: &str,
        requested: &Path,
        ticket: &mut Option<ForegroundTicket>,
    ) -> Result<ScopeOutcome> {
        let (root, indexed) = {
            let store = self.store.lock().map_err(store::err)?;
            let root = store.root(id)?;
            let mut indexed = store.enclosing_candidate(&root, requested)?;
            if indexed.as_deref() == Some(requested)
                && refresh::cargo_lock_target(&root, requested)?.is_some()
                && let Some(parent) = requested.parent()
                && let Some(enclosing) = store.enclosing_candidate(&root, parent)?
            {
                // A partial file-to-directory refresh can retain an old parent
                // row beside a new lockfile download row. Reconcile that larger
                // footprint before applying the dependency-specific shortcut.
                indexed = Some(enclosing);
            }
            (root, indexed)
        };
        // Partial coverage does not widen an unrelated event into a Home scan.
        let resolved = refresh::resolve_scope(&root, requested, indexed)?;
        let scope = (resolved != root.path).then_some(resolved.as_path());
        let cargo_lock =
            requested == resolved && refresh::cargo_lock_target(&root, &resolved)?.is_some();
        let (base, mode, refresh, mut recent_files, kept) = {
            let mut runtime = self.runtime.lock().map_err(store::err)?;
            if self.cancel.load(Ordering::Acquire) {
                // A cancelled old claim must not adopt or coalesce a new Scan
                // before the worker resets cancellation between durable jobs.
                self.store
                    .lock()
                    .map_err(store::err)?
                    .cancel_claimed_scope(id, requested)?;
                return Ok(ScopeOutcome {
                    stats: ScanStats {
                        cancelled: true,
                        ..Default::default()
                    },
                    error: None,
                });
            }
            let mut store = self.store.lock().map_err(store::err)?;
            // Multiple file events may resolve to the same directory. Coalesce
            // only work received before this traversal starts; later events stay queued.
            // This boundary shares the request lock: a previously claimed full
            // job may adopt a new request here, before any traversal begins.
            // Once begun, its ticket is fixed and cannot consume a later Scan.
            if scope.is_none()
                && let Some(scan) = &mut runtime.foreground
            {
                if !ticket.as_ref().is_some_and(|ticket| scan.accepts(ticket)) {
                    *ticket = scan.claim(id, &resolved);
                }
                if let Some(ticket) = ticket.as_ref().filter(|ticket| scan.accepts(ticket)) {
                    let elapsed = scan.elapsed_ms();
                    scan.roots.get_mut(&ticket.root_id).unwrap().started_ms = Some(elapsed);
                }
            }
            // Keep changes accepted before this traversal begins are exclusions
            // for both ordinary discovery and the optional original-file probe.
            let kept = store
                .kept()?
                .into_iter()
                .map(PathBuf::from)
                .collect::<Vec<_>>();
            let refresh = if cargo_lock {
                store.begin_cargo_lock_refresh(&root, requested)?
            } else {
                store.begin_scope_refresh(&root, requested, scope)?
            };
            // Traversal edits only this bounded path pool. A later event, Scan,
            // Keep, or grant change prevents its writeback at scope completion.
            let recent_files = (runtime.scan_mode == scanner::ScanMode::Suggestions && !cargo_lock)
                .then(|| runtime.recent_files.snapshot());
            (
                runtime.stats.clone(),
                runtime.scan_mode,
                refresh,
                recent_files,
                kept,
            )
        };
        #[cfg(test)]
        self.observe_discovery(DiscoveryStage::Began, id, &resolved);
        let mut failure = None;
        let mut latest = ScanStats::default();
        let result = if let Err(reason) = safety::check_scope_policy(&root, &resolved) {
            // A replayed scope can predate the current exclusion policy. Prune
            // its derived results without opening or probing protected content.
            Ok(ScanStats {
                skipped: 1,
                complete: true,
                message: format!("Excluded scope reconciled without filesystem access: {reason}."),
                ..Default::default()
            })
        } else {
            let publish = |batch: ScanBatch| {
                if failure.is_some() {
                    return;
                }
                let saved = self
                    .store
                    .lock()
                    .map_err(store::err)
                    .and_then(|mut store| store.save_batch(&batch));
                if let Err(error) = saved {
                    failure = Some(error);
                    self.cancel.store(true, Ordering::Release);
                    return;
                }
                latest.clone_from(&batch.stats);
                if let Ok(mut runtime) = self.runtime.lock() {
                    runtime.stats = combine_stats(&base, &batch.stats);
                    if let (Some(scan), Some(ticket)) = (&mut runtime.foreground, ticket.as_ref()) {
                        scan.progress(ticket, &batch.stats);
                    }
                }
            };
            if cargo_lock {
                scanner::scan_cargo_lock_with_checkpoint_mode(
                    &root,
                    &resolved,
                    &kept,
                    &self.cancel,
                    mode,
                    || self.scan_checkpoint(),
                    publish,
                )
            } else {
                scanner::scan_with_options(
                    &root,
                    scope,
                    &kept,
                    &self.cancel,
                    scanner::ScanOptions {
                        mode,
                        recent_files: recent_files.as_mut().map(|(_, hints)| hints),
                    },
                    || self.scan_checkpoint(),
                    publish,
                )
            }
        };
        if let Some(error) = failure {
            // An unsaved batch cannot safely acknowledge this traversal. Keep
            // its claim/generation for recovery instead of pruning old findings.
            return Err(error);
        }
        let (mut stats, error) = match result {
            Ok(stats) => (stats, None),
            Err(error) => {
                latest.complete = false;
                latest.cancelled |= self.cancel.load(Ordering::Acquire);
                latest.errors = latest.errors.saturating_add(1);
                latest.message = format!("Could not complete this scope: {error}");
                (latest, Some(error))
            }
        };
        #[cfg(test)]
        self.observe_discovery(DiscoveryStage::Scanned, id, &resolved);
        {
            let mut store = self.store.lock().map_err(store::err)?;
            store.finish_scope_refresh(&refresh, &stats, self.cancel.load(Ordering::Acquire))?;
            store.apply_root_coverage(id, &mut stats)?;
        }
        let mut runtime = self.runtime.lock().map_err(store::err)?;
        runtime.stats = combine_stats(&base, &stats);
        if stats.complete
            && !stats.cancelled
            && stats.errors == 0
            && !self.cancel.load(Ordering::Acquire)
            && let Some((revision, hints)) = recent_files
        {
            runtime.recent_files.replace_if_unchanged(revision, hints);
        }
        Ok(ScopeOutcome { stats, error })
    }
}

#[derive(Default)]
struct ManagedReviewState {
    active: Option<(String, Arc<AtomicBool>)>,
    cancelled: Option<String>,
}

fn managed_request_id(request: &Value) -> Result<&str> {
    let id = request
        .get("request_id")
        .and_then(Value::as_str)
        .ok_or("The owner review requires a request identifier")?;
    if id.is_empty()
        || id.len() > 128
        || !id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err("The owner review request identifier is invalid".into());
    }
    Ok(id)
}

struct ManagedReviewGuard<'a>(&'a Mutex<ManagedReviewState>);
impl Drop for ManagedReviewGuard<'_> {
    fn drop(&mut self) {
        self.0
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .active = None;
    }
}

struct DuplicateCheckGuard(Arc<Engine>);
impl Drop for DuplicateCheckGuard {
    fn drop(&mut self) {
        self.0.end_duplicate_check();
    }
}

fn same_root(left: &Root, right: &Root) -> bool {
    left.id == right.id
        && left.path == right.path
        && left.kind == right.kind
        && left.identity == right.identity
}

fn path_overlap(left: &Path, right: &Path) -> bool {
    left.starts_with(right) || right.starts_with(left)
}

fn candidates_overlap(left: &Candidate, right: &Candidate) -> bool {
    path_overlap(&left.path, &right.path)
        || (left.identity.device == right.identity.device
            && left.identity.inode == right.identity.inode)
}

fn review_is_live(review: &Review) -> bool {
    now().saturating_sub(review.created) < 120
        && review
            .duplicate_created
            .is_none_or(|created| created.elapsed() < DUPLICATE_REVIEW_LIFETIME)
}

/// Always resumes discovery, including expired review tokens and unwinding.
struct MutationGuard(Arc<Engine>);
impl Drop for MutationGuard {
    fn drop(&mut self) {
        self.0.end_mutation();
    }
}

fn combine_stats(base: &ScanStats, current: &ScanStats) -> ScanStats {
    ScanStats {
        entries: base.entries.saturating_add(current.entries),
        files: base.files.saturating_add(current.files),
        directories: base.directories.saturating_add(current.directories),
        logical_bytes: base.logical_bytes.saturating_add(current.logical_bytes),
        allocated_bytes: base.allocated_bytes.saturating_add(current.allocated_bytes),
        skipped: base.skipped.saturating_add(current.skipped),
        excluded_artifacts: base
            .excluded_artifacts
            .saturating_add(current.excluded_artifacts),
        metadata_skipped: base
            .metadata_skipped
            .saturating_add(current.metadata_skipped),
        errors: base.errors.saturating_add(current.errors),
        candidates: base.candidates.saturating_add(current.candidates),
        elapsed_ms: base.elapsed_ms.saturating_add(current.elapsed_ms),
        first_finding_ms: base.first_finding_ms.or(current
            .first_finding_ms
            .map(|ms| base.elapsed_ms.saturating_add(ms))),
        cancelled: current.cancelled,
        complete: current.complete,
        message: current.message.clone(),
    }
}

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("Missing {key}"))
}

/// Opens a uniquely locked local engine. A null return indicates failure.
///
/// # Safety
/// `path` must be a valid NUL-terminated UTF-8 string for this call. The optional
/// callback must obey the header's buffer contract and remain valid until close.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_open(
    path: *const libc::c_char,
    trash: Option<cleanup::TrashCallback>,
) -> *mut Arc<Engine> {
    if path.is_null() {
        return std::ptr::null_mut();
    }
    std::panic::catch_unwind(|| {
        let path = unsafe { CStr::from_ptr(path) }.to_str().ok()?;
        Engine::open(Path::new(path), trash)
            .ok()
            .map(|e| Box::into_raw(Box::new(e)))
    })
    .ok()
    .flatten()
    .unwrap_or(std::ptr::null_mut())
}

fn success_envelope(data: Value) -> Value {
    let mut envelope = serde_json::Map::new();
    envelope.insert("ok".into(), Value::Bool(true));
    // json! serializes a Value again; move this already-owned tree instead.
    envelope.insert("data".into(), data);
    Value::Object(envelope)
}

#[derive(serde::Serialize)]
struct SnapshotEnvelope<T> {
    ok: bool,
    data: T,
}

/// Executes a JSON command; the caller owns the returned UTF-8 response.
///
/// # Safety
/// `engine` must be a live handle from `ct_open`; `request` must be a valid
/// NUL-terminated UTF-8 string. Do not close the handle during this call. Free
/// each returned pointer exactly once with `ct_free_string`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_request(
    engine: *const Arc<Engine>,
    request: *const libc::c_char,
) -> *mut libc::c_char {
    let result = std::panic::catch_unwind(|| -> Result<String> {
        if engine.is_null() || request.is_null() {
            return Err("Invalid engine handle".into());
        }
        let text = unsafe { CStr::from_ptr(request) }
            .to_str()
            .map_err(store::err)?;
        let request: Value = serde_json::from_str(text).map_err(store::err)?;
        let engine = unsafe { &*engine };
        if request.get("action").and_then(Value::as_str) == Some("snapshot") {
            // Native polling only needs encoded JSON, not an intermediate Value
            // tree duplicating every snapshot field and string. Keep the public
            // Value-based request API unchanged for its Rust callers.
            serde_json::to_string(&SnapshotEnvelope {
                ok: true,
                data: engine.snapshot()?,
            })
            .map_err(store::err)
        } else if request.get("action").and_then(Value::as_str) == Some("snapshot_if_changed") {
            serde_json::to_string(&SnapshotEnvelope {
                ok: true,
                data: engine.snapshot_update(
                    request.get("after_revision").and_then(Value::as_str),
                    request
                        .get("after_content_revision")
                        .and_then(Value::as_str),
                )?,
            })
            .map_err(store::err)
        } else {
            engine
                .request(request)
                .map(|data| success_envelope(data).to_string())
        }
    });
    let response = match result {
        Ok(Ok(response)) => response,
        Ok(Err(error)) => json!({"ok":false,"error":error}).to_string(),
        Err(_) => {
            json!({"ok":false,"error":"The engine stopped this operation after an internal error."})
                .to_string()
        }
    };
    CString::new(response).unwrap().into_raw()
}
/// Cancels current work without waiting for a filesystem operation to finish.
///
/// # Safety
/// A non-null `engine` must be live and must not be closed concurrently.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_cancel(engine: *const Arc<Engine>) {
    if !engine.is_null() {
        unsafe { &*engine }.cancel_scan();
    }
}
/// Releases an owned command response.
///
/// # Safety
/// A non-null `value` must be an unfreed pointer returned by `ct_request`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_free_string(value: *mut libc::c_char) {
    if !value.is_null() {
        drop(unsafe { CString::from_raw(value) });
    }
}
/// Cancels outstanding discovery and releases the caller's engine handle.
///
/// # Safety
/// A non-null `engine` must have been returned by `ct_open`, must be closed only
/// once, and must not be in use by concurrent foreign calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_close(engine: *mut Arc<Engine>) {
    if !engine.is_null() {
        unsafe { &*engine }.cancel_scan();
        drop(unsafe { Box::from_raw(engine) });
    }
}

#[cfg(test)]
mod controller_tests {
    use super::*;
    use std::{
        fs,
        io::Write,
        time::{Duration, Instant, SystemTime},
    };

    #[test]
    fn isolated_results_cannot_escape_the_exact_read_scope() {
        let temp = tempfile::tempdir().unwrap();
        let root = safety::authorize(&fs::canonicalize(temp.path()).unwrap(), "folder").unwrap();
        let scope = root.path.join("project-a");
        assert!(candidate_in_read_scope(
            &root,
            &scope,
            false,
            &scope.join("target")
        ));
        assert!(!candidate_in_read_scope(
            &root,
            &scope,
            false,
            &root.path.join("project-b/target")
        ));
        assert!(!candidate_in_read_scope(
            &root,
            &scope,
            false,
            &scope.join("../project-b/target")
        ));
        assert!(!candidate_in_read_scope(
            &root, &root.path, false, &root.path
        ));
        let lock = scope.join("Cargo.lock");
        assert!(candidate_in_read_scope(&root, &lock, true, &lock));
        assert!(candidate_in_read_scope(
            &root,
            &lock,
            true,
            &scope.join("target")
        ));
        assert!(!candidate_in_read_scope(
            &root,
            &lock,
            true,
            &scope.join("target/unexpected-child")
        ));
        assert!(!candidate_in_read_scope(
            &root,
            &lock,
            true,
            &root.path.join("project-b/target")
        ));
    }

    #[test]
    fn owned_success_envelope_preserves_json_values_and_encoding() {
        for data in [
            Value::Null,
            Value::Bool(false),
            json!(u64::MAX),
            json!({
                "nested": [null, true, i64::MIN, u64::MAX, 9_007_199_254_740_993u64],
                "text": "café · 🪙\n\"quoted\"\0",
                "empty": {},
            }),
        ] {
            let expected = json!({"ok":true,"data":data});
            let actual = success_envelope(data);
            assert_eq!(actual, expected);
            assert_eq!(actual.to_string(), expected.to_string());
        }
    }

    struct FfiHandle(*mut Arc<Engine>);

    impl Drop for FfiHandle {
        fn drop(&mut self) {
            unsafe { ct_close(self.0) };
        }
    }

    fn parse_ffi_response(response: *mut libc::c_char) -> Value {
        assert!(!response.is_null());
        let bytes = unsafe { CStr::from_ptr(response) }.to_bytes().to_vec();
        unsafe { ct_free_string(response) };
        serde_json::from_slice(&bytes).expect("FFI responses must remain valid JSON")
    }

    fn ffi_response(engine: *const Arc<Engine>, request: &CStr) -> Value {
        parse_ffi_response(unsafe { ct_request(engine, request.as_ptr()) })
    }

    #[test]
    fn conditional_snapshots_separate_progress_and_persistent_content() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let full = engine.snapshot_update(None, None).unwrap();
        assert!(full.changed && full.snapshot.is_some() && full.progress.is_none());
        let unchanged = engine
            .snapshot_update(Some(&full.revision), Some(&full.content_revision))
            .unwrap();
        assert!(!unchanged.changed);
        assert!(unchanged.snapshot.is_none() && unchanged.progress.is_none());
        {
            let mut runtime = engine.runtime.lock().unwrap();
            runtime.stats.entries = 9_007_199_254_740_993;
            runtime.stats.message = "Disposable progress only".into();
            runtime.restored_foreground = Some(ForegroundScan {
                active: true,
                stats: runtime.stats.clone(),
            });
            engine.scanning.store(true, Ordering::Release);
        }
        let progress = engine
            .snapshot_update(Some(&full.revision), Some(&full.content_revision))
            .unwrap();
        assert!(progress.changed && progress.snapshot.is_none());
        assert_eq!(progress.content_revision, full.content_revision);
        assert_ne!(progress.revision, full.revision);
        let state = progress.progress.as_ref().unwrap();
        assert!(state.scanning);
        assert_eq!(state.stats.entries, 9_007_199_254_740_993);
        assert!(state.foreground_scan.as_ref().unwrap().active);
        assert!(serde_json::to_vec(&progress).unwrap().len() < 4096);
        assert!(
            engine
                .snapshot_update(Some(&progress.revision), Some(&progress.content_revision))
                .is_ok_and(|value| !value.changed)
        );
        // A persistent change, even outside the candidate list, requires a full
        // replacement. No wallet/history/Keep update can hide behind progress.
        engine
            .store
            .lock()
            .unwrap()
            .keep("/disposable/kept", true)
            .unwrap();
        let changed = engine
            .snapshot_update(Some(&progress.revision), Some(&progress.content_revision))
            .unwrap();
        assert!(changed.changed && changed.progress.is_none());
        assert_ne!(changed.content_revision, progress.content_revision);
        assert_eq!(
            changed.snapshot.unwrap().kept_paths,
            vec!["/disposable/kept"]
        );
        engine.scanning.store(false, Ordering::Release);
    }

    #[test]
    fn conditional_snapshot_tokens_are_connection_scoped_and_cold_reads_are_full() {
        let temp = tempfile::tempdir().unwrap();
        let db = temp.path().join("library.sqlite");
        let engine = Engine::open(&db, None).unwrap();
        let old = engine.snapshot_update(None, None).unwrap();
        for (revision, content) in [
            (None, None),
            (Some(old.revision.as_str()), None),
            (Some("stale"), Some("stale")),
        ] {
            let response = engine.snapshot_update(revision, content).unwrap();
            assert!(response.changed && response.snapshot.is_some());
            assert!(response.progress.is_none());
        }
        drop(engine);
        let reopened = Engine::open(&db, None).unwrap();
        let response = reopened
            .snapshot_update(Some(&old.revision), Some(&old.content_revision))
            .unwrap();
        assert!(response.changed && response.snapshot.is_some());
        assert_ne!(response.content_revision, old.content_revision);
    }

    #[test]
    fn conditional_snapshot_ffi_returns_typed_full_unchanged_and_progress_envelopes() {
        let temp = tempfile::tempdir().unwrap();
        let path = CString::new(temp.path().join("library.sqlite").to_str().unwrap()).unwrap();
        let handle = FfiHandle(unsafe { ct_open(path.as_ptr(), None) });
        assert!(!handle.0.is_null());
        let full = ffi_response(handle.0, c"{\"action\":\"snapshot_if_changed\"}");
        assert_eq!(full["ok"], true);
        assert!(full["data"].get("snapshot").is_some());
        assert!(full["data"].get("progress").is_none());
        let request = CString::new(
            json!({
                "action":"snapshot_if_changed",
                "after_revision": full["data"]["revision"],
                "after_content_revision": full["data"]["content_revision"]
            })
            .to_string(),
        )
        .unwrap();
        let unchanged = ffi_response(handle.0, &request);
        assert_eq!(unchanged["data"]["changed"], false);
        assert!(unchanged["data"].get("snapshot").is_none());
        assert!(unchanged["data"].get("progress").is_none());
        let engine = unsafe { &*handle.0 };
        engine.runtime.lock().unwrap().error = Some("Disposable error".into());
        let progress = ffi_response(handle.0, &request);
        assert_eq!(progress["data"]["changed"], true);
        assert!(progress["data"].get("snapshot").is_none());
        assert_eq!(progress["data"]["progress"]["error"], "Disposable error");
        assert_eq!(
            progress["data"],
            engine
                .request(serde_json::from_slice(request.to_bytes()).unwrap())
                .unwrap()
        );
    }

    #[test]
    fn lost_event_reconciliation_persists_lower_cursor_and_all_roots_across_restart() {
        let (temp, engine, roots) = foreground_fixture(2);
        engine.scan_paused.store(true, Ordering::Release);
        engine
            .request(json!({"action":"cursor","value":1000}))
            .unwrap();
        assert_eq!(
            engine
                .request(json!({"action":"reconcile_events","value":7}))
                .unwrap()["cursor"],
            7
        );
        assert_eq!(
            engine
                .request(json!({"action":"cursor","value":8}))
                .unwrap()["cursor"],
            8
        );
        drop(engine);
        let restarted = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        assert_eq!(
            restarted.request(json!({"action":"cursor"})).unwrap()["cursor"],
            8
        );
        let store = restarted.store.lock().unwrap();
        for root in roots {
            assert!(store.incomplete(&root.id).unwrap());
            let pending: bool = store
                .conn
                .query_row(
                    "SELECT EXISTS(SELECT 1 FROM pending_scopes WHERE root_id=?1 AND path=?2)",
                    rusqlite::params![root.id, root.path.to_str().unwrap()],
                    |row| row.get(0),
                )
                .unwrap();
            assert!(
                pending,
                "Every root must be journaled before the lower cursor is acknowledged"
            );
        }
    }

    #[test]
    fn lost_event_reconciliation_never_acknowledges_partial_database_failure() {
        let (_temp, engine, _roots) = foreground_fixture(2);
        engine.scan_paused.store(true, Ordering::Release);
        engine
            .request(json!({"action":"cursor","value":1000}))
            .unwrap();
        let pending_before: u64 = engine
            .store
            .lock()
            .unwrap()
            .conn
            .query_row("SELECT count(*) FROM pending_scopes", [], |row| row.get(0))
            .unwrap();
        engine
            .store
            .lock()
            .unwrap()
            .conn
            .execute_batch(
                "CREATE TEMP TRIGGER reject_event_reset BEFORE UPDATE ON event_cursor
             BEGIN SELECT RAISE(ABORT,'disposable cursor failure'); END;",
            )
            .unwrap();
        assert!(
            engine
                .request(json!({"action":"reconcile_events","value":7}))
                .is_err()
        );
        assert_eq!(
            engine.request(json!({"action":"cursor"})).unwrap()["cursor"],
            1000
        );
        let pending_after: u64 = engine
            .store
            .lock()
            .unwrap()
            .conn
            .query_row("SELECT count(*) FROM pending_scopes", [], |row| row.get(0))
            .unwrap();
        assert_eq!(pending_after, pending_before);
    }

    #[test]
    fn ffi_snapshot_and_error_envelopes_remain_compatible() {
        let temp = tempfile::tempdir().unwrap();
        let path = CString::new(temp.path().join("library.sqlite").to_str().unwrap()).unwrap();
        let handle = FfiHandle(unsafe { ct_open(path.as_ptr(), None) });
        assert!(!handle.0.is_null());
        let engine = unsafe { &*handle.0 };
        {
            let mut runtime = engine.runtime.lock().unwrap();
            runtime.stats.entries = u64::MAX;
            runtime.stats.message = "Disposable snapshot: café\n\0".into();
        }
        let expected_data = engine.request(json!({"action":"snapshot"})).unwrap();
        assert_eq!(
            ffi_response(handle.0, c"{\"action\":\"snapshot\"}"),
            json!({"ok":true,"data":expected_data})
        );
        assert_eq!(
            ffi_response(std::ptr::null(), c"{\"action\":\"snapshot\"}"),
            json!({"ok":false,"error":"Invalid engine handle"})
        );
        assert_eq!(
            parse_ffi_response(unsafe { ct_request(handle.0, std::ptr::null()) }),
            json!({"ok":false,"error":"Invalid engine handle"})
        );
        for request in [
            c"{}",
            c"null",
            c"[]",
            c"{\"action\":null}",
            c"{\"action\":\"unknown\"}",
        ] {
            let error = engine
                .request(serde_json::from_slice(request.to_bytes()).unwrap())
                .unwrap_err();
            assert_eq!(
                ffi_response(handle.0, request),
                json!({"ok":false,"error":error})
            );
        }
        let progress = engine
            .request(json!({"action":"cleanup_progress"}))
            .unwrap();
        assert_eq!(
            ffi_response(handle.0, c"{\"action\":\"cleanup_progress\"}"),
            json!({"ok":true,"data":progress})
        );
        let invalid_json = serde_json::from_str::<Value>("{").unwrap_err().to_string();
        assert_eq!(
            ffi_response(handle.0, c"{"),
            json!({"ok":false,"error":invalid_json})
        );
        let invalid_utf8 = c"\xff";
        assert_eq!(
            ffi_response(handle.0, invalid_utf8),
            json!({"ok":false,"error":invalid_utf8.to_str().unwrap_err().to_string()})
        );
        assert!(engine.snapshot().unwrap().roots.is_empty());
        assert!(engine.snapshot().unwrap().history.is_empty());
        assert_eq!(engine.snapshot().unwrap().wallet.credited_bytes, 0);
        // A snapshot read failure must use the same error envelope as other
        // commands, not accidentally serialize an empty or partial snapshot.
        engine
            .store
            .lock()
            .unwrap()
            .conn
            .execute("INSERT INTO roots VALUES('invalid','/synthetic','{')", [])
            .unwrap();
        let error = engine.request(json!({"action":"snapshot"})).unwrap_err();
        assert_eq!(
            ffi_response(handle.0, c"{\"action\":\"snapshot\"}"),
            json!({"ok":false,"error":error})
        );
    }

    #[test]
    fn ffi_snapshot_preserves_populated_values_and_large_integer_precision() {
        let temp = tempfile::tempdir().unwrap();
        let path = CString::new(temp.path().join("library.sqlite").to_str().unwrap()).unwrap();
        let handle = FfiHandle(unsafe { ct_open(path.as_ptr(), None) });
        assert!(!handle.0.is_null());
        let engine = unsafe { &*handle.0 };
        let large = 9_007_199_254_740_993u64;
        let identity = Identity {
            device: u64::MAX,
            inode: large,
            mode: 0o40700,
            size: large,
            modified_ns: i64::MIN,
            changed_ns: i64::MAX,
        };
        let root = Root {
            id: "synthetic".into(),
            path: "/synthetic/ffi-snapshot".into(),
            kind: "folder".into(),
            identity: identity.clone(),
        };
        let candidate = Candidate {
            id: "synthetic-candidate".into(),
            root_id: root.id.clone(),
            path: root.path.join(".venv"),
            title: "Disposable café · 🪙\n\"quoted\"\0".into(),
            kind: "venv".into(),
            logical_bytes: u64::MAX,
            allocated_bytes: large,
            file_count: large,
            modified_ns: i64::MIN,
            explanation: "Synthetic serializer fixture, never scanned or deleted".into(),
            consequence: String::new(),
            eligible_permanent: false,
            blocked_reason: None,
            identity,
            fingerprint: "synthetic".into(),
            evidence: "synthetic".into(),
            suggestion_eligible: true,
            provisional: false,
        };
        let receipt = Receipt {
            id: "synthetic-receipt".into(),
            path: candidate.path.to_str().unwrap().into(),
            title: candidate.title.clone(),
            operation: "permanent".into(),
            outcome: "removed".into(),
            detail: "Synthetic serializer fixture; no real cleanup occurred".into(),
            created_at: i64::MIN,
            reported_bytes: u64::MAX,
            observed_bytes: large,
            credited_bytes: large,
            coins: large,
            trash_path: None,
            can_restore: false,
            seq: None,
        };
        {
            let mut store = engine.store.lock().unwrap();
            store.add_root(&root).unwrap();
            store
                .save_batch(&ScanBatch {
                    candidates: vec![candidate],
                    stats: ScanStats::default(),
                })
                .unwrap();
            store
                .conn
                .execute(
                    "INSERT INTO operations VALUES(?1,'{}','{}',?2,NULL,NULL,'removed')",
                    rusqlite::params![receipt.id, serde_json::to_string(&receipt).unwrap()],
                )
                .unwrap();
            store
                .conn
                .execute(
                    "UPDATE wallet SET collected=?1,credited=?1 WHERE id=1",
                    [large],
                )
                .unwrap();
            store.keep("/synthetic/kept-sibling", true).unwrap();
        }
        {
            let mut runtime = engine.runtime.lock().unwrap();
            runtime.stats.entries = u64::MAX;
            runtime.stats.first_finding_ms = Some(large);
            runtime.restored_foreground = Some(ForegroundScan {
                active: false,
                stats: runtime.stats.clone(),
            });
        }
        let expected = engine.request(json!({"action":"snapshot"})).unwrap();
        let actual = ffi_response(handle.0, c"{\"action\":\"snapshot\"}");
        assert_eq!(actual, json!({"ok":true,"data":expected}));
        let data = &actual["data"];
        assert_eq!(
            data["candidates"][0]["logical_bytes"].as_u64(),
            Some(u64::MAX)
        );
        assert_eq!(
            data["candidates"][0]["allocated_bytes"].as_u64(),
            Some(large)
        );
        assert_eq!(data["history"][0]["created_at"].as_i64(), Some(i64::MIN));
        assert_eq!(data["wallet"]["credited_bytes"].as_u64(), Some(large));
        assert!(data["history"][0].get("seq").is_none());
        assert!(data["history"][0]["trash_path"].is_null());
        assert!(data["error"].is_null());
    }

    fn debounce_worker(
        engine: &Arc<Engine>,
        deadline: Instant,
    ) -> (
        std::sync::mpsc::Receiver<Instant>,
        std::sync::mpsc::Receiver<()>,
        std::thread::JoinHandle<()>,
    ) {
        debounce_worker_with_urgency(
            engine,
            deadline,
            engine.discovery_urgency.load(Ordering::Acquire),
        )
    }

    fn debounce_worker_with_urgency(
        engine: &Arc<Engine>,
        deadline: Instant,
        urgency: u64,
    ) -> (
        std::sync::mpsc::Receiver<Instant>,
        std::sync::mpsc::Receiver<()>,
        std::thread::JoinHandle<()>,
    ) {
        let (waiting_send, waiting) = std::sync::mpsc::channel();
        let (finished_send, finished) = std::sync::mpsc::channel();
        *engine.debounce_wait_observer.lock().unwrap() = Some(waiting_send);
        engine.scanning.store(true, Ordering::Release);
        engine.busy.store(true, Ordering::Release);
        let engine = Arc::clone(engine);
        let worker = std::thread::spawn(move || {
            engine.wait_for_debounce(deadline, urgency);
            {
                let _runtime = engine.runtime.lock().unwrap();
                engine.finish_worker();
            }
            let _ = finished_send.send(());
        });
        (waiting, finished, worker)
    }

    #[test]
    fn debounce_skips_wait_for_expired_deadline_or_existing_cancellation() {
        for cancelled in [false, true] {
            let temp = tempfile::tempdir().unwrap();
            let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
            let deadline = if cancelled {
                engine.cancel_scan();
                Instant::now() + Duration::from_secs(30)
            } else {
                Instant::now() - Duration::from_secs(1)
            };
            let (waiting, finished, worker) = debounce_worker(&engine, deadline);
            finished
                .recv_timeout(Duration::from_secs(2))
                .expect("An expired or cancelled debounce must not wait");
            worker.join().unwrap();
            assert!(waiting.try_recv().is_err());
            assert!(!engine.scanning.load(Ordering::Acquire));
        }
    }

    #[test]
    fn interactive_hint_is_required_and_inert_without_discovery_work() {
        let (_temp, engine, _roots) = foreground_fixture(1);
        let before = serde_json::to_value(engine.snapshot().unwrap()).unwrap();
        let urgency = engine.discovery_urgency.load(Ordering::Acquire);
        for request in [
            json!({"action":"set_interactive"}),
            json!({"action":"set_interactive","active":null}),
            json!({"action":"set_interactive","active":"true"}),
        ] {
            assert_eq!(
                engine.request(request).unwrap_err(),
                "set_interactive requires a boolean active"
            );
        }
        assert!(!engine.interactive.load(Ordering::Acquire));
        assert_eq!(
            engine
                .request(json!({"action":"set_interactive","active":true}))
                .unwrap(),
            json!({"ok":true})
        );
        let opened_urgency = engine.discovery_urgency.load(Ordering::Acquire);
        assert_ne!(opened_urgency, urgency);
        // Repeated visibility delivery is idempotent and cannot keep changing a
        // future worker's captured urgency.
        engine
            .request(json!({"action":"set_interactive","active":true}))
            .unwrap();
        assert_eq!(
            engine.discovery_urgency.load(Ordering::Acquire),
            opened_urgency
        );
        engine
            .request(json!({"action":"set_interactive","active":false}))
            .unwrap();
        assert!(!engine.interactive.load(Ordering::Acquire));
        assert_eq!(
            engine.discovery_urgency.load(Ordering::Acquire),
            opened_urgency
        );
        assert!(!engine.busy.load(Ordering::Acquire));
        assert!(!engine.scanning.load(Ordering::Acquire));
        assert!(!engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert!(engine.runtime.lock().unwrap().foreground.is_none());
        assert_eq!(
            serde_json::to_value(engine.snapshot().unwrap()).unwrap(),
            before,
            "An advisory visibility hint must not alter grants, foreground state, findings or the ledger"
        );
    }

    #[test]
    fn becoming_interactive_wakes_an_existing_background_wait() {
        let (_temp, engine, _roots) = foreground_fixture(0);
        let before = serde_json::to_value(engine.snapshot().unwrap()).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        engine
            .request(json!({"action":"set_interactive","active":true}))
            .unwrap();
        let woke = finished.recv_timeout(Duration::from_secs(2)).is_ok();
        if !woke {
            engine.cancel_scan();
        }
        worker.join().unwrap();
        assert!(
            woke,
            "Opening the app must wake an existing background batch"
        );
        assert!(engine.interactive.load(Ordering::Acquire));
        assert!(!engine.busy.load(Ordering::Acquire));
        assert!(!engine.scanning.load(Ordering::Acquire));
        assert!(!engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert_eq!(
            serde_json::to_value(engine.snapshot().unwrap()).unwrap(),
            before,
            "Waking an empty debounce must not manufacture foreground work or ledger state"
        );
    }

    #[test]
    fn closing_preserves_the_current_deadline_and_batches_later_workers() {
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let scope = root.path.join("child");
        engine
            .request(json!({"action":"set_interactive","active":true}))
            .unwrap();
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&root.id, &scope)
            .unwrap();
        let (interactive_send, interactive_waiting) = std::sync::mpsc::channel();
        *engine.debounce_wait_observer.lock().unwrap() = Some(interactive_send);
        let interactive_started = Instant::now();
        engine.launch_scan(ScanLaunch::Background).unwrap();
        let interactive_deadline = interactive_waiting
            .recv_timeout(Duration::from_secs(2))
            .unwrap();

        engine
            .request(json!({"action":"set_interactive","active":false}))
            .unwrap();
        engine.wake_discovery();
        assert_eq!(
            interactive_waiting
                .recv_timeout(Duration::from_secs(2))
                .unwrap(),
            interactive_deadline,
            "Closing must not replace or extend a deadline already captured while visible"
        );
        assert!(engine.scanning.load(Ordering::Acquire));
        let interactive_window =
            interactive_deadline.saturating_duration_since(interactive_started);
        engine.cancel_scan();
        wait_for_discovery_idle(&engine);
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());

        // Resume the still-durable scope as a later background launch, not an
        // explicit user request that would intentionally bypass batching.
        engine.scan_paused.store(false, Ordering::Release);
        let (closed_send, closed_waiting) = std::sync::mpsc::channel();
        *engine.debounce_wait_observer.lock().unwrap() = Some(closed_send);
        let closed_started = Instant::now();
        engine.launch_scan(ScanLaunch::Background).unwrap();
        let closed_deadline = closed_waiting.recv_timeout(Duration::from_secs(2)).unwrap();
        let closed_window = closed_deadline.saturating_duration_since(closed_started);
        assert!(
            closed_window > interactive_window + Duration::from_millis(150),
            "A later hidden worker must retain a materially longer coalescing window"
        );
        assert!(engine.scanning.load(Ordering::Acquire));
        engine.cancel_scan();
        wait_for_discovery_idle(&engine);
        assert!(engine.runtime.lock().unwrap().foreground.is_none());
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
        let snapshot = engine.snapshot().unwrap();
        assert!(snapshot.history.is_empty());
        assert_eq!(snapshot.wallet.credited_bytes, 0);
        assert_eq!(
            fs::read(scope.join("preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn explicit_scan_and_resume_interrupt_an_existing_debounce() {
        for (action, already_scanning) in [("scan", false), ("resume", false), ("scan", true)] {
            let (_temp, engine, roots) = foreground_fixture(1);
            let scope = roots[0].path.join("child");
            engine
                .store
                .lock()
                .unwrap()
                .enqueue_scope(&roots[0].id, &scope)
                .unwrap();
            if already_scanning {
                let mut runtime = engine.runtime.lock().unwrap();
                runtime.foreground_generation = 1;
                runtime.foreground = Some(ForegroundRequest::new(
                    runtime.foreground_generation,
                    &roots,
                    engine.store.lock().unwrap().foreground_context().unwrap(),
                ));
                engine
                    .store
                    .lock()
                    .unwrap()
                    .enqueue_scope(&roots[0].id, &roots[0].path)
                    .unwrap();
            }
            let deadline = Instant::now() + Duration::from_secs(30);
            let (waiting, finished, worker) = debounce_worker(&engine, deadline);
            assert_eq!(
                waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
                deadline
            );
            let response = engine.request(json!({"action":action})).unwrap();
            assert_eq!(response["already_scanning"] == true, already_scanning);
            let woke = finished.recv_timeout(Duration::from_secs(2)).is_ok();
            if !woke {
                // Release the worker before failing so this regression leaves
                // no live work or open disposable library behind.
                engine.cancel_scan();
            }
            worker.join().unwrap();
            assert!(
                woke,
                "Explicit {action} must interrupt an existing background wait"
            );
            assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
            engine.request(json!({"action":"resume"})).unwrap();
            wait_for_discovery_idle(&engine);
            let snapshot = engine.snapshot().unwrap();
            assert!(!snapshot.scanning && snapshot.error.is_none());
            assert_eq!(snapshot.stats.errors, 0);
            assert!(snapshot.history.is_empty());
            assert_eq!(snapshot.wallet.credited_bytes, 0);
            assert_eq!(
                fs::read(scope.join("preserve.txt")).unwrap(),
                b"disposable source"
            );
        }
    }

    #[test]
    fn urgency_before_wait_is_remembered_without_bypassing_a_later_worker() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let urgency = engine.discovery_urgency.load(Ordering::Acquire);
        // Model the request arriving after worker acquisition but before the
        // spawned thread reaches its condition wait.
        engine.request(json!({"action":"resume"})).unwrap();
        assert_ne!(engine.discovery_urgency.load(Ordering::Acquire), urgency);
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker_with_urgency(&engine, deadline, urgency);
        let woke = finished.recv_timeout(Duration::from_secs(2)).is_ok();
        if !woke {
            engine.cancel_scan();
        }
        worker.join().unwrap();
        assert!(woke, "A request before the wait must remain observable");
        assert!(waiting.try_recv().is_err());

        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        assert!(finished.try_recv().is_err());
        engine.cancel_scan();
        finished.recv_timeout(Duration::from_secs(2)).unwrap();
        worker.join().unwrap();
    }

    #[test]
    fn background_and_unkeep_preserve_an_existing_debounce() {
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let scope = root.path.join("child");
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&root.id, &scope)
            .unwrap();
        let urgency = engine.discovery_urgency.load(Ordering::Acquire);
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        dirty_scope(&engine, root, &scope);
        engine
            .request(json!({"action":"unkeep", "path":scope}))
            .unwrap();
        assert_eq!(engine.discovery_urgency.load(Ordering::Acquire), urgency);
        // A spurious notification provides a handshake proving that both
        // actions left the original deadline and wait predicate unchanged.
        engine.wake_discovery();
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        assert!(finished.try_recv().is_err());
        engine.cancel_scan();
        finished.recv_timeout(Duration::from_secs(2)).unwrap();
        worker.join().unwrap();
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert_eq!(
            fs::read(scope.join("preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn full_root_promotion_wakes_a_waiting_background_worker() {
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&root.id, &root.path.join("child"))
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        assert!(engine.snapshot().unwrap().foreground_scan.is_none());
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&root.id, &root.path)
            .unwrap();
        engine.launch_scan(ScanLaunch::Background).unwrap();
        let woke = finished.recv_timeout(Duration::from_secs(2)).is_ok();
        if !woke {
            engine.cancel_scan();
        }
        worker.join().unwrap();
        assert!(
            woke,
            "Promoting pending full-root work must bypass an existing wait"
        );
        assert!(engine.snapshot().unwrap().foreground_scan.unwrap().active);
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());

        // A newly acquired worker also skips batching for the captured full
        // request. Only the actual traversal may acknowledge the pending root.
        let (waiting_send, waiting) = std::sync::mpsc::channel();
        *engine.debounce_wait_observer.lock().unwrap() = Some(waiting_send);
        let steps = watch_discovery(&engine);
        engine.launch_scan(ScanLaunch::Background).unwrap();
        let release = finish_discovery_job(&steps, &root.path);
        assert!(waiting.try_recv().is_err());
        release.send(()).unwrap();
        wait_for_discovery_idle(&engine);
        let snapshot = engine.snapshot().unwrap();
        let foreground = snapshot.foreground_scan.unwrap();
        assert!(!foreground.active && foreground.stats.complete);
        assert_eq!(foreground.stats.entries, 3);
        assert!(!engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert!(snapshot.history.is_empty());
        assert_eq!(snapshot.wallet.credited_bytes, 0);
    }

    #[test]
    fn debounce_cancellation_wakes_at_the_wait_boundary() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        // The handshake is sent while parked is held, immediately before the
        // atomic wait. Cancellation must not lose this boundary notification.
        engine.cancel_scan();
        finished
            .recv_timeout(Duration::from_secs(2))
            .expect("Cancellation did not interrupt the debounce wait");
        worker.join().unwrap();
        assert!(engine.scan_paused.load(Ordering::Acquire));
        assert!(!engine.scanning.load(Ordering::Acquire));
    }

    #[test]
    fn debounce_spurious_notifications_preserve_the_original_deadline() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        for _ in 0..3 {
            assert_eq!(
                waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
                deadline
            );
            assert!(finished.try_recv().is_err());
            engine.wake_discovery();
        }
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        engine.cancel_scan();
        finished.recv_timeout(Duration::from_secs(2)).unwrap();
        worker.join().unwrap();
    }

    #[test]
    fn debounce_parks_for_mutation_and_resumes_the_same_deadline() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        let (parked_send, parked) = std::sync::mpsc::channel();
        let (release, released) = std::sync::mpsc::channel();
        let mutating = Arc::clone(&engine);
        let mutation = std::thread::spawn(move || {
            let guard = mutating.begin_mutation().unwrap();
            parked_send.send(*mutating.parked.lock().unwrap()).unwrap();
            // Dropping the release sender also releases the guard on failure.
            let _ = released.recv();
            drop(guard);
        });
        assert!(
            parked
                .recv_timeout(Duration::from_secs(2))
                .expect("Mutation did not park the debouncing worker")
        );
        assert!(engine.pause_requested.load(Ordering::Acquire));
        assert!(finished.try_recv().is_err());
        release.send(()).unwrap();
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        engine.cancel_scan();
        finished.recv_timeout(Duration::from_secs(2)).unwrap();
        mutation.join().unwrap();
        worker.join().unwrap();
        assert!(!engine.pause_requested.load(Ordering::Acquire));
        assert!(!*engine.parked.lock().unwrap());
        assert!(!engine.scanning.load(Ordering::Acquire));
    }

    #[test]
    fn explicit_resume_waits_for_mutation_then_bypasses_debounce() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        let (waiting, finished, worker) = debounce_worker(&engine, deadline);
        assert_eq!(
            waiting.recv_timeout(Duration::from_secs(2)).unwrap(),
            deadline
        );
        let (parked_send, parked) = std::sync::mpsc::channel();
        let (release, released) = std::sync::mpsc::channel();
        let mutating = Arc::clone(&engine);
        let mutation = std::thread::spawn(move || {
            let guard = mutating.begin_mutation().unwrap();
            parked_send.send(*mutating.parked.lock().unwrap()).unwrap();
            let _ = released.recv();
            drop(guard);
        });
        assert!(parked.recv_timeout(Duration::from_secs(2)).unwrap());
        engine.request(json!({"action":"resume"})).unwrap();
        assert!(engine.pause_requested.load(Ordering::Acquire));
        assert!(*engine.parked.lock().unwrap());
        assert!(finished.try_recv().is_err());
        release.send(()).unwrap();
        let woke = finished.recv_timeout(Duration::from_secs(2)).is_ok();
        if !woke {
            engine.cancel_scan();
        }
        worker.join().unwrap();
        mutation.join().unwrap();
        assert!(
            woke,
            "Resume must skip the remaining wait after mutation releases it"
        );
        assert!(!engine.pause_requested.load(Ordering::Acquire));
        assert!(!engine.scanning.load(Ordering::Acquire));
        assert!(!engine.cleaning.load(Ordering::Acquire));
    }

    struct DiscoveryStep {
        stage: DiscoveryStage,
        path: PathBuf,
        release: std::sync::mpsc::Sender<()>,
    }

    fn watch_discovery(engine: &Arc<Engine>) -> std::sync::mpsc::Receiver<DiscoveryStep> {
        let (send, receive) = std::sync::mpsc::channel();
        *engine.discovery_observer.lock().unwrap() = Some(Arc::new(move |stage, _, path| {
            if stage == DiscoveryStage::Scanned {
                return;
            }
            let (release, released) = std::sync::mpsc::channel();
            if send
                .send(DiscoveryStep {
                    stage,
                    path: path.into(),
                    release,
                })
                .is_ok()
            {
                // A dropped test receiver/release sender also releases the worker.
                let _ = released.recv_timeout(Duration::from_secs(5));
            }
        }));
        receive
    }

    fn discovery_step(
        steps: &std::sync::mpsc::Receiver<DiscoveryStep>,
        stage: DiscoveryStage,
        path: &Path,
    ) -> std::sync::mpsc::Sender<()> {
        let step = steps
            .recv_timeout(Duration::from_secs(5))
            .expect("Discovery did not reach the expected boundary");
        assert_eq!(step.stage, stage);
        assert_eq!(step.path, path);
        step.release
    }

    fn finish_discovery_job(
        steps: &std::sync::mpsc::Receiver<DiscoveryStep>,
        path: &Path,
    ) -> std::sync::mpsc::Sender<()> {
        discovery_step(steps, DiscoveryStage::Claimed, path)
            .send(())
            .unwrap();
        discovery_step(steps, DiscoveryStage::Began, path)
            .send(())
            .unwrap();
        discovery_step(steps, DiscoveryStage::Finished, path)
    }

    fn wait_for_discovery_idle(engine: &Engine) {
        let parked = engine.parked.lock().unwrap();
        let (parked, timeout) = engine
            .pause_changed
            .wait_timeout_while(parked, Duration::from_secs(5), |_| {
                engine.scanning.load(Ordering::Acquire)
            })
            .unwrap();
        drop(parked);
        assert!(!timeout.timed_out(), "Discovery did not stop");
    }

    fn foreground_fixture(count: usize) -> (tempfile::TempDir, Arc<Engine>, Vec<Root>) {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let engine = Engine::open(&base.join("library.sqlite"), None).unwrap();
        let roots = (0..count)
            .map(|index| {
                let path = base.join(format!("Root{index}"));
                fs::create_dir_all(path.join("child")).unwrap();
                fs::write(path.join("child/preserve.txt"), b"disposable source").unwrap();
                serde_json::from_value(
                    engine
                        .request(json!({
                            "action":"authorize", "path":path, "kind":"folder"
                        }))
                        .unwrap(),
                )
                .unwrap()
            })
            .collect();
        (temp, engine, roots)
    }

    // These coordinator tests exercise the real process-wide admission pool.
    // Independent unit-test engines must not compete for its production quota.
    static ISOLATED_FIXTURE_LOCK: Mutex<()> = Mutex::new(());

    fn isolated_helper_fixture(directory: &Path, roots: &[Root], stalled: usize) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let helper = directory.join("disposable-scan-helper");
        let mut script = String::from("#!/bin/sh\ninput=$(/bin/cat)\ncase \"$input\" in\n");
        for (index, root) in roots.iter().enumerate() {
            // Root IDs are generated identifiers, not user-supplied shell text.
            assert!(
                root.id
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            );
            let mut frames = scan_worker::encode_json_frame(&scan_worker::ScanEvent::Resolved {
                path: root.path.clone(),
                cargo_lock: false,
            })
            .unwrap();
            frames.extend(
                scan_worker::encode_json_frame(&scan_worker::ScanEvent::Finished {
                    stats: ScanStats {
                        entries: 7,
                        complete: true,
                        message: "Fixture scope complete".into(),
                        ..Default::default()
                    },
                    recent_files: None,
                })
                .unwrap(),
            );
            let escaped = frames
                .iter()
                .map(|byte| format!("\\{byte:03o}"))
                .collect::<String>();
            script.push_str(&format!("*'\"id\":\"{}\"'*)\n", root.id));
            if index == stalled {
                script.push_str("/bin/sleep 4\n");
            }
            script.push_str(&format!("printf '{escaped}'\n;;\n"));
        }
        script.push_str("*) exit 9;;\nesac\n");
        fs::write(&helper, script).unwrap();
        fs::set_permissions(&helper, fs::Permissions::from_mode(0o700)).unwrap();
        helper
    }

    fn isolated_failure_helper_fixture(
        directory: &Path,
        failed: &Root,
        sibling: &Root,
        malformed: bool,
    ) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let helper = directory.join(if malformed {
            "disposable-malformed-scan-helper"
        } else {
            "disposable-failed-scan-helper"
        });
        assert!(
            failed
                .id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        );
        let mut outputs = Vec::new();
        let mut failed_output = scan_worker::encode_json_frame(&scan_worker::ScanEvent::Resolved {
            path: failed.path.clone(),
            cargo_lock: false,
        })
        .unwrap();
        if malformed {
            failed_output.extend_from_slice(&[0, 0, 0, 3, b'n', b'o', b'p']);
        } else {
            failed_output.extend(
                scan_worker::encode_json_frame(&scan_worker::ScanEvent::Failed(
                    "disposable helper failure".into(),
                ))
                .unwrap(),
            );
        }
        outputs.push((failed, failed_output));
        let mut sibling_output =
            scan_worker::encode_json_frame(&scan_worker::ScanEvent::Resolved {
                path: sibling.path.clone(),
                cargo_lock: false,
            })
            .unwrap();
        sibling_output.extend(
            scan_worker::encode_json_frame(&scan_worker::ScanEvent::Finished {
                stats: ScanStats {
                    entries: 7,
                    complete: true,
                    ..Default::default()
                },
                recent_files: None,
            })
            .unwrap(),
        );
        outputs.push((sibling, sibling_output));
        let mut cases = String::new();
        for (root, output) in outputs {
            let escaped = output
                .iter()
                .map(|byte| format!("\\{byte:03o}"))
                .collect::<String>();
            let wait = if root.id == sibling.id {
                let gate = directory.join("release-sibling");
                format!(
                    "attempt=0\nwhile [ ! -f '{}' ]; do\nattempt=$((attempt + 1))\n[ \"$attempt\" -lt 250 ] || exit 10\n/bin/sleep 0.01\ndone\n",
                    gate.to_str().unwrap().replace('\'', "'\\''")
                )
            } else {
                String::new()
            };
            cases.push_str(&format!(
                "*'\"id\":\"{}\"'*)\n{wait}printf '{escaped}';;\n",
                root.id
            ));
        }
        let script =
            format!("#!/bin/sh\ninput=$(/bin/cat)\ncase \"$input\" in\n{cases}*) exit 9;;\nesac\n");
        fs::write(&helper, script).unwrap();
        fs::set_permissions(&helper, fs::Permissions::from_mode(0o700)).unwrap();
        helper
    }

    #[test]
    fn isolated_helper_failure_requeues_without_retry_storm_and_survives_resume() {
        let _serial = ISOLATED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for malformed in [false, true] {
            let (temp, engine, roots) = foreground_fixture(3);
            let helper =
                isolated_failure_helper_fixture(temp.path(), &roots[0], &roots[1], malformed);
            *engine.scan_helper_fixture.lock().unwrap() = Some(helper);
            engine.request(json!({"action":"scan"})).unwrap();
            let deadline = Instant::now() + Duration::from_secs(2);
            loop {
                let runtime = engine.runtime.lock().unwrap();
                let scan = runtime.foreground.as_ref().unwrap();
                if scan.roots[&roots[0].id].terminal {
                    assert!(!scan.roots[&roots[1].id].terminal);
                    assert!(scan.roots[&roots[2].id].started_ms.is_none());
                    break;
                }
                drop(runtime);
                assert!(Instant::now() < deadline, "Helper failure was not received");
                std::thread::sleep(Duration::from_millis(5));
            }
            fs::write(temp.path().join("release-sibling"), b"release").unwrap();
            wait_for_discovery_idle(&engine);
            let snapshot = engine.snapshot().unwrap();
            let foreground = snapshot.foreground_scan.unwrap();
            assert!(!foreground.active);
            assert!(!snapshot.stats.complete);
            assert!(snapshot.stats.errors > 0);
            assert!(
                foreground
                    .stats
                    .message
                    .contains("pending scopes remain for Resume")
            );
            {
                let store = engine.store.lock().unwrap();
                assert!(!store.has_active_scopes().unwrap());
                assert!(
                    !store
                        .conn
                        .query_row::<bool, _, _>(
                            "SELECT EXISTS(SELECT 1 FROM refreshes)",
                            [],
                            |row| row.get(0)
                        )
                        .unwrap()
                );
                assert!(store.has_pending_scopes().unwrap());
                let pending: Vec<String> = store
                    .conn
                    .prepare("SELECT path FROM pending_scopes ORDER BY path")
                    .unwrap()
                    .query_map([], |row| row.get(0))
                    .unwrap()
                    .collect::<std::result::Result<_, _>>()
                    .unwrap();
                assert_eq!(
                    pending,
                    vec![
                        roots[0].path.to_string_lossy().to_string(),
                        roots[2].path.to_string_lossy().to_string()
                    ]
                );
                assert_eq!(store.latest_stats().unwrap().entries, 7);
                assert!(
                    store
                        .load_foreground_summary()
                        .unwrap()
                        .unwrap()
                        .stats
                        .message
                        .contains("pending scopes remain for Resume")
                );
                assert!(store.history().unwrap().is_empty());
                assert_eq!(store.wallet().unwrap().credited_bytes, 0);
            }

            // The queued failed root survives process restart and a later
            // explicit Resume completes through a healthy isolated helper.
            let database = temp.path().join("library.sqlite");
            drop(engine);
            let reopened = Engine::open(&database, None).unwrap();
            assert!(reopened.store.lock().unwrap().has_pending_scopes().unwrap());
            *reopened.scan_helper_fixture.lock().unwrap() =
                Some(isolated_helper_fixture(temp.path(), &roots, usize::MAX));
            reopened.request(json!({"action":"resume"})).unwrap();
            wait_for_discovery_idle(&reopened);
            let completed = reopened.snapshot().unwrap();
            assert!(completed.stats.complete);
            assert_eq!(completed.stats.errors, 0);
            assert_eq!(completed.stats.entries, 14);
            assert!(completed.foreground_scan.unwrap().stats.complete);
            let store = reopened.store.lock().unwrap();
            assert!(!store.has_pending_scopes().unwrap());
            assert!(!store.has_active_scopes().unwrap());
            assert!(
                !store
                    .conn
                    .query_row::<bool, _, _>(
                        "SELECT EXISTS(SELECT 1 FROM incomplete_roots)",
                        [],
                        |row| row.get(0)
                    )
                    .unwrap()
            );
        }
    }

    #[test]
    fn isolated_helper_start_failure_preserves_replay_and_persists_resume_summary() {
        let _serial = ISOLATED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for failure in ["start", "before-refresh", "cancel"] {
            let before_refresh = failure == "before-refresh";
            let (temp, engine, roots) = foreground_fixture(1);
            // A trusted-path rejection is a synchronous start failure after
            // begin-refresh. The trigger also covers a claim abandoned before
            // a refresh/receiver exists; neither path may strand the claim.
            *engine.scan_helper_fixture.lock().unwrap() = Some(if failure == "cancel" {
                isolated_helper_fixture(temp.path(), &roots, 0)
            } else {
                temp.path().join("missing-helper")
            });
            if before_refresh {
                engine.store.lock().unwrap().conn.execute_batch(
                    "CREATE TEMP TRIGGER fail_isolated_begin BEFORE INSERT ON refreshes BEGIN SELECT RAISE(ABORT,'disposable isolated begin failure'); END;",
                ).unwrap();
            }
            engine.request(json!({"action":"scan"})).unwrap();
            if failure == "cancel" {
                let deadline = Instant::now() + Duration::from_secs(2);
                while !engine.store.lock().unwrap().has_active_scopes().unwrap() {
                    assert!(Instant::now() < deadline);
                    std::thread::sleep(Duration::from_millis(5));
                }
                engine.cancel_scan();
            }
            wait_for_discovery_idle(&engine);
            {
                let store = engine.store.lock().unwrap();
                assert!(!store.has_active_scopes().unwrap());
                assert!(store.has_pending_scopes().unwrap());
                let pending: String = store
                    .conn
                    .query_row("SELECT path FROM pending_scopes", [], |row| row.get(0))
                    .unwrap();
                assert_eq!(pending, roots[0].path.to_str().unwrap());
                let summary = store.load_foreground_summary().unwrap().unwrap();
                assert!(!summary.active);
                assert!(!summary.stats.complete);
                if failure == "cancel" {
                    assert!(summary.stats.cancelled);
                } else {
                    assert!(
                        summary
                            .stats
                            .message
                            .contains("pending scopes remain for Resume")
                    );
                }
                assert!(store.history().unwrap().is_empty());
                assert_eq!(store.wallet().unwrap().credited_bytes, 0);
                if before_refresh {
                    store
                        .conn
                        .execute_batch("DROP TRIGGER fail_isolated_begin")
                        .unwrap();
                }
            }
            *engine.scan_helper_fixture.lock().unwrap() =
                Some(isolated_helper_fixture(temp.path(), &roots, usize::MAX));
            let failed_generation = engine.runtime.lock().unwrap().foreground_generation;
            engine.request(json!({"action":"resume"})).unwrap();
            assert_ne!(
                engine.runtime.lock().unwrap().foreground_generation,
                failed_generation
            );
            wait_for_discovery_idle(&engine);
            let completed = engine.snapshot().unwrap();
            assert!(completed.stats.complete);
            assert_eq!(completed.stats.errors, 0);
            let foreground = completed.foreground_scan.unwrap();
            assert!(!foreground.active && foreground.stats.complete);
            assert!(!foreground.stats.cancelled);
            assert_eq!(foreground.stats.entries, 7);
            let store = engine.store.lock().unwrap();
            assert!(!store.has_pending_scopes().unwrap());
            let saved = store.load_foreground_summary().unwrap().unwrap();
            assert!(saved.stats.complete);
            assert_eq!(saved.stats.entries, 7);
        }
    }

    #[test]
    fn isolated_discovery_finishes_an_unrelated_root_while_another_is_stalled() {
        let _serial = ISOLATED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let (temp, engine, roots) = foreground_fixture(2);
        let helper = isolated_helper_fixture(temp.path(), &roots, 0);
        *engine.scan_helper_fixture.lock().unwrap() = Some(helper);
        engine.request(json!({"action":"scan"})).unwrap();
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let runtime = engine.runtime.lock().unwrap();
            let scan = runtime.foreground.as_ref().unwrap();
            if scan.roots[&roots[1].id].terminal {
                assert!(!scan.roots[&roots[0].id].terminal);
                assert_eq!(scan.roots[&roots[1].id].stats.entries, 7);
                assert!(!scan.snapshot.stats.complete);
                break;
            }
            drop(runtime);
            assert!(
                Instant::now() < deadline,
                "A stalled helper hid the unrelated completed root"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
        engine.cancel_scan();
        wait_for_discovery_idle(&engine);
        let store = engine.store.lock().unwrap();
        assert!(!store.has_active_scopes().unwrap());
        assert!(store.has_pending_scopes().unwrap());
        assert!(store.history().unwrap().is_empty());
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[test]
    fn isolated_cleanup_parks_without_waiting_for_a_stalled_read_process() {
        let _serial = ISOLATED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let (temp, engine, roots) = foreground_fixture(1);
        *engine.scan_helper_fixture.lock().unwrap() =
            Some(isolated_helper_fixture(temp.path(), &roots, 0));
        engine.request(json!({"action":"scan"})).unwrap();
        let deadline = Instant::now() + Duration::from_secs(2);
        while !engine.store.lock().unwrap().has_active_scopes().unwrap() {
            assert!(Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(5));
        }
        let old_epoch = engine.read_epoch.load(Ordering::Acquire);
        let started = Instant::now();
        let mutation = engine.begin_mutation().unwrap();
        assert!(
            started.elapsed() < Duration::from_secs(1),
            "Mutation waited for a read-only helper"
        );
        assert_ne!(engine.read_epoch.load(Ordering::Acquire), old_epoch);
        {
            let store = engine.store.lock().unwrap();
            assert!(!store.has_active_scopes().unwrap());
            assert!(store.has_pending_scopes().unwrap());
            assert_eq!(store.latest_stats().unwrap().entries, 0);
        }
        engine.cancel_scan();
        drop(mutation);
        wait_for_discovery_idle(&engine);
        assert_eq!(
            fs::read(roots[0].path.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn isolated_finalization_failure_replays_both_claims_without_restart() {
        let _serial = ISOLATED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let (temp, engine, roots) = foreground_fixture(2);
        *engine.scan_helper_fixture.lock().unwrap() =
            Some(isolated_helper_fixture(temp.path(), &roots, 1));
        engine.store.lock().unwrap().conn.execute_batch(&format!(
            "CREATE TEMP TRIGGER fail_isolated_finish BEFORE DELETE ON active_scopes WHEN OLD.root_id='{}' BEGIN SELECT RAISE(ABORT,'disposable isolated finish failure'); END;", roots[0].id
        )).unwrap();
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        assert!(
            engine
                .snapshot()
                .unwrap()
                .error
                .unwrap()
                .contains("disposable isolated finish failure")
        );
        {
            let store = engine.store.lock().unwrap();
            let count: u64 = store
                .conn
                .query_row("SELECT count(*) FROM active_scopes", [], |row| row.get(0))
                .unwrap();
            assert_eq!(count, 2, "Failed recovery must retain both durable claims");
            store
                .conn
                .execute_batch("DROP TRIGGER fail_isolated_finish")
                .unwrap();
        }
        // A new ordinary request recovers abandoned generations in this engine;
        // no close/reopen, deletion, or inferred successful scan is involved.
        *engine.scan_helper_fixture.lock().unwrap() = None;
        engine
            .request(json!({"action":"scan", "metadata_coverage":true}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        assert!(
            engine
                .snapshot()
                .unwrap()
                .foreground_scan
                .unwrap()
                .stats
                .complete
        );
        let store = engine.store.lock().unwrap();
        assert!(!store.has_active_scopes().unwrap());
        assert!(!store.has_pending_scopes().unwrap());
        assert!(store.history().unwrap().is_empty());
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[test]
    fn managed_reviews_require_confirmation_and_cancellation_is_request_scoped() {
        let (_temp, engine, _) = foreground_fixture(0);
        assert!(
            engine
                .request(
                    json!({"action":"managed_review", "provider":"homebrew", "request_id":"first"})
                )
                .is_err()
        );
        engine
            .request(json!({"action":"cancel_managed_review", "request_id":"first"}))
            .unwrap();
        let error = engine.request(json!({"action":"managed_review", "provider":"homebrew", "request_id":"first", "confirmed_read_only":true})).unwrap_err();
        assert!(error.contains("cancelled"));
        let cancel = Arc::new(AtomicBool::new(false));
        engine.managed_review.lock().unwrap().active = Some(("second".into(), Arc::clone(&cancel)));
        engine
            .request(json!({"action":"cancel_managed_review", "request_id":"first"}))
            .unwrap();
        assert!(!cancel.load(Ordering::Acquire));
        engine
            .request(json!({"action":"cancel_managed_review", "request_id":"second"}))
            .unwrap();
        assert!(cancel.load(Ordering::Acquire));
        engine.managed_review.lock().unwrap().active = None;
        assert_eq!(engine.snapshot().unwrap().wallet.credited_bytes, 0);
    }

    fn dirty_scope(engine: &Arc<Engine>, root: &Root, path: &Path) {
        let response = engine
            .request(json!({"action":"dirty", "root_id":root.id, "path":path}))
            .unwrap();
        assert_ne!(response["ignored"], true);
    }

    fn reopen_foreground_fixture(temp: &tempfile::TempDir, engine: Arc<Engine>) -> Arc<Engine> {
        wait_for_discovery_idle(&engine);
        // The idle notification precedes the worker releasing its final Arc.
        // Wait for that actual ownership handoff before reopening its lock.
        let deadline = Instant::now() + Duration::from_secs(5);
        while Arc::strong_count(&engine) != 1 {
            assert!(
                Instant::now() < deadline,
                "Worker did not release its engine"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
        drop(engine);
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match Engine::open(&temp.path().join("library.sqlite"), None) {
                Ok(engine) => return engine,
                Err(err)
                    if err == "This chippytea library is already open in another process."
                        && Instant::now() < deadline =>
                {
                    std::thread::sleep(Duration::from_millis(5));
                }
                Err(err) => panic!("{err}"),
            }
        }
    }

    // Seed derived rows without allocating cleanup-sized payloads or making
    // disposable source files eligible for mutation.
    fn indexed_fixture_source(root: &Root, id: &str) -> Candidate {
        let path = root.path.join("child/preserve.txt");
        Candidate {
            id: id.into(),
            root_id: root.id.clone(),
            identity: safety::identity(&path).unwrap(),
            path,
            title: "Disposable indexed source".into(),
            kind: "download".into(),
            logical_bytes: 0,
            allocated_bytes: 0,
            file_count: 1,
            modified_ns: 0,
            explanation: "Synthetic prior index row".into(),
            consequence: "Preserve this source".into(),
            eligible_permanent: false,
            blocked_reason: Some("Test index row; no cleanup is authorized".into()),
            fingerprint: "disposable".into(),
            evidence: "disposable".into(),
            suggestion_eligible: false,
            provisional: false,
        }
    }

    fn recent_event_fixture() -> (tempfile::TempDir, Arc<Engine>, Root, PathBuf, [PathBuf; 2]) {
        let (temp, engine, mut roots) = foreground_fixture(1);
        let root = roots.remove(0);
        let project = root.path.join("project");
        let artifact = project.join("node_modules");
        let deep = artifact.join("deep");
        fs::create_dir_all(&deep).unwrap();
        fs::write(
            project.join("package.json"),
            br#"{"name":"disposable","version":"1.0.0"}"#,
        )
        .unwrap();
        fs::write(
            project.join("package-lock.json"),
            br#"{"lockfileVersion":3,"packages":{}}"#,
        )
        .unwrap();
        let leaves = [deep.join("first"), deep.join("second")];
        for leaf in &leaves {
            fs::write(leaf, b"preserve disposable output").unwrap();
        }
        let old = std::time::SystemTime::UNIX_EPOCH + Duration::from_secs(1_000_000);
        for path in [
            &leaves[0],
            &leaves[1],
            &deep,
            &artifact,
            &project.join("package.json"),
            &project.join("package-lock.json"),
            &project,
        ] {
            fs::File::open(path)
                .unwrap()
                .set_times(fs::FileTimes::new().set_modified(old))
                .unwrap();
        }
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        (temp, engine, root, artifact, leaves)
    }

    fn recent_file_event(engine: &Arc<Engine>, root: &Root, leaf: &Path) -> Result<Value> {
        engine.request(json!({"action":"dirty","root_id":root.id,
            "events":[{"path":leaf,"kind":"file","recursive":false}]}))
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn full_scans_learn_recent_hints_without_events_and_revalidate_them_on_repeats() {
        let (_temp, engine, root, artifact, leaves) = recent_event_fixture();
        assert!(
            engine
                .runtime
                .lock()
                .unwrap()
                .recent_files
                .get(&root.id, &artifact)
                .is_none()
        );
        let old = fs::metadata(&leaves[0]).unwrap().modified().unwrap();
        fs::write(&leaves[0], b"preserve disposable output").unwrap();
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let first = engine.snapshot().unwrap().foreground_scan.unwrap().stats;
        assert!(first.complete && first.errors == 0);
        assert_eq!(
            engine
                .runtime
                .lock()
                .unwrap()
                .recent_files
                .get(&root.id, &artifact),
            Some(leaves[0].as_path())
        );
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let second = engine.snapshot().unwrap().foreground_scan.unwrap().stats;
        assert!(second.complete && second.errors == 0);
        assert!(second.entries < first.entries);

        engine
            .request(json!({"action":"scan","metadata_coverage":true}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        let covered = engine.snapshot().unwrap().foreground_scan.unwrap().stats;
        assert!(covered.complete && covered.entries > second.entries);
        assert_eq!(
            engine
                .runtime
                .lock()
                .unwrap()
                .recent_files
                .get(&root.id, &artifact),
            Some(leaves[0].as_path())
        );

        fs::File::open(&leaves[0])
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(old))
            .unwrap();
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let stale = engine.snapshot().unwrap();
        assert!(stale.foreground_scan.unwrap().stats.entries > second.entries);
        assert!(
            engine
                .runtime
                .lock()
                .unwrap()
                .recent_files
                .get(&root.id, &artifact)
                .is_none()
        );
        assert!(stale.history.is_empty() && stale.wallet.credited_bytes == 0);
        assert_eq!(fs::read(&leaves[0]).unwrap(), b"preserve disposable output");
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn recent_hint_writeback_preserves_late_unhinted_events_and_keep_changes() {
        for change in ["paths", "root", "structural", "keep"] {
            let (_temp, engine, root, artifact, leaves) = recent_event_fixture();
            fs::write(&leaves[0], b"preserve disposable output").unwrap();
            let steps = watch_discovery(&engine);
            engine.request(json!({"action":"scan"})).unwrap();
            discovery_step(&steps, DiscoveryStage::Claimed, &root.path)
                .send(())
                .unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Began, &root.path);
            let request = match change {
                "paths" => json!({"action":"dirty","root_id":root.id,"paths":[leaves[0]]}),
                "root" => json!({"action":"dirty","root_id":root.id}),
                "structural" => json!({"action":"dirty","root_id":root.id,
                    "events":[{"path":artifact,"kind":"directory","recursive":true}]}),
                "keep" => {
                    let row = engine
                        .store
                        .lock()
                        .unwrap()
                        .candidates_for_root(&root.id)
                        .unwrap()
                        .into_iter()
                        .find(|row| row.path == artifact)
                        .unwrap();
                    json!({"action":"keep","id":row.id})
                }
                _ => unreachable!(),
            };
            engine.request(request).unwrap();
            release.send(()).unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Finished, &root.path);
            assert!(
                engine
                    .runtime
                    .lock()
                    .unwrap()
                    .recent_files
                    .get(&root.id, &artifact)
                    .is_none(),
                "A late {change} change must reject an earlier traversal's learned path"
            );
            if change != "keep" {
                assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
            }
            // Retain late durable work without starting a second job in this test.
            engine.cancel_scan();
            release.send(()).unwrap();
            wait_for_discovery_idle(&engine);
            assert_eq!(fs::read(&leaves[0]).unwrap(), b"preserve disposable output");
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn recent_hint_writeback_requires_successful_uncancelled_scope_finalization() {
        for failure in ["cancel", "publish", "finalize", "partial"] {
            let (_temp, engine, root, artifact, leaves) = recent_event_fixture();
            fs::write(&leaves[0], b"preserve disposable output").unwrap();
            if failure == "partial" {
                let mut deep = root.path.clone();
                for _ in 0..=safety::MAX_DEPTH {
                    deep.push("d");
                    fs::create_dir(&deep).unwrap();
                }
            }
            let scanned = Arc::new(AtomicBool::new(false));
            let observed = Arc::clone(&scanned);
            let weak = Arc::downgrade(&engine);
            let checked_root = root.id.clone();
            let checked_artifact = artifact.clone();
            *engine.discovery_observer.lock().unwrap() = Some(Arc::new(move |stage, _, _| {
                let engine = weak.upgrade().unwrap();
                if stage == DiscoveryStage::Began && failure == "publish" {
                    engine.store.lock().unwrap().conn.execute_batch(
                        "CREATE TEMP TRIGGER reject_hint_batch BEFORE INSERT ON candidates BEGIN SELECT RAISE(ABORT,'disposable batch failure'); END;"
                    ).unwrap();
                }
                if stage != DiscoveryStage::Scanned {
                    return;
                }
                observed.store(true, Ordering::Release);
                let row = engine
                    .store
                    .lock()
                    .unwrap()
                    .candidates_for_root(&checked_root)
                    .unwrap()
                    .into_iter()
                    .find(|row| row.path == checked_artifact)
                    .unwrap();
                assert!(!row.provisional && row.file_count > 0 && row.fingerprint.is_empty());
                assert!(
                    engine
                        .runtime
                        .lock()
                        .unwrap()
                        .recent_files
                        .get(&checked_root, &checked_artifact)
                        .is_none(),
                    "A learned path must stay local until finalization"
                );
                if failure == "cancel" {
                    engine.cancel_scan();
                } else if failure == "finalize" {
                    engine.store.lock().unwrap().conn.execute_batch(
                        "CREATE TEMP TRIGGER reject_hint_finish BEFORE DELETE ON active_scopes BEGIN SELECT RAISE(ABORT,'disposable finish failure'); END;"
                    ).unwrap();
                }
            }));
            engine.request(json!({"action":"scan"})).unwrap();
            wait_for_discovery_idle(&engine);
            assert_eq!(scanned.load(Ordering::Acquire), failure != "publish");
            assert!(
                engine
                    .runtime
                    .lock()
                    .unwrap()
                    .recent_files
                    .get(&root.id, &artifact)
                    .is_none(),
                "The {failure} scope cannot write back learned hints"
            );
            let snapshot = engine.snapshot().unwrap();
            let stats = snapshot.foreground_scan.unwrap().stats;
            assert!(!stats.complete);
            if failure == "partial" {
                assert!(stats.errors > 0);
                assert!(snapshot.error.is_none());
            } else if failure == "cancel" {
                assert!(stats.cancelled);
            } else {
                assert!(snapshot.error.unwrap().contains("disposable"));
            }
            assert!(snapshot.history.is_empty() && snapshot.wallet.credited_bytes == 0);
            assert_eq!(fs::read(&leaves[0]).unwrap(), b"preserve disposable output");
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn recent_hints_follow_committed_traversals_and_preserve_late_events() {
        let (_temp, engine, root, artifact, leaves) = recent_event_fixture();
        let before = engine.snapshot().unwrap();
        let foreground = serde_json::to_value(&before.foreground_scan).unwrap();
        let old = fs::metadata(&leaves[0]).unwrap().modified().unwrap();
        fs::write(&leaves[0], b"preserve disposable output").unwrap();
        let steps = watch_discovery(&engine);
        recent_file_event(&engine, &root, &leaves[0]).unwrap();
        discovery_step(&steps, DiscoveryStage::Claimed, &artifact)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &artifact);
        fs::write(&leaves[1], b"preserve disposable output").unwrap();
        recent_file_event(&engine, &root, &leaves[1]).unwrap();
        release.send(()).unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Finished, &artifact);
        assert_eq!(
            engine.snapshot().unwrap().stats.entries,
            before.stats.entries + 1
        );
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
        // Make the first proof stale. Only the late event's retained hint can
        // exclude this artifact without visiting descendants on the next job.
        fs::File::open(&leaves[0])
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(old))
            .unwrap();
        release.send(()).unwrap();
        discovery_step(&steps, DiscoveryStage::Claimed, &artifact)
            .send(())
            .unwrap();
        discovery_step(&steps, DiscoveryStage::Began, &artifact)
            .send(())
            .unwrap();
        discovery_step(&steps, DiscoveryStage::Finished, &artifact)
            .send(())
            .unwrap();
        wait_for_discovery_idle(&engine);
        let after = engine.snapshot().unwrap();
        assert_eq!(after.stats.entries, before.stats.entries + 2);
        assert!(after.error.is_none() && after.stats.complete);
        assert_eq!(
            serde_json::to_value(&after.foreground_scan).unwrap(),
            foreground
        );
        assert!(after.history.is_empty() && after.wallet.credited_bytes == 0);
        let store = engine.store.lock().unwrap();
        let row = store
            .candidates_for_root(&root.id)
            .unwrap()
            .into_iter()
            .find(|c| c.path == artifact)
            .unwrap();
        assert!(!row.provisional && !row.suggestion_eligible && !row.eligible_permanent);
        assert!(row.fingerprint.is_empty());
        assert_eq!((row.file_count, row.allocated_bytes), (0, 0));
        assert!(!store.has_pending_scopes().unwrap());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn missing_hints_after_restart_preserve_durable_recent_file_exclusion() {
        let (temp, engine, root, artifact, leaves) = recent_event_fixture();
        engine.cancel_scan();
        fs::write(&leaves[0], b"preserve disposable output").unwrap();
        recent_file_event(&engine, &root, &leaves[0]).unwrap();
        assert!(!engine.scanning.load(Ordering::Acquire));
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
        let reopened = reopen_foreground_fixture(&temp, engine);
        let before = reopened.snapshot().unwrap();
        reopened.request(json!({"action":"resume"})).unwrap();
        wait_for_discovery_idle(&reopened);
        let after = reopened.snapshot().unwrap();
        assert!(after.error.is_none() && after.stats.complete);
        assert!(after.stats.entries >= before.stats.entries + 2);
        assert!(after.history.is_empty() && after.wallet.credited_bytes == 0);
        let store = reopened.store.lock().unwrap();
        let row = store
            .candidates_for_root(&root.id)
            .unwrap()
            .into_iter()
            .find(|c| c.path == artifact)
            .unwrap();
        assert!(!row.suggestion_eligible && !row.eligible_permanent);
        assert!(!store.has_pending_scopes().unwrap());
    }

    #[test]
    fn rejected_event_batches_cannot_install_recent_file_hints() {
        let (_temp, engine, root, artifact, leaves) = recent_event_fixture();
        engine.cancel_scan();
        engine.store.lock().unwrap().conn.execute_batch(
            "CREATE TRIGGER reject_test_scope BEFORE INSERT ON pending_scopes BEGIN SELECT RAISE(ABORT,'disposable enqueue failure'); END;"
        ).unwrap();
        assert!(recent_file_event(&engine, &root, &leaves[0]).is_err());
        assert!(!engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert!(
            engine
                .runtime
                .lock()
                .unwrap()
                .recent_files
                .get(&root.id, &artifact)
                .is_none()
        );
    }

    #[test]
    fn typed_lockfile_refresh_updates_target_and_origin_without_replacing_saved_scan() {
        let (temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let origin = root.path.join("Cargo.lock");
        let target = root.path.join("target");
        fs::write(&origin, b"version = 4\n").unwrap();
        fs::write(
            root.path.join("Cargo.toml"),
            b"[package]\nname = 'disposable'\nversion = '0.1.0'\n",
        )
        .unwrap();
        fs::create_dir(&target).unwrap();
        fs::write(
            target.join("CACHEDIR.TAG"),
            b"Signature: 8a477f597d28d172789f06886806bc55\n",
        )
        .unwrap();
        let old = std::time::SystemTime::UNIX_EPOCH + Duration::from_secs(1_000_000);
        for path in [
            &origin,
            &root.path.join("Cargo.toml"),
            &target.join("CACHEDIR.TAG"),
            &target,
        ] {
            fs::File::open(path)
                .unwrap()
                .set_times(fs::FileTimes::new().set_modified(old))
                .unwrap();
        }
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let before = engine.snapshot().unwrap();
        let foreground = serde_json::to_value(&before.foreground_scan).unwrap();
        let initial = engine
            .store
            .lock()
            .unwrap()
            .candidates_for_root(&root.id)
            .unwrap();
        assert!(initial.iter().any(|row| row.path == target));
        let sibling = indexed_fixture_source(root, "preserved-sibling");
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates: vec![sibling.clone()],
                stats: ScanStats::default(),
            })
            .unwrap();

        // A real lockfile rewrite refreshes the target's evidence even though
        // unrelated source rows and the completed foreground summary stay put.
        fs::write(&origin, b"version = 4\n# changed ownership evidence\n").unwrap();
        engine
            .request(json!({"action":"dirty", "root_id":root.id,
            "events":[{"path":origin,"kind":"file","recursive":false}]}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        let refreshed = engine.snapshot().unwrap();
        assert!(refreshed.error.is_none());
        assert_eq!(refreshed.stats.entries, before.stats.entries + 2);
        assert_eq!(
            serde_json::to_value(&refreshed.foreground_scan).unwrap(),
            foreground
        );
        {
            let store = engine.store.lock().unwrap();
            assert_eq!(store.candidate(&sibling.id).unwrap(), sibling);
            let rows = store.candidates_for_root(&root.id).unwrap();
            let changed = rows.iter().find(|row| row.path == target).unwrap();
            assert_ne!(
                changed.evidence,
                initial
                    .iter()
                    .find(|row| row.path == target)
                    .unwrap()
                    .evidence
            );
            assert!(!changed.suggestion_eligible);
            assert!(!store.incomplete(&root.id).unwrap());
        }

        // Case-only renames leave a differently spelled directory in place.
        // Replay must remove the old lowercase row without following its alias.
        fs::rename(&target, root.path.join("Target")).unwrap();
        let mut origin_row = sibling.clone();
        origin_row.id = "old-lockfile".into();
        origin_row.path = origin.clone();
        origin_row.identity = safety::identity(&origin).unwrap();
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates: vec![origin_row],
                stats: ScanStats::default(),
            })
            .unwrap();
        fs::remove_file(&origin).unwrap();
        engine
            .request(json!({"action":"dirty", "root_id":root.id,
            "events":[{"path":origin,"kind":"file","recursive":false}]}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        let after = engine.snapshot().unwrap();
        assert!(after.error.is_none() && after.stats.complete);
        assert_eq!(after.stats.entries, refreshed.stats.entries);
        assert_eq!(
            serde_json::to_value(&after.foreground_scan).unwrap(),
            foreground
        );
        {
            let store = engine.store.lock().unwrap();
            assert_eq!(
                store.candidates_for_root(&root.id).unwrap(),
                vec![sibling.clone()]
            );
            assert!(!store.has_pending_scopes().unwrap());
        }
        assert!(after.history.is_empty());
        assert_eq!(after.wallet.credited_bytes, 0);
        assert_eq!(
            fs::read(root.path.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
        let reopened = reopen_foreground_fixture(&temp, engine);
        assert_eq!(
            serde_json::to_value(reopened.snapshot().unwrap().foreground_scan).unwrap(),
            foreground
        );
        assert_eq!(
            reopened
                .store
                .lock()
                .unwrap()
                .candidate(&sibling.id)
                .unwrap(),
            sibling
        );
    }

    #[test]
    fn lockfile_row_does_not_hide_an_enclosing_partial_download_row() {
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let parent = root.path.join("child");
        let origin = parent.join("Cargo.lock");
        fs::write(&origin, b"version = 4\n").unwrap();
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let before = engine.snapshot().unwrap();
        let mut old_parent = indexed_fixture_source(root, "old-parent");
        old_parent.path = parent.clone();
        let mut old_origin = old_parent.clone();
        old_origin.id = "old-origin".into();
        old_origin.path = origin.clone();
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates: vec![old_parent, old_origin],
                stats: ScanStats::default(),
            })
            .unwrap();
        engine
            .request(json!({"action":"dirty", "root_id":root.id,
            "events":[{"path":origin,"kind":"file","recursive":false}]}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        let after = engine.snapshot().unwrap();
        assert!(after.error.is_none() && after.stats.complete);
        assert_eq!(after.stats.entries, before.stats.entries + 3);
        let store = engine.store.lock().unwrap();
        assert!(store.candidates_for_root(&root.id).unwrap().is_empty());
        assert!(!store.has_pending_scopes().unwrap());
    }

    #[test]
    fn raw_artifact_scopes_share_traversal_and_reconciliation_boundaries() {
        for previously_incomplete in [false, true] {
            let (_temp, engine, roots) = foreground_fixture(1);
            let root = &roots[0];
            engine.request(json!({"action":"scan"})).unwrap();
            wait_for_discovery_idle(&engine);
            let before = engine.snapshot().unwrap();
            let foreground = serde_json::to_value(&before.foreground_scan).unwrap();
            let artifact = root.path.join("target");
            let nested = artifact.join("inner/node_modules");
            fs::create_dir_all(&nested).unwrap();
            let stale_path = artifact.join("stale");
            fs::write(&stale_path, b"preserve artifact contents").unwrap();
            let mut stale = indexed_fixture_source(root, "stale");
            stale.identity = safety::identity(&stale_path).unwrap();
            stale.path = stale_path.clone();
            let sibling = indexed_fixture_source(root, "sibling");
            let first = nested.join("a");
            let second = nested.join("b");
            let late = nested.join("late");
            {
                let mut store = engine.store.lock().unwrap();
                store
                    .save_batch(&ScanBatch {
                        candidates: vec![stale, sibling.clone()],
                        stats: ScanStats::default(),
                    })
                    .unwrap();
                store.keep(sibling.path.to_str().unwrap(), true).unwrap();
                if previously_incomplete {
                    store
                        .conn
                        .execute(
                            "INSERT INTO incomplete_roots(root_id) VALUES(?1)",
                            [&root.id],
                        )
                        .unwrap();
                }
                // Raw persisted/unkeep work has not passed through event_scope.
                store
                    .enqueue_scopes(&root.id, &[first.clone(), second])
                    .unwrap();
            }
            let steps = watch_discovery(&engine);
            engine.request(json!({"action":"resume"})).unwrap();
            discovery_step(&steps, DiscoveryStage::Claimed, &first)
                .send(())
                .unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Began, &artifact);
            {
                let mut store = engine.store.lock().unwrap();
                let effective: String = store
                    .conn
                    .query_row("SELECT scope FROM refreshes", [], |row| row.get(0))
                    .unwrap();
                assert_eq!(Path::new(&effective), artifact);
                assert!(
                    !store.has_pending_scopes().unwrap(),
                    "Covered siblings must coalesce before traversal"
                );
                // A later event must survive even though it shares the artifact.
                store.enqueue_scope(&root.id, &late).unwrap();
            }
            release.send(()).unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Finished, &first);
            {
                let store = engine.store.lock().unwrap();
                assert!(
                    store.candidate("stale").is_err(),
                    "Reconcile the whole traversed artifact"
                );
                assert_eq!(store.candidate("sibling").unwrap(), sibling);
                assert_eq!(
                    store.kept().unwrap(),
                    vec![sibling.path.to_str().unwrap().to_string()]
                );
                assert_eq!(store.incomplete(&root.id).unwrap(), previously_incomplete);
                let pending: String = store
                    .conn
                    .query_row("SELECT path FROM pending_scopes", [], |row| row.get(0))
                    .unwrap();
                assert_eq!(Path::new(&pending), late);
            }
            release.send(()).unwrap();
            discovery_step(&steps, DiscoveryStage::Claimed, &late)
                .send(())
                .unwrap();
            discovery_step(&steps, DiscoveryStage::Began, &artifact)
                .send(())
                .unwrap();
            discovery_step(&steps, DiscoveryStage::Finished, &late)
                .send(())
                .unwrap();
            wait_for_discovery_idle(&engine);
            assert!(steps.try_recv().is_err());
            let after = engine.snapshot().unwrap();
            assert_eq!(
                serde_json::to_value(after.foreground_scan).unwrap(),
                foreground
            );
            assert_eq!(after.stats.complete, !previously_incomplete);
            assert_eq!(after.stats.errors, 0);
            assert!(after.error.is_none());
            assert!(after.history.is_empty());
            assert_eq!(after.wallet.credited_bytes, 0);
            assert_eq!(
                fs::read(&stale_path).unwrap(),
                b"preserve artifact contents"
            );
            assert_eq!(fs::read(&sibling.path).unwrap(), b"disposable source");
            let store = engine.store.lock().unwrap();
            for table in ["pending_scopes", "active_scopes", "refreshes"] {
                let count: u64 = store
                    .conn
                    .query_row(&format!("SELECT count(*) FROM {table}"), [], |row| {
                        row.get(0)
                    })
                    .unwrap();
                assert_eq!(count, 0, "{table} must drain");
            }
        }
    }

    #[test]
    fn disappeared_scope_prunes_its_rows_preserving_late_events_and_foreground_summary() {
        for previously_incomplete in [false, true] {
            let (temp, engine, roots) = foreground_fixture(2);
            engine.request(json!({"action":"scan"})).unwrap();
            wait_for_discovery_idle(&engine);
            let before = engine.snapshot().unwrap();
            let foreground = serde_json::to_value(&before.foreground_scan).unwrap();
            let old = indexed_fixture_source(&roots[0], "old");
            let sibling = indexed_fixture_source(&roots[1], "sibling");
            {
                let mut store = engine.store.lock().unwrap();
                store
                    .save_batch(&ScanBatch {
                        candidates: vec![old, sibling.clone()],
                        stats: ScanStats::default(),
                    })
                    .unwrap();
                if previously_incomplete {
                    store
                        .conn
                        .execute(
                            "INSERT INTO incomplete_roots(root_id) VALUES(?1)",
                            [&roots[0].id],
                        )
                        .unwrap();
                }
            }
            let scope = roots[0].path.join("child");
            let moved = temp.path().join("preserved-child");
            let steps = watch_discovery(&engine);
            dirty_scope(&engine, &roots[0], &scope);
            discovery_step(&steps, DiscoveryStage::Claimed, &scope)
                .send(())
                .unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Began, &scope);
            fs::rename(&scope, &moved).unwrap();
            engine
                .store
                .lock()
                .unwrap()
                .enqueue_scope(&roots[0].id, &scope)
                .unwrap();
            release.send(()).unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Finished, &scope);
            {
                let store = engine.store.lock().unwrap();
                assert!(store.candidate("old").is_err());
                assert_eq!(store.candidate("sibling").unwrap(), sibling);
                assert_eq!(
                    store.incomplete(&roots[0].id).unwrap(),
                    previously_incomplete
                );
                let pending: u64 = store
                    .conn
                    .query_row("SELECT count(*) FROM pending_scopes", [], |row| row.get(0))
                    .unwrap();
                assert_eq!(
                    pending, 1,
                    "An event received after begin must survive finalization"
                );
            }
            let missing = engine.snapshot().unwrap();
            assert!(missing.error.is_none());
            assert_eq!(missing.stats.errors, 0);
            assert_eq!(missing.stats.entries, before.stats.entries);
            assert_eq!(
                serde_json::to_value(missing.foreground_scan).unwrap(),
                foreground
            );
            // A later recreation is discovered through the retained exact job,
            // without enumerating a sibling or widening to a full root scan.
            fs::rename(&moved, &scope).unwrap();
            release.send(()).unwrap();
            finish_discovery_job(&steps, &scope).send(()).unwrap();
            wait_for_discovery_idle(&engine);
            let after = engine.snapshot().unwrap();
            assert_eq!(after.stats.entries, before.stats.entries + 2);
            assert_eq!(after.stats.complete, !previously_incomplete);
            assert!(after.error.is_none());
            assert_eq!(
                serde_json::to_value(after.foreground_scan).unwrap(),
                foreground
            );
            assert!(after.history.is_empty());
            assert_eq!(after.wallet.credited_bytes, 0);
            for root in &roots {
                assert_eq!(
                    fs::read(root.path.join("child/preserve.txt")).unwrap(),
                    b"disposable source"
                );
            }
        }
    }

    #[test]
    fn disappeared_grant_is_not_reconciled_as_an_empty_child_scope() {
        let (temp, engine, roots) = foreground_fixture(1);
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let old = indexed_fixture_source(&roots[0], "old");
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates: vec![old.clone()],
                stats: ScanStats::default(),
            })
            .unwrap();
        let scope = roots[0].path.join("child");
        let moved = temp.path().join("preserved-grant");
        let steps = watch_discovery(&engine);
        dirty_scope(&engine, &roots[0], &scope);
        discovery_step(&steps, DiscoveryStage::Claimed, &scope)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &scope);
        fs::rename(&roots[0].path, &moved).unwrap();
        release.send(()).unwrap();
        discovery_step(&steps, DiscoveryStage::Finished, &scope)
            .send(())
            .unwrap();
        wait_for_discovery_idle(&engine);
        let after = engine.snapshot().unwrap();
        assert!(!after.stats.complete && after.stats.errors > 0);
        assert!(after.error.is_some());
        assert_eq!(engine.store.lock().unwrap().candidate("old").unwrap(), old);
        assert!(after.history.is_empty());
        assert_eq!(after.wallet.credited_bytes, 0);
        assert_eq!(
            fs::read(moved.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn restart_retains_full_summary_without_rescanning_or_writing_for_child_events() {
        let (temp, engine, roots) = foreground_fixture(2);
        engine.store.lock().unwrap().conn.execute_batch(
            "CREATE TABLE test_summary_writes(n INTEGER); INSERT INTO test_summary_writes VALUES(0);
             CREATE TRIGGER count_summary_writes AFTER UPDATE OF summary_json ON foreground_state
             WHEN NEW.summary_json IS NOT NULL BEGIN UPDATE test_summary_writes SET n=n+1; END;",
        ).unwrap();
        engine
            .request(json!({"action":"scan","metadata_coverage":true}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        let full = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(full.stats.complete && !full.active);
        assert_eq!(full.stats.entries, 6);
        let frozen = serde_json::to_value(full).unwrap();
        dirty_scope(&engine, &roots[0], &roots[0].path.join("child"));
        wait_for_discovery_idle(&engine);
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&roots[1].id, &roots[1].path.join("child"))
            .unwrap();
        let engine = reopen_foreground_fixture(&temp, engine);
        assert_eq!(engine.snapshot().unwrap().stats.entries, 2);
        assert_eq!(
            serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap(),
            frozen
        );
        assert!(engine.runtime.lock().unwrap().foreground.is_none());
        let steps = watch_discovery(&engine);
        engine.request(json!({"action":"resume"})).unwrap();
        // A full-root rescan would fail this exact scope handshake.
        finish_discovery_job(&steps, &roots[1].path.join("child"))
            .send(())
            .unwrap();
        wait_for_discovery_idle(&engine);
        let snapshot = engine.snapshot().unwrap();
        assert_eq!(
            serde_json::to_value(snapshot.foreground_scan.unwrap()).unwrap(),
            frozen
        );
        assert!(snapshot.history.is_empty());
        assert_eq!(snapshot.wallet.credited_bytes, 0);
        let writes: u64 = engine
            .store
            .lock()
            .unwrap()
            .conn
            .query_row("SELECT n FROM test_summary_writes", [], |r| r.get(0))
            .unwrap();
        assert_eq!(
            writes, 1,
            "Background work must not rewrite terminal presentation"
        );
        for root in roots {
            assert_eq!(
                fs::read(root.path.join("child/preserve.txt")).unwrap(),
                b"disposable source"
            );
        }
    }

    #[test]
    fn restored_summary_yields_to_recovered_full_root_work() {
        let (temp, engine, roots) = foreground_fixture(2);
        engine
            .request(json!({"action":"scan","metadata_coverage":true}))
            .unwrap();
        wait_for_discovery_idle(&engine);
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&roots[1].id, &roots[1].path)
            .unwrap();
        let engine = reopen_foreground_fixture(&temp, engine);
        assert_eq!(
            engine
                .snapshot()
                .unwrap()
                .foreground_scan
                .unwrap()
                .stats
                .entries,
            6
        );
        let steps = watch_discovery(&engine);
        engine.request(json!({"action":"resume"})).unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Claimed, &roots[1].path);
        let active = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(active.active && !active.stats.complete);
        assert_eq!(active.stats.entries, 0);
        release.send(()).unwrap();
        discovery_step(&steps, DiscoveryStage::Began, &roots[1].path)
            .send(())
            .unwrap();
        discovery_step(&steps, DiscoveryStage::Finished, &roots[1].path)
            .send(())
            .unwrap();
        wait_for_discovery_idle(&engine);
        let engine = reopen_foreground_fixture(&temp, engine);
        let completed = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(completed.stats.complete && !completed.active);
        assert_eq!(completed.stats.entries, 3);
    }

    #[test]
    fn restart_retains_cancelled_and_failed_foreground_results() {
        for cancel in [false, true] {
            let (temp, engine, roots) = foreground_fixture(1);
            let steps = watch_discovery(&engine);
            engine.request(json!({"action":"scan"})).unwrap();
            let release = discovery_step(&steps, DiscoveryStage::Claimed, &roots[0].path);
            if cancel {
                engine.cancel_scan();
                release.send(()).unwrap();
                discovery_step(&steps, DiscoveryStage::Finished, &roots[0].path)
                    .send(())
                    .unwrap();
            } else {
                release.send(()).unwrap();
                let release = discovery_step(&steps, DiscoveryStage::Began, &roots[0].path);
                // Rename only this newly created disposable grant. The original
                // identity and source survive, while discovery must report partial coverage.
                fs::rename(&roots[0].path, roots[0].path.with_extension("moved")).unwrap();
                release.send(()).unwrap();
                discovery_step(&steps, DiscoveryStage::Finished, &roots[0].path)
                    .send(())
                    .unwrap();
            }
            wait_for_discovery_idle(&engine);
            let snapshot = engine.snapshot().unwrap();
            let failed = snapshot.foreground_scan.unwrap();
            assert!(!failed.active && !failed.stats.complete);
            assert_eq!(failed.stats.cancelled, cancel);
            if !cancel {
                assert!(failed.stats.errors > 0);
                // A missing grant fails at the root-open boundary, before
                // child-entry inspection. Both remain explicit errors.
                assert!(snapshot.error.is_some());
            }
            let frozen = serde_json::to_value(failed).unwrap();
            let engine = reopen_foreground_fixture(&temp, engine);
            let snapshot = engine.snapshot().unwrap();
            assert_eq!(
                serde_json::to_value(snapshot.foreground_scan.unwrap()).unwrap(),
                frozen
            );
            assert!(!snapshot.stats.complete);
            assert!(snapshot.history.is_empty());
            assert_eq!(snapshot.wallet.credited_bytes, 0);
            if !cancel {
                let moved = roots[0].path.with_extension("moved");
                assert_eq!(
                    fs::read(moved.join("child/preserve.txt")).unwrap(),
                    b"disposable source"
                );
                fs::rename(moved, &roots[0].path).unwrap();
            }
        }
    }

    #[test]
    fn grant_mutations_invalidate_live_and_restored_summaries_only_on_success() {
        let (temp, engine, roots) = foreground_fixture(1);
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let engine = reopen_foreground_fixture(&temp, engine);
        engine
            .request(json!({"action":"forget","id":"already-forgotten"}))
            .unwrap();
        assert!(engine.snapshot().unwrap().foreground_scan.is_some());
        assert!(
            engine
                .request(json!({"action":"authorize","path":roots[0].path,"kind":"folder"}))
                .is_err()
        );
        assert!(engine.snapshot().unwrap().foreground_scan.is_some());
        engine
            .request(json!({"action":"forget","id":roots[0].id}))
            .unwrap();
        assert!(engine.snapshot().unwrap().foreground_scan.is_none());
        let engine = reopen_foreground_fixture(&temp, engine);
        assert!(engine.snapshot().unwrap().foreground_scan.is_none());
        assert!(engine.snapshot().unwrap().roots.is_empty());
        assert_eq!(
            fs::read(roots[0].path.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn summary_write_failure_preserves_completed_work_and_previous_history() {
        let (temp, engine, roots) = foreground_fixture(1);
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let old =
            serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap();
        engine
            .store
            .lock()
            .unwrap()
            .conn
            .execute_batch(
                "CREATE TEMP TRIGGER fail_summary BEFORE UPDATE OF summary_json ON foreground_state
             BEGIN SELECT RAISE(ABORT,'disposable summary failure'); END;",
            )
            .unwrap();
        fs::create_dir(roots[0].path.join("new-child")).unwrap();
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let snapshot = engine.snapshot().unwrap();
        assert!(snapshot.foreground_scan.unwrap().stats.complete);
        assert!(
            snapshot
                .error
                .unwrap()
                .contains("Could not save the last scan summary")
        );
        {
            let store = engine.store.lock().unwrap();
            assert!(!store.has_pending_scopes().unwrap());
            let outstanding: u64 = store.conn.query_row(
                "SELECT (SELECT count(*) FROM active_scopes)+(SELECT count(*) FROM refreshes)+(SELECT count(*) FROM incomplete_roots)",
                [], |r| r.get(0),
            ).unwrap();
            assert_eq!(outstanding, 0);
            assert!(store.history().unwrap().is_empty());
            assert_eq!(store.wallet().unwrap().credited_bytes, 0);
        }
        let engine = reopen_foreground_fixture(&temp, engine);
        assert_eq!(
            serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap(),
            old
        );
        assert_eq!(engine.snapshot().unwrap().stats.entries, 4);
    }

    #[test]
    fn foreground_finishes_two_roots_without_waiting_for_late_events() {
        let (_temp, engine, roots) = foreground_fixture(2);
        let (a, b) = (&roots[0], &roots[1]);
        let steps = watch_discovery(&engine);
        engine
            .request(json!({"action":"scan", "metadata_coverage":true}))
            .unwrap();
        discovery_step(&steps, DiscoveryStage::Claimed, &a.path)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &a.path);
        dirty_scope(&engine, a, &a.path.join("child"));
        release.send(()).unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Finished, &a.path);
        let partial = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(partial.active);
        assert!(!partial.stats.complete);
        assert_eq!(partial.stats.entries, 3);
        // A new full event between requested passes must remain background work.
        dirty_scope(&engine, a, &a.path);
        release.send(()).unwrap();
        discovery_step(&steps, DiscoveryStage::Claimed, &b.path)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &b.path);
        dirty_scope(&engine, b, &b.path.join("child"));
        release.send(()).unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Finished, &b.path);
        let snapshot = engine.snapshot().unwrap();
        assert!(
            snapshot.scanning,
            "The background worker still has durable work"
        );
        let completed = snapshot.foreground_scan.unwrap();
        assert!(!completed.active);
        assert!(completed.stats.complete);
        assert_eq!(completed.stats.entries, 6);
        assert_eq!(completed.stats.files, 2);
        assert_eq!(completed.stats.errors, 0);
        let frozen = serde_json::to_value(&completed).unwrap();
        release.send(()).unwrap();

        discovery_step(&steps, DiscoveryStage::Claimed, &a.path)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &a.path);
        let snapshot = engine.snapshot().unwrap();
        assert!(
            !snapshot.stats.complete,
            "The active background scope affects global coverage"
        );
        assert_eq!(
            serde_json::to_value(snapshot.foreground_scan.unwrap()).unwrap(),
            frozen
        );
        // Events after both requested passes are also retained and cannot change
        // the completed foreground count, timing, or status.
        dirty_scope(&engine, a, &a.path.join("child"));
        release.send(()).unwrap();
        discovery_step(&steps, DiscoveryStage::Finished, &a.path)
            .send(())
            .unwrap();
        for path in [b.path.join("child"), a.path.join("child")] {
            let release = finish_discovery_job(&steps, &path);
            assert_eq!(
                serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap(),
                frozen
            );
            release.send(()).unwrap();
        }
        wait_for_discovery_idle(&engine);
        assert!(!engine.store.lock().unwrap().has_pending_scopes().unwrap());
        assert_eq!(
            serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap(),
            frozen
        );
        assert_eq!(
            fs::read(a.path.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
        assert!(engine.snapshot().unwrap().history.is_empty());
        assert_eq!(engine.snapshot().unwrap().wallet.credited_bytes, 0);
    }

    #[test]
    fn foreground_request_adopts_only_a_full_pass_that_has_not_begun() {
        for request_at in [DiscoveryStage::Claimed, DiscoveryStage::Began] {
            let (_temp, engine, roots) = foreground_fixture(1);
            let root = &roots[0];
            engine
                .request(json!({"action":"scan", "metadata_coverage":true}))
                .unwrap();
            wait_for_discovery_idle(&engine);
            let steps = watch_discovery(&engine);
            dirty_scope(&engine, root, &root.path);
            let mut release = discovery_step(&steps, DiscoveryStage::Claimed, &root.path);
            if request_at == DiscoveryStage::Began {
                release.send(()).unwrap();
                release = discovery_step(&steps, DiscoveryStage::Began, &root.path);
            }
            assert!(!engine.snapshot().unwrap().foreground_scan.unwrap().active);
            let response = engine
                .request(json!({"action":"scan", "metadata_coverage":true}))
                .unwrap();
            assert_ne!(response["already_scanning"], true);
            assert_eq!(
                engine.request(json!({"action":"scan"})).unwrap()["already_scanning"],
                true
            );
            release.send(()).unwrap();
            if request_at == DiscoveryStage::Claimed {
                discovery_step(&steps, DiscoveryStage::Began, &root.path)
                    .send(())
                    .unwrap();
            }
            let release = discovery_step(&steps, DiscoveryStage::Finished, &root.path);
            if request_at == DiscoveryStage::Began {
                let foreground = engine.snapshot().unwrap().foreground_scan.unwrap();
                assert!(foreground.active);
                assert_eq!(
                    foreground.stats.entries, 0,
                    "Pre-request traversal cannot count toward a new scan"
                );
                assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
                release.send(()).unwrap();
                finish_discovery_job(&steps, &root.path).send(()).unwrap();
            } else {
                let foreground = engine.snapshot().unwrap().foreground_scan.unwrap();
                assert!(!foreground.active);
                assert!(foreground.stats.complete);
                assert!(
                    !engine.store.lock().unwrap().has_pending_scopes().unwrap(),
                    "Adopted traversal must cover the queued request exactly once"
                );
                release.send(()).unwrap();
            }
            wait_for_discovery_idle(&engine);
            let foreground = engine.snapshot().unwrap().foreground_scan.unwrap();
            assert!(!foreground.active);
            assert!(foreground.stats.complete);
            assert_eq!(foreground.stats.entries, 3);
        }
    }

    #[test]
    fn foreground_root_failure_stays_incomplete_after_another_root_succeeds() {
        let (temp, engine, roots) = foreground_fixture(2);
        let (a, b) = (&roots[0], &roots[1]);
        let steps = watch_discovery(&engine);
        engine
            .request(json!({"action":"scan", "metadata_coverage":true}))
            .unwrap();
        discovery_step(&steps, DiscoveryStage::Claimed, &a.path)
            .send(())
            .unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Began, &a.path);
        let preserved = temp.path().join("preserved-root");
        fs::rename(&a.path, &preserved).unwrap();
        fs::create_dir(&a.path).unwrap();
        release.send(()).unwrap();
        let release = discovery_step(&steps, DiscoveryStage::Finished, &a.path);
        let failed = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(failed.active);
        assert_eq!(failed.stats.errors, 1);
        release.send(()).unwrap();
        finish_discovery_job(&steps, &b.path).send(()).unwrap();
        wait_for_discovery_idle(&engine);
        let completed = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(!completed.active);
        assert!(!completed.stats.complete);
        assert!(!completed.stats.cancelled);
        assert_eq!(completed.stats.errors, 1);
        assert_eq!(completed.stats.entries, 3);
        assert_eq!(
            fs::read(preserved.join("child/preserve.txt")).unwrap(),
            b"disposable source"
        );
    }

    #[test]
    fn foreground_cancellation_retains_pending_work_and_new_request_survives_worker_drain() {
        for restart_before_exit in [false, true] {
            let (_temp, engine, roots) = foreground_fixture(2);
            let (a, b) = (&roots[0], &roots[1]);
            let steps = watch_discovery(&engine);
            engine
                .request(json!({"action":"scan", "metadata_coverage":true}))
                .unwrap();
            let release = finish_discovery_job(&steps, &a.path);
            engine.cancel_scan();
            let cancelled = engine.snapshot().unwrap().foreground_scan.unwrap();
            assert!(!cancelled.active);
            assert!(!cancelled.stats.complete);
            assert!(cancelled.stats.cancelled);
            assert_eq!(cancelled.stats.entries, 3);
            assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
            if !restart_before_exit {
                release.send(()).unwrap();
                wait_for_discovery_idle(&engine);
                assert_eq!(
                    serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap())
                        .unwrap(),
                    serde_json::to_value(cancelled).unwrap()
                );
                assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
                engine
                    .request(json!({"action":"scan", "root_id":b.id, "metadata_coverage":true}))
                    .unwrap();
            } else {
                engine
                    .request(json!({"action":"scan", "root_id":b.id, "metadata_coverage":true}))
                    .unwrap();
                let saved = engine
                    .store
                    .lock()
                    .unwrap()
                    .load_foreground_summary()
                    .unwrap()
                    .unwrap();
                assert!(saved.stats.cancelled && !saved.active);
                assert_eq!(
                    saved.stats.entries, cancelled.stats.entries,
                    "Replacing a cancelled request must save it before its worker drains"
                );
                release.send(()).unwrap();
            }
            let release = finish_discovery_job(&steps, &b.path);
            let completed = engine.snapshot().unwrap().foreground_scan.unwrap();
            assert!(!completed.active);
            assert!(completed.stats.complete);
            assert!(!completed.stats.cancelled);
            assert_eq!(
                completed.stats.entries, 3,
                "The new request includes only its selected root"
            );
            release.send(()).unwrap();
            wait_for_discovery_idle(&engine);
        }
    }

    #[test]
    fn cancelled_claim_cannot_adopt_or_consume_a_new_foreground_request() {
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let steps = watch_discovery(&engine);
        dirty_scope(&engine, root, &root.path);
        let release = discovery_step(&steps, DiscoveryStage::Claimed, &root.path);
        engine.cancel_scan();
        engine
            .request(json!({"action":"scan", "metadata_coverage":true}))
            .unwrap();
        release.send(()).unwrap();
        // The cancelled claim never crosses begin-refresh, so it cannot discard
        // the new root or borrow that request's ticket while cancel is still set.
        let release = discovery_step(&steps, DiscoveryStage::Finished, &root.path);
        let foreground = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(foreground.active);
        assert_eq!(foreground.stats.entries, 0);
        assert!(!foreground.stats.cancelled);
        assert!(engine.store.lock().unwrap().has_pending_scopes().unwrap());
        release.send(()).unwrap();
        finish_discovery_job(&steps, &root.path).send(()).unwrap();
        wait_for_discovery_idle(&engine);
        let foreground = engine.snapshot().unwrap().foreground_scan.unwrap();
        assert!(foreground.stats.complete);
        assert!(!foreground.active);
        assert_eq!(foreground.stats.entries, 3);
    }

    #[test]
    fn startup_resume_or_watcher_captures_only_already_pending_full_roots() {
        for watcher_first in [false, true] {
            let (_temp, engine, roots) = foreground_fixture(2);
            let (a, b) = (&roots[0], &roots[1]);
            {
                let mut store = engine.store.lock().unwrap();
                store.enqueue_scope(&a.id, &a.path).unwrap();
                store.enqueue_scope(&b.id, &b.path.join("child")).unwrap();
            }
            let steps = watch_discovery(&engine);
            if watcher_first {
                dirty_scope(&engine, b, &b.path.join("child"));
            } else {
                engine.request(json!({"action":"resume"})).unwrap();
            }
            let release = finish_discovery_job(&steps, &a.path);
            let snapshot = engine.snapshot().unwrap();
            assert!(snapshot.scanning);
            let foreground = snapshot.foreground_scan.unwrap();
            assert!(!foreground.active);
            assert!(foreground.stats.complete);
            assert_eq!(
                foreground.stats.entries, 3,
                "Only the queued full root belongs to startup's finite pass"
            );
            let frozen = serde_json::to_value(foreground).unwrap();
            engine.request(json!({"action":"resume"})).unwrap();
            dirty_scope(&engine, a, &a.path.join("child"));
            release.send(()).unwrap();
            for path in [b.path.join("child"), a.path.join("child")] {
                finish_discovery_job(&steps, &path).send(()).unwrap();
            }
            wait_for_discovery_idle(&engine);
            assert_eq!(
                serde_json::to_value(engine.snapshot().unwrap().foreground_scan.unwrap()).unwrap(),
                frozen
            );
        }
        let (_temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let steps = watch_discovery(&engine);
        dirty_scope(&engine, root, &root.path.join("child"));
        let release = finish_discovery_job(&steps, &root.path.join("child"));
        assert!(
            engine.snapshot().unwrap().foreground_scan.is_none(),
            "An incremental replay must not create a foreground scan"
        );
        release.send(()).unwrap();
        wait_for_discovery_idle(&engine);
    }

    #[test]
    fn foreground_partial_counts_and_stale_tickets_cannot_be_overwritten() {
        let (_temp, _engine, roots) = foreground_fixture(2);
        let mut request = ForegroundRequest::new(1, &roots, 0);
        let a = request.claim(&roots[0].id, &roots[0].path).unwrap();
        let b = request.claim(&roots[1].id, &roots[1].path).unwrap();
        let partial = ScanStats {
            entries: 17,
            errors: 2,
            candidates: 1,
            first_finding_ms: Some(4),
            ..Default::default()
        };
        request.progress(&a, &partial);
        request.finish(&a, Ok(&partial));
        let completed_root = ScanStats {
            entries: 9,
            complete: true,
            message: "Scan complete".into(),
            ..Default::default()
        };
        request.progress(&b, &completed_root);
        assert!(request.snapshot.active);
        assert_ne!(request.snapshot.stats.message, "Scan complete");
        request.finish(&b, Ok(&completed_root));
        assert!(!request.snapshot.active);
        assert!(!request.snapshot.stats.complete);
        assert_eq!(request.snapshot.stats.entries, 26);
        assert_eq!(request.snapshot.stats.errors, 2);
        assert_eq!(request.snapshot.stats.candidates, 1);
        assert!(request.snapshot.stats.first_finding_ms.is_some());
        let frozen = serde_json::to_value(&request.snapshot).unwrap();
        request.progress(&a, &ScanStats::default());
        request.stop(true, "late cancellation");
        assert_eq!(serde_json::to_value(&request.snapshot).unwrap(), frozen);
        let mut next = ForegroundRequest::new(2, &roots, 0);
        next.progress(&a, &partial);
        next.finish(&b, Err("old worker failure".into()));
        assert!(next.snapshot.active);
        assert_eq!(next.snapshot.stats.entries, 0);
        assert_eq!(next.snapshot.stats.errors, 0);
    }

    #[test]
    fn foreground_worker_panic_finishes_incomplete_without_losing_durable_scopes() {
        let (_temp, engine, _roots) = foreground_fixture(2);
        *engine.discovery_observer.lock().unwrap() = Some(Arc::new(|stage, _, _| {
            if stage == DiscoveryStage::Claimed {
                panic!("Disposable discovery boundary failure");
            }
        }));
        engine.request(json!({"action":"scan"})).unwrap();
        wait_for_discovery_idle(&engine);
        let snapshot = engine.snapshot().unwrap();
        let foreground = snapshot.foreground_scan.unwrap();
        assert!(!foreground.active);
        assert!(!foreground.stats.complete);
        assert_eq!(foreground.stats.errors, 1);
        assert!(snapshot.error.unwrap().contains("internal error"));
        let store = engine.store.lock().unwrap();
        let durable: u64 = store.conn.query_row("SELECT (SELECT count(*) FROM pending_scopes) + (SELECT count(*) FROM active_scopes)", [], |row| row.get(0)).unwrap();
        assert_eq!(durable, 2);
        assert!(store.history().unwrap().is_empty());
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[test]
    fn discovery_journal_failure_retains_replay_and_can_resume_without_restart() {
        for failure_at in [DiscoveryStage::Claimed, DiscoveryStage::Began] {
            let (_temp, engine, roots) = foreground_fixture(2);
            let root = &roots[0];
            let steps = watch_discovery(&engine);
            engine
                .request(json!({"action":"scan", "metadata_coverage":true}))
                .unwrap();
            let mut release = discovery_step(&steps, DiscoveryStage::Claimed, &root.path);
            if failure_at == DiscoveryStage::Began {
                release.send(()).unwrap();
                release = discovery_step(&steps, DiscoveryStage::Began, &root.path);
            }
            let trigger = if failure_at == DiscoveryStage::Claimed {
                "CREATE TEMP TRIGGER fail_journal BEFORE INSERT ON refreshes BEGIN SELECT RAISE(ABORT,'disposable start failure'); END;"
            } else {
                "CREATE TEMP TRIGGER fail_journal BEFORE DELETE ON active_scopes BEGIN SELECT RAISE(ABORT,'disposable finish failure'); END;"
            };
            engine
                .store
                .lock()
                .unwrap()
                .conn
                .execute_batch(trigger)
                .unwrap();
            release.send(()).unwrap();
            wait_for_discovery_idle(&engine);
            let snapshot = engine.snapshot().unwrap();
            let foreground = snapshot.foreground_scan.unwrap();
            assert!(!foreground.active);
            assert!(!foreground.stats.complete);
            assert_eq!(foreground.stats.errors, 1);
            assert!(snapshot.error.unwrap().contains("disposable"));
            let store = engine.store.lock().unwrap();
            let (active, pending, refreshes): (u64, u64, u64) = store.conn.query_row(
                "SELECT (SELECT count(*) FROM active_scopes),(SELECT count(*) FROM pending_scopes),(SELECT count(*) FROM refreshes)",
                [], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
            ).unwrap();
            assert_eq!(
                (active, pending),
                if failure_at == DiscoveryStage::Claimed {
                    (0, 2)
                } else {
                    (1, 1)
                },
                "Failed recovery stays journaled; a recoverable start error is requeued immediately"
            );
            assert_eq!(refreshes, u64::from(failure_at == DiscoveryStage::Began));
            assert_eq!(
                store.latest_stats().unwrap().entries,
                0,
                "Failed finalization must not persist a successful scan result"
            );
            assert!(store.history().unwrap().is_empty());
            assert_eq!(store.wallet().unwrap().credited_bytes, 0);
            assert_eq!(
                fs::read(root.path.join("child/preserve.txt")).unwrap(),
                b"disposable source"
            );
            store
                .conn
                .execute_batch("DROP TRIGGER fail_journal")
                .unwrap();
            drop(store);
            *engine.discovery_observer.lock().unwrap() = None;
            engine
                .request(json!({"action":"scan", "metadata_coverage":true}))
                .unwrap();
            wait_for_discovery_idle(&engine);
            let snapshot = engine.snapshot().unwrap();
            assert!(snapshot.foreground_scan.unwrap().stats.complete);
            let store = engine.store.lock().unwrap();
            assert!(!store.has_active_scopes().unwrap());
            assert!(!store.has_pending_scopes().unwrap());
            assert!(store.history().unwrap().is_empty());
            assert_eq!(store.wallet().unwrap().credited_bytes, 0);
        }
    }

    #[test]
    fn legacy_snapshot_without_foreground_scan_decodes_and_empty_request_finishes() {
        let (_temp, engine, _roots) = foreground_fixture(0);
        let mut legacy = serde_json::to_value(engine.snapshot().unwrap()).unwrap();
        legacy.as_object_mut().unwrap().remove("foreground_scan");
        assert!(
            serde_json::from_value::<Snapshot>(legacy)
                .unwrap()
                .foreground_scan
                .is_none()
        );
        engine.request(json!({"action":"scan"})).unwrap();
        let snapshot = engine.snapshot().unwrap();
        assert!(!snapshot.scanning);
        let foreground = snapshot.foreground_scan.unwrap();
        assert!(!foreground.active);
        assert!(foreground.stats.complete);
        assert_eq!(foreground.stats.entries, 0);
    }

    #[test]
    fn queued_home_media_scope_is_reconciled_without_a_filesystem_probe() {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let home = base.join("Home");
        fs::create_dir_all(home.join("Music")).unwrap();
        let sentinel = home.join("Music/preserve");
        fs::write(&sentinel, b"personal media").unwrap();
        let engine = Engine::open(&base.join("library.sqlite"), None).unwrap();
        let root: Root = serde_json::from_value(
            engine
                .request(json!({"action": "authorize", "path": home, "kind": "home"}))
                .unwrap(),
        )
        .unwrap();
        {
            let mut store = engine.store.lock().unwrap();
            store
                .enqueue_scope(&root.id, &home.join("Music/previously-indexed"))
                .unwrap();
            assert!(store.take_scope().unwrap().is_some());
        }
        engine
            .scan_root(&root.id, &home.join("Music/previously-indexed"), &mut None)
            .unwrap();
        let runtime = engine.runtime.lock().unwrap();
        assert_eq!(runtime.stats.entries, 0);
        assert_eq!(runtime.stats.skipped, 1);
        assert_eq!(runtime.stats.errors, 0);
        assert!(runtime.stats.complete);
        assert!(runtime.stats.message.contains("without filesystem access"));
        assert_eq!(fs::read(&sentinel).unwrap(), b"personal media");
    }

    #[test]
    fn history_action_pages_receipts_with_cursors_totals_and_sequences() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        {
            let store = engine.store.lock().unwrap();
            for index in 0..5 {
                let receipt = Receipt {
                    id: format!("op-{index}"),
                    path: "/scope/item".into(),
                    title: "Disposable artifacts".into(),
                    operation: "permanent".into(),
                    outcome: "removed".into(),
                    detail: String::new(),
                    created_at: now(),
                    reported_bytes: 0,
                    observed_bytes: 0,
                    credited_bytes: 0,
                    coins: 0,
                    trash_path: None,
                    can_restore: false,
                    seq: None,
                };
                store
                    .conn
                    .execute(
                        "INSERT INTO operations VALUES(?1,'{}','{}',?2,NULL,NULL,'removed')",
                        rusqlite::params![receipt.id, serde_json::to_string(&receipt).unwrap()],
                    )
                    .unwrap();
            }
        }
        let first = engine
            .request(json!({"action":"history","limit":2}))
            .unwrap();
        assert_eq!(first["total"], 5);
        assert_eq!(first["receipts"].as_array().unwrap().len(), 2);
        assert_eq!(first["receipts"][0]["id"], "op-4");
        assert_eq!(first["receipts"][1]["id"], "op-3");
        let cursor = first["next_before"].as_i64().unwrap();
        assert_eq!(first["receipts"][1]["seq"].as_i64(), Some(cursor));
        let second = engine
            .request(json!({"action":"history","before":cursor,"limit":2}))
            .unwrap();
        assert_eq!(second["receipts"][0]["id"], "op-2");
        assert_eq!(second["receipts"][1]["id"], "op-1");
        let last = engine
            .request(json!({"action":"history","before":second["next_before"].as_i64().unwrap()}))
            .unwrap();
        assert_eq!(last["receipts"].as_array().unwrap().len(), 1);
        assert_eq!(last["receipts"][0]["id"], "op-0");
        assert!(last["next_before"].is_null());
        assert_eq!(last["total"], 5);
        let sequences: Vec<i64> = [&first, &second, &last]
            .iter()
            .flat_map(|page| page["receipts"].as_array().unwrap())
            .map(|receipt| receipt["seq"].as_i64().unwrap())
            .collect();
        assert!(
            sequences.windows(2).all(|pair| pair[1] < pair[0]),
            "Sequences must strictly decrease across pages: {sequences:?}"
        );
        // An oversized limit is clamped rather than refused, and the bounded
        // snapshot history keeps omitting the sequence field entirely.
        let clamped = engine
            .request(json!({"action":"history","limit":100_000}))
            .unwrap();
        assert_eq!(clamped["receipts"].as_array().unwrap().len(), 5);
        let snapshot = serde_json::to_value(engine.snapshot().unwrap()).unwrap();
        assert_eq!(snapshot["history"].as_array().unwrap().len(), 5);
        assert!(snapshot["history"][0].get("seq").is_none());
    }

    // Model previously indexed rows without allocating cleanup-sized payloads.
    // These tests exercise controller rejection; no successful cleanup is requested.
    fn keep_overlap_fixture(
        kept_relative: &str,
    ) -> (tempfile::TempDir, Arc<Engine>, Candidate, Candidate) {
        let (temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let artifact = root.path.join("project/.venv");
        let kept_path = root.path.join(kept_relative);
        fs::create_dir_all(&artifact).unwrap();
        fs::create_dir_all(&kept_path).unwrap();
        fs::write(artifact.join("preserve.txt"), b"preserve this artifact").unwrap();
        let selected = Candidate {
            id: "selected-parent".into(),
            root_id: root.id.clone(),
            identity: safety::identity(&artifact).unwrap(),
            path: artifact,
            title: "Previously indexed environment".into(),
            kind: "venv".into(),
            logical_bytes: 100_000_000,
            allocated_bytes: 100_000_000,
            file_count: 1,
            modified_ns: 0,
            explanation: "Synthetic prior index row for controller checks".into(),
            consequence: "Recreate environment".into(),
            eligible_permanent: true,
            blocked_reason: None,
            fingerprint: "synthetic prior fingerprint".into(),
            evidence: "synthetic prior evidence".into(),
            suggestion_eligible: true,
            provisional: false,
        };
        let kept = if kept_path == selected.path {
            selected.clone()
        } else {
            Candidate {
                id: "kept-path".into(),
                identity: safety::identity(&kept_path).unwrap(),
                path: kept_path,
                eligible_permanent: false,
                suggestion_eligible: false,
                blocked_reason: Some("Keep-only controller fixture".into()),
                ..selected.clone()
            }
        };
        let mut candidates = vec![selected.clone()];
        if kept.id != selected.id {
            candidates.push(kept.clone());
        }
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates,
                stats: ScanStats::default(),
            })
            .unwrap();
        (temp, engine, selected, kept)
    }

    // Controller-only fixture: the report is seeded directly to exercise
    // admission without claiming that these tiny files passed discovery or
    // content verification. End-to-end duplicate fixtures live in discovery.rs.
    fn duplicate_review_fixture() -> (tempfile::TempDir, Arc<Engine>, [Candidate; 2], Value) {
        let (temp, engine, roots) = foreground_fixture(1);
        let root = &roots[0];
        let files = ["keeper.dmg", "copy.dmg"].map(|name| {
            let path = root.path.join("child").join(name);
            fs::write(&path, b"disposable equal copies").unwrap();
            Candidate {
                id: name.into(),
                identity: safety::identity(&path).unwrap(),
                path,
                blocked_reason: None,
                suggestion_eligible: true,
                ..indexed_fixture_source(root, name)
            }
        });
        engine
            .store
            .lock()
            .unwrap()
            .save_batch(&ScanBatch {
                candidates: files.to_vec(),
                stats: ScanStats::default(),
            })
            .unwrap();
        engine.duplicate_state.lock().unwrap().report = Some(DuplicateReportState {
            token: "report".into(),
            created: Instant::now(),
            groups: vec![(
                "group".into(),
                duplicates::Group {
                    items: files
                        .iter()
                        .map(|candidate| duplicates::Input {
                            root: root.clone(),
                            candidate: candidate.clone(),
                            keeper_only: false,
                        })
                        .collect(),
                },
            )],
        });
        let request = json!({"action":"prepare_duplicate", "operation":"trash",
            "report_token":"report", "group_id":"group",
            "keeper_id":files[0].id, "copy_id":files[1].id});
        (temp, engine, files, request)
    }

    #[test]
    fn duplicate_reviews_bind_choices_expiry_and_keeper_reservations() {
        let (_temp, engine, files, request) = duplicate_review_fixture();
        for (field, value) in [
            ("operation", "permanent"),
            ("report_token", "wrong"),
            ("group_id", "wrong"),
            ("keeper_id", "wrong"),
            ("copy_id", "keeper.dmg"),
        ] {
            let mut invalid = request.clone();
            invalid[field] = json!(value);
            assert!(engine.request(invalid).is_err(), "{field}");
        }
        let prepared = engine.request(request.clone()).unwrap();
        assert!(prepared["token"].is_string());
        let error = engine
            .request(json!({"action":"prepare", "operation":"trash",
            "items":[files[0]]}))
            .unwrap_err();
        assert!(error.contains("reserved"), "{error}");
        let mut reversed = request.clone();
        reversed["keeper_id"] = json!(files[1].id);
        reversed["copy_id"] = json!(files[0].id);
        assert!(engine.request(reversed).unwrap_err().contains("reserved"));
        engine
            .duplicate_state
            .lock()
            .unwrap()
            .report
            .as_mut()
            .unwrap()
            .created = Instant::now() - DUPLICATE_REVIEW_LIFETIME;
        assert!(engine.request(request).unwrap_err().contains("expired"));
        assert!(engine.snapshot().unwrap().history.is_empty());
        for file in files {
            assert_eq!(fs::read(file.path).unwrap(), b"disposable equal copies");
        }
    }

    #[test]
    fn review_admission_cannot_promise_a_keeper_after_mutation_admission() {
        for duplicate in [false, true] {
            let (_temp, engine, files, duplicate_request) = duplicate_review_fixture();
            let request = if duplicate {
                duplicate_request
            } else {
                json!({"action":"prepare", "operation":"trash", "items":[files[0]]})
            };
            let (ready_tx, ready) = std::sync::mpsc::channel();
            let (release_tx, release) = std::sync::mpsc::channel();
            let release = Mutex::new(release);
            *engine.review_admission_observer.lock().unwrap() = Some(Arc::new(move || {
                ready_tx.send(()).unwrap();
                release
                    .lock()
                    .unwrap()
                    .recv_timeout(Duration::from_secs(5))
                    .unwrap();
            }));
            let reviewing = Arc::clone(&engine);
            let prepare = std::thread::spawn(move || reviewing.request(request));
            ready.recv_timeout(Duration::from_secs(5)).unwrap();
            let mutating = Arc::clone(&engine);
            let (finished_tx, finished) = std::sync::mpsc::channel();
            let mutation = std::thread::spawn(move || {
                let _guard = mutating.begin_mutation().unwrap();
                finished.recv_timeout(Duration::from_secs(5)).unwrap();
            });
            let deadline = Instant::now() + Duration::from_secs(5);
            while !engine.cleaning.load(Ordering::Acquire) {
                assert!(
                    Instant::now() < deadline,
                    "Mutation never crossed admission"
                );
                std::thread::yield_now();
            }
            release_tx.send(()).unwrap();
            let error = prepare.join().unwrap().unwrap_err();
            assert!(error.contains("current file operation"), "{error}");
            assert!(engine.reviews.lock().unwrap().is_empty());
            finished_tx.send(()).unwrap();
            mutation.join().unwrap();
            assert!(!engine.cleaning.load(Ordering::Acquire));
            assert!(files.iter().all(|file| file.path.is_file()));
        }
    }

    #[test]
    fn duplicate_cancellation_does_not_pause_discovery_or_cancel_other_reviews() {
        let (_temp, engine, files, _) = duplicate_review_fixture();
        let prepared = engine
            .request(json!({"action":"prepare", "operation":"trash",
            "items":[files[0]]}))
            .unwrap();
        let generation = engine.cancel_generation.load(Ordering::Acquire);
        let before = engine.runtime.lock().unwrap().stats.clone();
        let database = engine.store.lock().unwrap();
        let checking = Arc::clone(&engine);
        let worker =
            std::thread::spawn(move || checking.request(json!({"action":"check_duplicates"})));
        let deadline = Instant::now() + Duration::from_secs(5);
        while !engine.checking_duplicates.load(Ordering::Acquire) {
            assert!(Instant::now() < deadline, "Duplicate check never started");
            std::thread::yield_now();
        }
        engine
            .request(json!({"action":"cancel_duplicates"}))
            .unwrap();
        assert!(!engine.scan_paused.load(Ordering::Acquire));
        assert_eq!(engine.cancel_generation.load(Ordering::Acquire), generation);
        drop(database);
        assert!(worker.join().unwrap().is_err());
        assert!(engine.duplicate_state.lock().unwrap().report.is_none());
        assert!(!engine.busy.load(Ordering::Acquire));
        assert_eq!(
            serde_json::to_value(engine.runtime.lock().unwrap().stats.clone()).unwrap(),
            serde_json::to_value(before).unwrap()
        );
        let token = prepared["token"].as_str().unwrap();
        let reviews = engine.reviews.lock().unwrap();
        let review = reviews.get(token).unwrap();
        assert_eq!(review.cancel_generation, generation);
        assert!(review_is_live(review));
        drop(reviews);
        assert!(engine.request(json!({"action":"snapshot"})).is_ok());
        // Empty-input checks also cannot publish evidence after cancellation.
        let guard = engine.begin_duplicate_check().unwrap();
        engine.cancel_duplicates();
        assert!(engine.check_duplicates().is_err());
        drop(guard);
        assert!(engine.duplicate_state.lock().unwrap().report.is_none());
    }

    #[test]
    fn keep_overlap_blocks_review_but_not_sibling_prefixes() {
        for operation in ["trash", "permanent"] {
            for (kept_relative, overlaps) in [
                ("project", true),
                ("project/.venv", true),
                ("project/.venv/kept", true),
                ("project/.venv-other/kept", false),
                ("project/.ven", false),
            ] {
                let (_temp, engine, selected, kept) = keep_overlap_fixture(kept_relative);
                engine
                    .request(json!({"action":"keep","id":kept.id}))
                    .unwrap();
                let prepared = engine.request(json!({
                    "action":"prepare", "operation":operation, "items":[&selected]
                }));
                if overlaps {
                    let error = prepared.unwrap_err();
                    assert!(
                        error.contains("Keep"),
                        "{operation}: {kept_relative}: {error}"
                    );
                    assert!(engine.reviews.lock().unwrap().is_empty());
                } else {
                    assert!(prepared.unwrap()["token"].is_string());
                }
                let snapshot = engine.snapshot().unwrap();
                assert_eq!(
                    snapshot.candidates.iter().any(|c| c.id == selected.id),
                    !overlaps,
                    "{kept_relative}"
                );
                assert_eq!(snapshot.kept_paths, [kept.path.to_str().unwrap()]);
                assert_eq!(
                    fs::read(selected.path.join("preserve.txt")).unwrap(),
                    b"preserve this artifact"
                );
            }
        }
    }

    #[test]
    fn keeping_a_descendant_after_review_blocks_execution_before_mutation() {
        for operation in ["trash", "permanent"] {
            let (_temp, engine, selected, kept) = keep_overlap_fixture("project/.venv/kept");
            let prepared = engine
                .request(json!({
                    "action":"prepare", "operation":operation, "items":[&selected]
                }))
                .unwrap();
            engine
                .request(json!({"action":"keep","id":kept.id}))
                .unwrap();
            let before = engine.snapshot().unwrap();
            let error = engine
                .request(json!({
                    "action":"execute", "token":prepared["token"], "confirmed":true
                }))
                .unwrap_err();
            assert!(error.contains("Keep"), "{operation}: {error}");
            let after = engine.snapshot().unwrap();
            assert_eq!(after.kept_paths, [kept.path.to_str().unwrap()]);
            assert!(after.history.is_empty());
            assert_eq!(
                serde_json::to_value(after.wallet).unwrap(),
                serde_json::to_value(before.wallet).unwrap()
            );
            let store = engine.store.lock().unwrap();
            assert_eq!(store.candidate(&selected.id).unwrap(), selected);
            let mutations: u64 = store
                .conn
                .query_row(
                    "SELECT (SELECT count(*) FROM candidate_tombstones)
                          + (SELECT count(*) FROM pending_scopes)
                          + (SELECT count(*) FROM operations)
                          + (SELECT count(*) FROM windows)
                          + (SELECT count(*) FROM allocations)
                          + (SELECT count(*) FROM earnings)",
                    [],
                    |row| row.get(0),
                )
                .unwrap();
            assert_eq!(mutations, 0, "Keep rejection must precede every mutation");
            assert_eq!(
                fs::read(selected.path.join("preserve.txt")).unwrap(),
                b"preserve this artifact"
            );
            assert!(!engine.cleaning.load(Ordering::Acquire));
            assert!(!engine.pause_requested.load(Ordering::Acquire));
        }
    }

    #[test]
    fn cleanup_progress_remains_readable_while_mutation_owns_the_database() {
        let temp = tempfile::tempdir().unwrap();
        let engine = Engine::open(&temp.path().join("library.sqlite"), None).unwrap();
        *engine.cleanup_progress.lock().unwrap() = Some(CleanupProgress {
            phase: cleanup::CleanupPhase::Removing,
            completed_entries: 40,
            total_entries: 100,
            item_number: 1,
            item_count: 2,
            title: "Disposable artifact".into(),
        });
        let database = engine.store.lock().unwrap();
        let reader = Arc::clone(&engine);
        let (send, receive) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            send.send(reader.request(json!({"action":"cleanup_progress"})))
                .unwrap();
        });
        let progress = receive
            .recv_timeout(Duration::from_secs(2))
            .expect("Progress waited for the mutation's database lock")
            .unwrap();
        assert_eq!(progress["phase"], "removing");
        assert_eq!(progress["completed_entries"], 40);
        assert_eq!(progress["total_entries"], 100);
        drop(database);
        worker.join().unwrap();
    }

    #[test]
    fn completed_finding_can_be_deleted_while_discovery_is_parked_then_resumes() {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let projects = base.join("Projects");
        let project = projects.join("Disposable");
        let artifact = project.join("target");
        fs::create_dir_all(artifact.join("debug/Fixture.app/Contents")).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            "[package]\nname=\"disposable\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        fs::write(
            artifact.join("CACHEDIR.TAG"),
            "Signature: 8a477f597d28d172789f06886806bc55\n",
        )
        .unwrap();
        let sentinel = base.join("preserve.txt");
        fs::write(&sentinel, "outside target: must survive").unwrap();
        std::os::unix::fs::symlink(&sentinel, artifact.join("debug/external-link")).unwrap();
        let payload = artifact.join("debug/Fixture.app/Contents/payload");
        let mut file = File::create(&payload).unwrap();
        let chunk = vec![19; 1024 * 1024];
        for _ in 0..100 {
            file.write_all(&chunk).unwrap();
        }
        file.sync_all().unwrap();
        drop(file);
        let old = SystemTime::now() - Duration::from_secs(9 * 86_400);
        for path in [
            payload,
            artifact.join("CACHEDIR.TAG"),
            project.join("Cargo.toml"),
            artifact.join("debug/Fixture.app/Contents"),
            artifact.join("debug/Fixture.app"),
            artifact.join("debug"),
            artifact.clone(),
            project.clone(),
        ] {
            File::open(path)
                .unwrap()
                .set_times(fs::FileTimes::new().set_modified(old))
                .unwrap();
        }
        // Date the symlink itself, never its target.
        use std::os::unix::ffi::OsStrExt;
        let link =
            CString::new(artifact.join("debug/external-link").as_os_str().as_bytes()).unwrap();
        let seconds = old
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64;
        let times = [libc::timespec {
            tv_sec: seconds,
            tv_nsec: 0,
        }; 2];
        assert_eq!(
            unsafe {
                libc::utimensat(
                    libc::AT_FDCWD,
                    link.as_ptr(),
                    times.as_ptr(),
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            },
            0
        );
        let engine = Engine::open(&base.join("library.sqlite"), None).unwrap();
        let root: Root = serde_json::from_value(
            engine
                .request(json!({"action":"authorize","path":projects,"kind":"projects"}))
                .unwrap(),
        )
        .unwrap();
        scanner::scan(&root, None, &AtomicBool::new(false), |batch| {
            engine.store.lock().unwrap().save_batch(&batch).unwrap();
        })
        .unwrap();
        let candidate = engine
            .snapshot()
            .unwrap()
            .candidates
            .into_iter()
            .next()
            .expect("Old disposable target should be reviewable");
        engine
            .store
            .lock()
            .unwrap()
            .enqueue_scope(&root.id, &root.path)
            .unwrap();
        engine.pause_requested.store(true, Ordering::Release);
        engine.launch_scan(ScanLaunch::Immediate).unwrap();
        let parked = engine.parked.lock().unwrap();
        let (parked, timeout) = engine
            .pause_changed
            .wait_timeout_while(parked, Duration::from_secs(2), |parked| !*parked)
            .unwrap();
        assert!(
            !timeout.timed_out(),
            "Discovery did not reach its checkpoint"
        );
        drop(parked);
        assert!(engine.snapshot().unwrap().scanning);
        assert_eq!(
            engine.request(json!({"action":"scan"})).unwrap()["already_scanning"],
            true
        );
        let prepared = engine
            .request(json!({"action":"prepare","operation":"permanent","items":[candidate]}))
            .unwrap();
        let receipts = engine
            .request(json!({"action":"execute","token":prepared["token"],"confirmed":true}))
            .unwrap();
        assert_eq!(receipts[0]["outcome"], "removed", "{receipts}");
        assert!(!artifact.exists());
        assert_eq!(
            fs::read_to_string(&sentinel).unwrap(),
            "outside target: must survive"
        );
        assert!(project.join("Cargo.toml").exists());
        let deadline = Instant::now() + Duration::from_secs(5);
        while engine.snapshot().unwrap().scanning {
            assert!(Instant::now() < deadline, "Discovery failed to resume");
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(
            engine.snapshot().unwrap().candidates.is_empty(),
            "A stale scan must not resurrect a cleaned finding"
        );
        assert!(
            engine
                .request(json!({"action":"execute","token":prepared["token"],"confirmed":true}))
                .is_err()
        );
        assert!(!engine.cleaning.load(Ordering::Acquire));
        assert!(!engine.pause_requested.load(Ordering::Acquire));
    }
}
