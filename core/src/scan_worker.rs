//! Process-isolated, read-only scan helper protocol.
//!
//! The helper is deliberately a thin transport boundary.  It resolves the
//! same lexical scope as the in-process engine and delegates traversal to the
//! existing scanner; it has no store, cleanup, reward, or authorization
//! authority.  The coordinator owns admission, cancellation fencing, and
//! durable publication.

use crate::model::{Root, ScanBatch, ScanStats};
use crate::refresh::RecentFileHints;
use crate::{refresh, safety, scanner};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::collections::VecDeque;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread;
use std::time::{Duration, Instant};

/// A frame is rejected before its body is allocated.  This applies to both
/// requests and events; scanner batches are expected to stay below this size.
pub(crate) const MAX_FRAME_BYTES: usize = 1024 * 1024;
/// A coordinator may retain at most two frames per job, reserving one slot for
/// a terminal outcome. These are transport-admission constants, not a scanner
/// traversal limit; output remains streaming and backpressure is intentional.
pub(crate) const MAX_QUEUED_EVENT_FRAMES: usize = 2;
pub(crate) const MAX_QUEUED_EVENT_BYTES: usize = 2 * MAX_FRAME_BYTES;
pub(crate) const MAX_DIAGNOSTIC_BYTES: usize = 16 * 1024;

/// One read-only traversal request.  `indexed` and `enclosing_parent` are
/// snapshots supplied by the durable coordinator; the helper never queries a
/// database to infer them.
#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct ScanRequest {
    pub root: Root,
    pub requested: PathBuf,
    #[serde(default)]
    pub indexed: Option<PathBuf>,
    #[serde(default)]
    pub enclosing_parent: Option<PathBuf>,
    #[serde(default)]
    pub kept: Vec<PathBuf>,
    #[serde(default)]
    pub metadata_coverage: bool,
    #[serde(default)]
    pub recent_files: Option<RecentFileHints>,
}

/// Events are ordered on one helper stdout stream.  `Resolved` is always the
/// first event for an accepted request; `Finished` or `Failed` is terminal.
#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "type", content = "data", rename_all = "snake_case")]
pub(crate) enum ScanEvent {
    Resolved {
        path: PathBuf,
        cargo_lock: bool,
    },
    Batch(ScanBatch),
    Finished {
        stats: ScanStats,
        #[serde(default)]
        recent_files: Option<RecentFileHints>,
    },
    Failed(String),
}

#[derive(Debug)]
pub(crate) enum FrameError {
    Io(io::Error),
    TooLarge { length: usize, limit: usize },
    Truncated { expected: usize, received: usize },
    Empty,
    InvalidJson(serde_json::Error),
    Protocol(String),
}

impl std::fmt::Display for FrameError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "scan-helper transport I/O: {error}"),
            Self::TooLarge { length, limit } => {
                write!(
                    formatter,
                    "scan-helper frame is {length} bytes (limit {limit})"
                )
            }
            Self::Truncated { expected, received } => write!(
                formatter,
                "scan-helper frame truncated after {received} of {expected} bytes"
            ),
            Self::Empty => formatter.write_str("scan-helper frame is empty"),
            Self::InvalidJson(error) => write!(formatter, "scan-helper JSON frame: {error}"),
            Self::Protocol(error) => write!(formatter, "scan-helper protocol: {error}"),
        }
    }
}

impl std::error::Error for FrameError {}

impl From<io::Error> for FrameError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Read one big-endian length-prefixed body.  EOF before a new prefix is a
/// clean stream end; EOF in a prefix or body is always a protocol failure.
pub(crate) fn read_frame<R: Read>(reader: &mut R) -> Result<Option<Vec<u8>>, FrameError> {
    let mut prefix = [0u8; 4];
    let mut received = 0;
    while received < prefix.len() {
        let count = reader.read(&mut prefix[received..])?;
        if count == 0 {
            if received == 0 {
                return Ok(None);
            }
            return Err(FrameError::Truncated {
                expected: prefix.len(),
                received,
            });
        }
        received += count;
    }
    let length = u32::from_be_bytes(prefix) as usize;
    if length == 0 {
        return Err(FrameError::Empty);
    }
    if length > MAX_FRAME_BYTES {
        return Err(FrameError::TooLarge {
            length,
            limit: MAX_FRAME_BYTES,
        });
    }
    let mut body = vec![0u8; length];
    let mut received = 0;
    while received < length {
        let count = reader.read(&mut body[received..])?;
        if count == 0 {
            return Err(FrameError::Truncated {
                expected: length,
                received,
            });
        }
        received += count;
    }
    Ok(Some(body))
}

pub(crate) fn read_json_frame<R: Read, T: DeserializeOwned>(
    reader: &mut R,
) -> Result<Option<T>, FrameError> {
    let Some(body) = read_frame(reader)? else {
        return Ok(None);
    };
    serde_json::from_slice(&body)
        .map(Some)
        .map_err(FrameError::InvalidJson)
}

/// Serialize before writing the prefix, so a failed serialization can never
/// leave a receiver waiting for a body that will not arrive.  The body is
/// capped before either prefix or body is written.
pub(crate) fn write_json_frame<W: Write, T: Serialize>(
    writer: &mut W,
    value: &T,
) -> Result<usize, FrameError> {
    let body = encode_json_body(value)?;
    let length = (body.len() as u32).to_be_bytes();
    writer.write_all(&length)?;
    writer.write_all(&body)?;
    Ok(body.len())
}

struct BoundedBuffer {
    bytes: Vec<u8>,
    limit: usize,
    overflowed: bool,
}

impl Write for BoundedBuffer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            self.overflowed = true;
            return Err(io::Error::new(
                io::ErrorKind::WriteZero,
                "scan-helper frame exceeds its limit",
            ));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn encode_json_body<T: Serialize>(value: &T) -> Result<Vec<u8>, FrameError> {
    let mut output = BoundedBuffer {
        bytes: Vec::with_capacity(MAX_FRAME_BYTES.min(64 * 1024)),
        limit: MAX_FRAME_BYTES,
        overflowed: false,
    };
    if let Err(error) = serde_json::to_writer(&mut output, value) {
        if output.overflowed {
            return Err(FrameError::TooLarge {
                length: MAX_FRAME_BYTES + 1,
                limit: MAX_FRAME_BYTES,
            });
        }
        return Err(FrameError::InvalidJson(error));
    }
    if output.bytes.is_empty() {
        return Err(FrameError::Empty);
    }
    Ok(output.bytes)
}

pub(crate) fn encode_json_frame<T: Serialize>(value: &T) -> Result<Vec<u8>, FrameError> {
    let body = encode_json_body(value)?;
    let mut frame = Vec::with_capacity(body.len() + 4);
    frame.extend_from_slice(&(body.len() as u32).to_be_bytes());
    frame.extend_from_slice(&body);
    Ok(frame)
}

/// Resolve the request with the same lexical rules used by `Engine::scan_root`.
/// The parent-supplied enclosing parent is used only for the exact Cargo.lock
/// dependency case; no filesystem or store probe is performed here.
pub(crate) fn resolve_request(request: &ScanRequest) -> Result<(PathBuf, bool), String> {
    let root = &request.root;
    let requested = &request.requested;
    let mut indexed = request.indexed.clone();
    if indexed.as_deref() == Some(requested.as_path())
        && refresh::cargo_lock_target(root, requested)?.is_some()
        && let Some(parent) = request.enclosing_parent.as_ref()
    {
        indexed = Some(parent.clone());
    }
    let resolved = refresh::resolve_scope(root, requested, indexed)?;
    let cargo_lock =
        requested == &resolved && refresh::cargo_lock_target(root, &resolved)?.is_some();
    Ok((resolved, cargo_lock))
}

// In addition to the anchored discovery/measurement stacks, leave room for
// stdio, transient no-follow lookups, evidence reads and bounded probe pipes.
// This changes capacity, not the number of descriptors actually retained.
const SCAN_PROCESS_DESCRIPTOR_LIMIT: libc::rlim_t =
    (scanner::MAX_SCHEDULED_DIRECTORY_FDS + 64) as libc::rlim_t;

fn descriptor_limits() -> Result<libc::rlimit, String> {
    let mut limits = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limits) } != 0 {
        return Err(format!(
            "Cannot read the scanner's file-descriptor limit: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(limits)
}

/// Reserve the fixed traversal budget in a standalone scanner process only.
///
/// The bundled helper and direct diagnostic CLI call this before scanning.
/// Never call it from the native host or a library's embedding process: limits
/// are process-wide. A sufficient inherited soft limit is left untouched; a
/// smaller one may be raised only within the unchanged inherited hard limit.
pub fn prepare_scan_process() -> Result<(), String> {
    let before = descriptor_limits()?;
    if before.rlim_cur >= SCAN_PROCESS_DESCRIPTOR_LIMIT {
        return Ok(());
    }
    if before.rlim_max < SCAN_PROCESS_DESCRIPTOR_LIMIT {
        return Err(format!(
            "The scanner's fixed file-descriptor budget needs {} descriptors, but this process has a hard limit of {}",
            SCAN_PROCESS_DESCRIPTOR_LIMIT, before.rlim_max
        ));
    }
    let requested = libc::rlimit {
        rlim_cur: SCAN_PROCESS_DESCRIPTOR_LIMIT,
        rlim_max: before.rlim_max,
    };
    if unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &requested) } != 0 {
        return Err(format!(
            "Cannot reserve the scanner's fixed file-descriptor budget: {}",
            io::Error::last_os_error()
        ));
    }
    let after = descriptor_limits()?;
    if after.rlim_cur < SCAN_PROCESS_DESCRIPTOR_LIMIT || after.rlim_max != before.rlim_max {
        return Err("The scanner's file-descriptor reservation could not be verified".into());
    }
    Ok(())
}

fn run_request<W: Write>(request: ScanRequest, output: &mut W) -> Result<(), FrameError> {
    let (resolved, cargo_lock) = resolve_request(&request).map_err(FrameError::Protocol)?;
    write_json_frame(
        output,
        &ScanEvent::Resolved {
            path: resolved.clone(),
            cargo_lock,
        },
    )?;
    output.flush()?;

    let cancel = AtomicBool::new(false);
    let mode = if request.metadata_coverage {
        scanner::ScanMode::MetadataCoverage
    } else {
        scanner::ScanMode::Suggestions
    };
    let scope = (resolved != request.root.path).then_some(resolved.as_path());
    let mut recent_files = request.recent_files;
    let mut output_error = None;
    let mut publish = |batch: ScanBatch| {
        if output_error.is_some() {
            return;
        }
        if let Err(error) = write_json_frame(output, &ScanEvent::Batch(batch))
            .and_then(|_| output.flush().map_err(FrameError::Io))
        {
            output_error = Some(error.to_string());
            cancel.store(true, Ordering::Release);
        }
    };
    let result = if safety::check_scope_policy(&request.root, &resolved).is_err() {
        // Protected replay scopes are pruned without opening or probing their
        // contents. This mirrors the in-process engine's complete skip.
        Ok(ScanStats {
            skipped: 1,
            complete: true,
            message: "Excluded scope reconciled without filesystem access.".into(),
            ..Default::default()
        })
    } else if let Err(reason) = prepare_scan_process() {
        // Emit Failed after Resolved so the coordinator atomically retains the
        // claimed scope for Resume, without publishing a partially scanned tree.
        Err(reason)
    } else if cargo_lock {
        scanner::scan_cargo_lock_with_checkpoint_mode(
            &request.root,
            &resolved,
            &request.kept,
            &cancel,
            mode,
            || {},
            &mut publish,
        )
    } else {
        scanner::scan_with_options(
            &request.root,
            scope,
            &request.kept,
            &cancel,
            scanner::ScanOptions {
                mode,
                recent_files: recent_files.as_mut(),
            },
            || {},
            &mut publish,
        )
    };
    if let Some(error) = output_error {
        return Err(FrameError::Io(io::Error::other(error)));
    }
    match result {
        Ok(stats) => {
            let recent_files = if !cargo_lock && !request.metadata_coverage {
                recent_files
            } else {
                None
            };
            write_json_frame(
                output,
                &ScanEvent::Finished {
                    stats,
                    recent_files,
                },
            )?;
            output.flush()?;
            Ok(())
        }
        Err(error) => {
            write_json_frame(output, &ScanEvent::Failed(error.clone()))?;
            output.flush()?;
            Ok(())
        }
    }
}

/// Entry point used by the bundled helper binary.  It accepts exactly one
/// request and emits an ordered event stream.  Expected scan failures are
/// represented by `Failed`; malformed input or transport failures return an
/// error so the coordinator can treat the process as failed, never complete.
pub fn run_stdio() -> Result<(), Box<dyn std::error::Error>> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut input = BufReader::new(stdin.lock());
    let mut output = BufWriter::new(stdout.lock());
    let request = match read_json_frame::<_, ScanRequest>(&mut input) {
        Ok(Some(request)) => request,
        Ok(None) => return Err("scan-helper received no request".into()),
        Err(error) => return Err(Box::new(error)),
    };
    run_request(request, &mut output)?;
    output.flush()?;
    Ok(())
}

/// Fixed metadata-only mode used by the separately confirmed editor review.
/// This process receives no database, cleanup callback, arbitrary scope, or
/// executable. Its caller enforces the same bounded probe deadline and output
/// cap as installed-tool reviews, inside the write/network-denying sandbox.
pub fn run_editor_review(editor: &str) -> Result<(), Box<dyn std::error::Error>> {
    let editor = match editor {
        "vscode" => crate::editor_review::Editor::Vscode,
        "cursor" => crate::editor_review::Editor::Cursor,
        _ => return Err("Unknown editor review".into()),
    };
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .filter(|home| home.is_absolute())
        .ok_or("Editor review HOME is unavailable")?;
    let review = crate::editor_review::inspect(&home, editor, &AtomicBool::new(false))?;
    let output = serde_json::to_vec(&review)?;
    if output.len() > 64 * 1024 {
        return Err("Editor review exceeded its output bound".into());
    }
    io::stdout().lock().write_all(&output)?;
    Ok(())
}

pub(crate) const ACTIVE_SCANS: usize = 2;
const QUEUED_SCANS: usize = 2;
const SCAN_INACTIVITY: Duration = Duration::from_secs(120);
const IO_POLL: Duration = Duration::from_millis(10);
const IO_CHUNK: usize = 16 * 1024;

/// Resolve only the helper shipped beside the executable. Tests use a private
/// injected fixture instead of altering production discovery.
#[cfg(not(test))]
pub(crate) fn bundled_helper() -> Option<PathBuf> {
    resolve_helper_for(&std::env::current_exe().ok()?)
}

fn resolve_helper_for(executable: &Path) -> Option<PathBuf> {
    let executable = std::fs::canonicalize(executable).ok()?;
    let parent = executable.parent()?;
    // App bundles have a fixed Contents/MacOS executable layout. Do not
    // accept a generic `../Helpers` path: it could escape the actual bundle.
    let helper_dir = if parent.file_name().and_then(|name| name.to_str()) == Some("MacOS")
        && parent
            .parent()
            .and_then(Path::file_name)
            .and_then(|name| name.to_str())
            == Some("Contents")
    {
        let contents = parent.parent()?;
        let bundle = contents.parent()?;
        if bundle.extension().and_then(|name| name.to_str()) != Some("app")
            || !trusted_context(bundle)
            || !trusted_context(contents)
            || !trusted_context(parent)
        {
            return None;
        }
        contents.join("Helpers")
    } else {
        // Command-line distributions ship the helper beside the CLI.
        parent.to_owned()
    };
    let helper = helper_dir.join("chippytea-scan-helper");
    trusted_context(&helper_dir)
        .then(|| trusted_file(&helper))
        .flatten()
}

fn trusted_context(path: &Path) -> bool {
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::fs::PermissionsExt;
    let Ok(metadata) = std::fs::symlink_metadata(path) else {
        return false;
    };
    let Ok(canonical) = std::fs::canonicalize(path) else {
        return false;
    };
    metadata.file_type().is_dir()
        && canonical == path
        && trusted_owner(metadata.uid(), unsafe { libc::geteuid() })
        && metadata.permissions().mode() & 0o022 == 0
}

fn trusted_owner(uid: u32, euid: u32) -> bool {
    uid == 0 || uid == euid
}

fn trusted_file(path: &Path) -> Option<PathBuf> {
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::fs::PermissionsExt;
    let metadata = std::fs::symlink_metadata(path).ok()?;
    (metadata.file_type().is_file()
        && metadata.permissions().mode() & 0o111 != 0
        && metadata.permissions().mode() & (0o022 | 0o6000) == 0
        && trusted_owner(metadata.uid(), unsafe { libc::geteuid() }))
    .then(|| std::fs::canonicalize(path).ok())
    .flatten()
}

fn helper_allowed(path: &Path) -> bool {
    if !path.is_absolute() {
        return false;
    }
    #[cfg(test)]
    {
        true
    }
    #[cfg(not(test))]
    {
        bundled_helper().is_some_and(|bundled| bundled == path)
    }
}

struct Job {
    helper: PathBuf,
    request_frame: Vec<u8>,
    mailbox: Arc<Mailbox>,
    aborted: Arc<AtomicBool>,
    started: Arc<AtomicBool>,
    inactivity: Duration,
}

struct Pool {
    jobs: std::sync::mpsc::SyncSender<Job>,
}

impl Pool {
    fn new() -> Self {
        let (jobs, receiver) = std::sync::mpsc::sync_channel::<Job>(QUEUED_SCANS);
        let receiver = Arc::new(Mutex::new(receiver));
        for index in 0..ACTIVE_SCANS {
            let receiver = Arc::clone(&receiver);
            let _ = thread::Builder::new()
                .name(format!("chippytea-scan-helper-{index}"))
                .spawn(move || {
                    loop {
                        let job = receiver.lock().unwrap().recv();
                        match job {
                            Ok(job) => {
                                job.started.store(true, Ordering::Release);
                                supervise(job);
                            }
                            Err(_) => break,
                        }
                    }
                });
        }
        Self { jobs }
    }
}

struct MailboxState {
    events: VecDeque<(ScanEvent, usize)>,
    bytes: usize,
    closed: bool,
    failure: Option<String>,
}

struct Mailbox {
    state: Mutex<MailboxState>,
    changed: Condvar,
}

impl Mailbox {
    fn new() -> Self {
        Self {
            state: Mutex::new(MailboxState {
                events: VecDeque::new(),
                bytes: 0,
                closed: false,
                failure: None,
            }),
            changed: Condvar::new(),
        }
    }

    fn push(&self, event: ScanEvent, bytes: usize, terminal: bool, aborted: &AtomicBool) -> bool {
        let mut state = self.state.lock().unwrap();
        loop {
            if state.closed || aborted.load(Ordering::Acquire) {
                return false;
            }
            // Keep one of the two slots and one frame's worth of bytes free
            // for a terminal event. Ordinary events therefore backpressure
            // the child rather than being discarded.
            let count_limit = if terminal {
                MAX_QUEUED_EVENT_FRAMES
            } else {
                MAX_QUEUED_EVENT_FRAMES - 1
            };
            let byte_limit = if terminal {
                MAX_QUEUED_EVENT_BYTES
            } else {
                MAX_QUEUED_EVENT_BYTES - MAX_FRAME_BYTES
            };
            if state.events.len() < count_limit && bytes <= byte_limit.saturating_sub(state.bytes) {
                state.bytes += bytes;
                state.events.push_back((event, bytes));
                self.changed.notify_all();
                return true;
            }
            state = self.changed.wait(state).unwrap();
        }
    }

    fn try_recv(&self) -> Result<Option<ScanEvent>, String> {
        let mut state = self.state.lock().unwrap();
        if let Some(error) = &state.failure {
            return Err(error.clone());
        }
        let Some((event, bytes)) = state.events.pop_front() else {
            return Ok(None);
        };
        state.bytes = state.bytes.saturating_sub(bytes);
        self.changed.notify_all();
        Ok(Some(event))
    }

    fn fail(&self, error: impl Into<String>) {
        let mut state = self.state.lock().unwrap();
        state.events.clear();
        state.bytes = 0;
        state.failure = Some(error.into());
        state.closed = true;
        self.changed.notify_all();
    }

    fn close(&self) {
        let mut state = self.state.lock().unwrap();
        state.closed = true;
        self.changed.notify_all();
    }

    fn wake(&self) {
        // Pair notification with the same mutex as the abort predicate check
        // and wait, so abort cannot be lost just before a full mailbox parks.
        let _state = self.state.lock().unwrap();
        self.changed.notify_all();
    }
}

pub(crate) struct Handle {
    mailbox: Arc<Mailbox>,
    aborted: Arc<AtomicBool>,
    started: Arc<AtomicBool>,
    queued_at: Instant,
    inactivity: Duration,
}

impl Handle {
    pub(crate) fn try_recv(&self) -> Result<Option<ScanEvent>, String> {
        if !self.started.load(Ordering::Acquire) && self.queued_at.elapsed() >= self.inactivity {
            self.abort();
            return Err("scan-helper remained queued beyond its deadline".into());
        }
        self.mailbox.try_recv()
    }

    pub(crate) fn abort(&self) {
        self.aborted.store(true, Ordering::Release);
        self.mailbox.wake();
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        self.abort();
    }
}

pub(crate) fn start(helper: &Path, request: ScanRequest) -> Result<Handle, String> {
    if !helper_allowed(helper) {
        return Err("scan-helper executable is not a trusted absolute path".into());
    }
    let request_frame = encode_json_frame(&request).map_err(|error| error.to_string())?;
    enqueue(static_pool(), helper, request_frame)
}

fn enqueue(pool: &Pool, helper: &Path, request_frame: Vec<u8>) -> Result<Handle, String> {
    enqueue_with_deadline(pool, helper, request_frame, SCAN_INACTIVITY)
}

fn enqueue_with_deadline(
    pool: &Pool,
    helper: &Path,
    request_frame: Vec<u8>,
    inactivity: Duration,
) -> Result<Handle, String> {
    let mailbox = Arc::new(Mailbox::new());
    let aborted = Arc::new(AtomicBool::new(false));
    let started = Arc::new(AtomicBool::new(false));
    let handle = Handle {
        mailbox: Arc::clone(&mailbox),
        aborted: Arc::clone(&aborted),
        started: Arc::clone(&started),
        queued_at: Instant::now(),
        inactivity,
    };
    match pool.jobs.try_send(Job {
        helper: helper.to_path_buf(),
        request_frame,
        mailbox,
        aborted,
        started,
        inactivity,
    }) {
        Ok(()) => Ok(handle),
        Err(std::sync::mpsc::TrySendError::Full(_)) => {
            handle.abort();
            Err("scan-helper capacity is busy; try again later".into())
        }
        Err(std::sync::mpsc::TrySendError::Disconnected(_)) => {
            handle.abort();
            Err("scan-helper supervisors are unavailable".into())
        }
    }
}

fn static_pool() -> &'static Pool {
    static POOL: OnceLock<Pool> = OnceLock::new();
    POOL.get_or_init(Pool::new)
}

fn set_nonblocking(fd: RawFd) -> io::Result<()> {
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn configure_request_pipe(fd: RawFd) -> io::Result<()> {
    set_nonblocking(fd)?;
    #[cfg(target_os = "macos")]
    {
        // Rust's executable startup ignores SIGPIPE, but the Swift host does
        // not run that startup for this static library. A helper that closes
        // stdin must yield EPIPE, not terminate the app. Use Darwin's per-fd
        // setting without changing the host's process-wide signal policy.
        // F_SETNOSIGPIPE is defined in the macOS SDK's sys/fcntl.h but not in
        // libc's Darwin module.
        const F_SETNOSIGPIPE: libc::c_int = 73;
        if unsafe { libc::fcntl(fd, F_SETNOSIGPIPE, 1) } < 0 {
            return Err(io::Error::last_os_error());
        }
    }
    Ok(())
}

fn supervise(job: Job) {
    if job.aborted.load(Ordering::Acquire) {
        job.mailbox.fail("scan-helper aborted before launch");
        return;
    }
    let mut command = Command::new(&job.helper);
    command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0);
    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            job.mailbox
                .fail(format!("scan-helper could not start: {error}"));
            return;
        }
    };
    let write_result = child
        .stdin
        .take()
        .ok_or_else(|| io::Error::other("scan-helper stdin unavailable"))
        .and_then(|mut input| {
            configure_request_pipe(input.as_raw_fd())?;
            write_request(&mut input, &job.request_frame, &job.aborted, job.inactivity)
        });
    if let Err(error) = write_result {
        job.mailbox
            .fail(format!("scan-helper request failed: {error}"));
        terminate_unreaped(&mut child);
        return;
    }
    if let Err(error) = child
        .stdout
        .as_ref()
        .ok_or_else(|| io::Error::other("scan-helper stdout unavailable"))
        .and_then(|pipe| set_nonblocking(pipe.as_raw_fd()))
        .and_then(|_| {
            child
                .stderr
                .as_ref()
                .ok_or_else(|| io::Error::other("scan-helper stderr unavailable"))
                .and_then(|pipe| set_nonblocking(pipe.as_raw_fd()))
        })
    {
        job.mailbox
            .fail(format!("scan-helper pipe setup failed: {error}"));
        terminate_unreaped(&mut child);
        return;
    }
    match drive_child(&mut child, &job) {
        Ok(decoder) => {
            // EOF and successful exit have been observed without reaping the
            // leader. End its process group while that PID is still reserved,
            // then reap before admitting a replacement or publishing Finished.
            terminate_unreaped(&mut child);
            match decoder.finish(&job.mailbox, &job.aborted) {
                Ok(()) => job.mailbox.close(),
                Err(error) => job.mailbox.fail(error),
            }
        }
        Err(error) => {
            job.mailbox.fail(error);
            terminate_unreaped(&mut child);
        }
    }
}

fn write_request(
    input: &mut impl Write,
    request: &[u8],
    aborted: &AtomicBool,
    inactivity: Duration,
) -> io::Result<()> {
    let mut written = 0;
    let started = Instant::now();
    while written < request.len() {
        if aborted.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "scan-helper request aborted",
            ));
        }
        match input.write(&request[written..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "scan-helper stdin closed",
                ));
            }
            Ok(count) => {
                written += count;
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if started.elapsed() >= inactivity {
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        "scan-helper request stalled",
                    ));
                }
                thread::sleep(IO_POLL);
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

fn terminate_unreaped(child: &mut Child) {
    // No earlier call is allowed to reap this child. In particular an exited
    // leader can still have descendants holding pipes or doing read probes.
    unsafe {
        libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL);
    }
    let _ = child.kill();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Err(error) if error.raw_os_error() == Some(libc::ECHILD) => break,
            // A kernel-stuck child keeps this fixed supervisor slot. Neither
            // cancellation nor a status error creates replacement workers.
            Ok(None) | Err(_) => thread::sleep(IO_POLL),
        }
    }
}

fn successful_exit_without_reaping(child: &Child) -> Result<Option<bool>, String> {
    // waitid(WNOWAIT) preserves the process identity until its group is ended.
    // Zero initialization also covers Darwin's no-event WNOHANG behavior.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            child.id() as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if result != 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::Interrupted {
            return Ok(None);
        }
        return Err(format!("scan-helper status unavailable: {error}"));
    }
    if unsafe { info.si_pid() } == 0 {
        Ok(None)
    } else {
        Ok(Some(
            info.si_code == libc::CLD_EXITED && unsafe { info.si_status() } == 0,
        ))
    }
}

struct FrameDecoder {
    bytes: Vec<u8>,
    resolved: bool,
    terminal: Option<(ScanEvent, usize)>,
}

impl FrameDecoder {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            resolved: false,
            terminal: None,
        }
    }

    fn feed(
        &mut self,
        incoming: &[u8],
        mailbox: &Mailbox,
        aborted: &AtomicBool,
    ) -> Result<(), String> {
        self.bytes.extend_from_slice(incoming);
        loop {
            if self.bytes.len() < 4 {
                if self.bytes.len() > MAX_FRAME_BYTES + 4 {
                    return Err("scan-helper frame stream exceeded its bounded parser".into());
                }
                return Ok(());
            }
            let length = u32::from_be_bytes(self.bytes[..4].try_into().unwrap()) as usize;
            if length == 0 || length > MAX_FRAME_BYTES {
                return Err("scan-helper emitted an invalid frame length".into());
            }
            if self.bytes.len() < length + 4 {
                if self.bytes.len() > MAX_FRAME_BYTES + 4 {
                    return Err("scan-helper frame stream exceeded its bounded parser".into());
                }
                return Ok(());
            }
            let body = self.bytes[4..length + 4].to_vec();
            self.bytes.drain(..length + 4);
            let event: ScanEvent = serde_json::from_slice(&body)
                .map_err(|error| format!("scan-helper emitted malformed JSON: {error}"))?;
            match event {
                ScanEvent::Resolved { .. } if self.resolved || self.terminal.is_some() => {
                    return Err("scan-helper emitted duplicate or late Resolved".into());
                }
                ScanEvent::Resolved { path, cargo_lock } => {
                    self.resolved = true;
                    if !mailbox.push(
                        ScanEvent::Resolved { path, cargo_lock },
                        body.len(),
                        false,
                        aborted,
                    ) {
                        return Err("scan-helper event delivery was aborted".into());
                    }
                }
                ScanEvent::Batch(_batch) if !self.resolved || self.terminal.is_some() => {
                    return Err("scan-helper emitted Batch before/after its scope".into());
                }
                ScanEvent::Batch(batch) => {
                    if !mailbox.push(ScanEvent::Batch(batch), body.len(), false, aborted) {
                        return Err("scan-helper event delivery was aborted".into());
                    }
                }
                ScanEvent::Finished {
                    stats: _,
                    recent_files: _,
                } if !self.resolved || self.terminal.is_some() => {
                    return Err("scan-helper emitted invalid duplicate Finished".into());
                }
                ScanEvent::Finished {
                    stats,
                    recent_files,
                } => {
                    self.terminal = Some((
                        ScanEvent::Finished {
                            stats,
                            recent_files,
                        },
                        body.len(),
                    ));
                }
                ScanEvent::Failed(_error) if !self.resolved || self.terminal.is_some() => {
                    return Err("scan-helper emitted invalid duplicate Failed".into());
                }
                ScanEvent::Failed(error) => {
                    self.terminal = Some((ScanEvent::Failed(error), body.len()));
                }
            }
        }
    }

    fn finish(self, mailbox: &Mailbox, aborted: &AtomicBool) -> Result<(), String> {
        if !self.bytes.is_empty() {
            return Err("scan-helper stdout ended with a truncated frame".into());
        }
        if !self.resolved {
            return Err("scan-helper ended without Resolved".into());
        }
        let Some((event, bytes)) = self.terminal else {
            return Err("scan-helper ended without a terminal event".into());
        };
        if !mailbox.push(event, bytes, true, aborted) {
            return Err("scan-helper terminal delivery was aborted".into());
        }
        Ok(())
    }
}

fn drive_child(child: &mut Child, job: &Job) -> Result<FrameDecoder, String> {
    let mut stdout_done = false;
    let mut stderr_done = false;
    let mut stdout_buffer = [0u8; IO_CHUNK];
    let mut stderr_buffer = [0u8; IO_CHUNK];
    let mut stderr = Vec::with_capacity(MAX_DIAGNOSTIC_BYTES);
    let mut decoder = FrameDecoder::new();
    let mut activity = Instant::now();
    loop {
        if job.aborted.load(Ordering::Acquire) {
            return Err("scan-helper aborted".into());
        }
        if activity.elapsed() >= job.inactivity {
            return Err("scan-helper stalled without progress".into());
        }
        let mut progressed = false;
        if !stdout_done {
            // Drain in a separate small loop so parser memory never includes
            // more than one bounded frame. The helper's pipe remains back-
            // pressured when the mailbox is full.
            for _ in 0..16 {
                if job.aborted.load(Ordering::Acquire) {
                    return Err("scan-helper aborted".into());
                }
                match child.stdout.as_mut().unwrap().read(&mut stdout_buffer) {
                    Ok(0) => {
                        stdout_done = true;
                        break;
                    }
                    Ok(count) => {
                        progressed = true;
                        activity = Instant::now();
                        decoder.feed(&stdout_buffer[..count], &job.mailbox, &job.aborted)?;
                        if count < stdout_buffer.len() {
                            break;
                        }
                    }
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(format!("scan-helper stdout read failed: {error}")),
                }
            }
        }
        if !stderr_done {
            // One bounded read per round. A chatty diagnostic stream cannot
            // starve stdout, cancellation, or the inactivity check.
            match child.stderr.as_mut().unwrap().read(&mut stderr_buffer) {
                Ok(0) => stderr_done = true,
                Ok(count) => {
                    progressed = true;
                    if count > MAX_DIAGNOSTIC_BYTES.saturating_sub(stderr.len()) {
                        return Err("scan-helper exceeded its diagnostic output limit".into());
                    }
                    stderr.extend_from_slice(&stderr_buffer[..count]);
                    // Only protocol output is traversal progress. Empty stderr
                    // polls and repetitive diagnostics never extend a stall.
                }
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                Err(error) => return Err(format!("scan-helper stderr read failed: {error}")),
            }
        }
        if stdout_done
            && stderr_done
            && let Some(success) = successful_exit_without_reaping(child)?
        {
            if !success {
                return Err("scan-helper exited unsuccessfully".into());
            }
            return Ok(decoder);
        }
        if !progressed {
            thread::sleep(IO_POLL);
        }
    }
}

/// Keep helper diagnostics bounded even when a caller displays stderr.  The
/// transport itself carries structured failures; this is only a short aid for
/// launch/protocol failures.
pub fn bounded_diagnostic(message: &str) -> String {
    let mut end = message.len().min(MAX_DIAGNOSTIC_BYTES);
    while end > 0 && !message.is_char_boundary(end) {
        end -= 1;
    }
    message[..end].to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn frame_reader_handles_partial_prefix_and_body() {
        let body = br#"{"ok":true}"#;
        let mut bytes = (body.len() as u32).to_be_bytes().to_vec();
        bytes.extend_from_slice(body);
        let mut reader = Cursor::new(bytes);
        assert_eq!(read_frame(&mut reader).unwrap().unwrap(), body);
    }

    #[test]
    fn frame_reader_rejects_oversized_before_body_allocation() {
        let length = (MAX_FRAME_BYTES as u32 + 1).to_be_bytes();
        let mut reader = Cursor::new(length);
        assert!(matches!(
            read_frame(&mut reader),
            Err(FrameError::TooLarge { .. })
        ));
    }

    #[test]
    fn frame_reader_rejects_truncated_and_malformed_json() {
        let mut truncated = Cursor::new(
            (4u32)
                .to_be_bytes()
                .into_iter()
                .chain(*b"{")
                .collect::<Vec<_>>(),
        );
        assert!(matches!(
            read_frame(&mut truncated),
            Err(FrameError::Truncated { .. })
        ));
        let body = b"not-json";
        let mut bytes = (body.len() as u32).to_be_bytes().to_vec();
        bytes.extend_from_slice(body);
        let mut malformed = Cursor::new(bytes);
        assert!(matches!(
            read_json_frame::<_, serde_json::Value>(&mut malformed),
            Err(FrameError::InvalidJson(_))
        ));
    }

    #[test]
    fn diagnostic_is_byte_bounded_without_cutting_utf8() {
        let input = "é".repeat(MAX_DIAGNOSTIC_BYTES);
        let output = bounded_diagnostic(&input);
        assert!(output.len() <= MAX_DIAGNOSTIC_BYTES);
        assert!(std::str::from_utf8(output.as_bytes()).is_ok());
    }

    fn request() -> ScanRequest {
        use crate::model::Identity;
        ScanRequest {
            root: Root {
                id: "fixture".into(),
                path: "/tmp".into(),
                kind: "folder".into(),
                identity: Identity {
                    device: 1,
                    inode: 1,
                    mode: 0,
                    size: 0,
                    modified_ns: 0,
                    changed_ns: 0,
                },
            },
            requested: "/tmp/fixture".into(),
            indexed: None,
            enclosing_parent: None,
            kept: Vec::new(),
            metadata_coverage: false,
            recent_files: None,
        }
    }

    fn fixture_script(
        directory: &Path,
        name: &str,
        output: &[u8],
        exit: i32,
        delay: &str,
    ) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = directory.join(name);
        let escaped = output
            .iter()
            .map(|byte| format!("\\{:03o}", byte))
            .collect::<String>();
        std::fs::write(
            &path,
            format!("#!/bin/sh\ncat >/dev/null\nprintf '{escaped}'\n{delay}\nexit {exit}\n"),
        )
        .unwrap();
        let mut permissions = std::fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&path, permissions).unwrap();
        path
    }

    fn valid_output() -> Vec<u8> {
        let resolved = encode_json_frame(&ScanEvent::Resolved {
            path: "/tmp/fixture".into(),
            cargo_lock: false,
        })
        .unwrap();
        let finished = encode_json_frame(&ScanEvent::Finished {
            stats: ScanStats {
                complete: true,
                ..Default::default()
            },
            recent_files: None,
        })
        .unwrap();
        let mut output = resolved;
        output.extend_from_slice(&finished);
        output
    }

    fn wait_until_error(handle: &Handle) -> String {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match handle.try_recv() {
                Err(error) => return error,
                Ok(Some(_)) => {}
                Ok(None) => {}
            }
            assert!(Instant::now() < deadline, "fixture did not terminate");
            thread::sleep(IO_POLL);
        }
    }

    #[test]
    fn finished_waits_for_clean_eof_and_successful_status() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(
            directory.path(),
            "clean-helper",
            &valid_output(),
            0,
            "sleep 0.15",
        );
        let pool = Pool::new();
        let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let deadline = Instant::now() + Duration::from_secs(2);
        let mut events = Vec::new();
        while events.len() < 2 {
            if let Some(event) = handle.try_recv().unwrap() {
                events.push(event);
            }
            assert!(Instant::now() < deadline);
            thread::sleep(IO_POLL);
        }
        assert!(matches!(events[0], ScanEvent::Resolved { .. }));
        assert!(matches!(events[1], ScanEvent::Finished { .. }));
    }

    #[test]
    fn failed_status_never_publishes_finished() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(directory.path(), "status-helper", &valid_output(), 7, "");
        let pool = Pool::new();
        let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let error = wait_until_error(&handle);
        assert!(error.contains("exited"), "{error}");
    }

    #[test]
    fn malformed_truncated_and_oversized_output_fail_closed() {
        let directory = tempfile::tempdir().unwrap();
        let cases = [
            ("malformed", vec![0, 0, 0, 3, b'n', b'o', b'p'], "malformed"),
            ("truncated", vec![0, 0, 0, 4, b'{'], "truncated"),
            (
                "oversized",
                (MAX_FRAME_BYTES as u32 + 1).to_be_bytes().to_vec(),
                "invalid frame length",
            ),
        ];
        for (name, output, expected) in cases {
            let helper = fixture_script(directory.path(), name, &output, 0, "");
            let pool = Pool::new();
            let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
            let error = wait_until_error(&handle);
            assert!(error.contains(expected), "{error}");
        }
    }

    #[test]
    fn abort_stalled_helper_without_waiting_for_child() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(directory.path(), "stalled-helper", &[], 0, "sleep 5");
        let pool = Pool::new();
        let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        thread::sleep(Duration::from_millis(30));
        let started = Instant::now();
        handle.abort();
        let error = wait_until_error(&handle);
        assert!(error.contains("aborted"), "{error}");
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn silent_open_stderr_does_not_extend_the_inactivity_deadline() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(directory.path(), "silent-helper", &[], 0, "sleep 10");
        let pool = Pool::new();
        let handle = enqueue_with_deadline(
            &pool,
            &helper,
            encode_json_frame(&request()).unwrap(),
            Duration::from_millis(80),
        )
        .unwrap();
        let started = Instant::now();
        let error = wait_until_error(&handle);
        assert!(
            error.contains("stalled") || error.contains("queued"),
            "{error}"
        );
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn unbounded_stderr_is_rejected_without_starving_cancellation() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(
            directory.path(),
            "noisy-helper",
            &[],
            0,
            "while :; do printf 'bounded-diagnostic-fixture\\n' >&2; done",
        );
        let pool = Pool::new();
        let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        assert!(wait_until_error(&handle).contains("diagnostic output limit"));
    }

    #[test]
    fn cancellation_ends_descendants_after_the_leader_has_exited() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(
            directory.path(),
            "descendant-helper",
            &[],
            0,
            "sleep 10 &\nprintf '%s' \"$!\" > \"$0.descendant\"",
        );
        let pool = Pool::new();
        let handle = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let pid_file = helper.with_file_name("descendant-helper.descendant");
        let deadline = Instant::now() + Duration::from_secs(2);
        let pid: libc::pid_t = loop {
            if let Ok(text) = std::fs::read_to_string(&pid_file)
                && let Ok(pid) = text.parse()
            {
                break pid;
            }
            assert!(Instant::now() < deadline);
            thread::sleep(IO_POLL);
        };
        // Give the shell time to exit with its pipe inherited by the sleeper.
        thread::sleep(Duration::from_millis(40));
        handle.abort();
        assert!(wait_until_error(&handle).contains("aborted"));
        while unsafe { libc::kill(pid, 0) } == 0 {
            assert!(
                Instant::now() < deadline,
                "fixture descendant survived cancellation"
            );
            thread::sleep(IO_POLL);
        }
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    }

    #[test]
    fn admission_is_two_active_plus_two_queued() {
        let directory = tempfile::tempdir().unwrap();
        let helper = fixture_script(directory.path(), "capacity-helper", &[], 0, "sleep 5");
        let pool = Pool::new();
        let first = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let second = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let deadline = Instant::now() + Duration::from_secs(1);
        while !first.started.load(Ordering::Acquire) || !second.started.load(Ordering::Acquire) {
            assert!(Instant::now() < deadline);
            thread::sleep(IO_POLL);
        }
        let third = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let fourth = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap()).unwrap();
        let fifth = enqueue(&pool, &helper, encode_json_frame(&request()).unwrap());
        assert!(fifth.is_err());
        first.abort();
        second.abort();
        third.abort();
        fourth.abort();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn broken_request_pipe_returns_error_with_default_sigpipe() {
        use std::os::fd::FromRawFd;
        use std::os::unix::process::ExitStatusExt;

        const CHILD_MODE: &str = "CHIPPYTEA_TEST_REQUEST_PIPE_SIGPIPE";
        if let Ok(mode) = std::env::var(CHILD_MODE) {
            assert!(mode == "protected" || mode == "unprotected");
            // Only this isolated test subprocess changes its signal policy.
            // The parallel parent test runner and the real host are untouched.
            assert_ne!(
                unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) },
                libc::SIG_ERR
            );
            let mut pipe = [-1; 2];
            assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
            let reader = unsafe { std::fs::File::from_raw_fd(pipe[0]) };
            let mut writer = unsafe { std::fs::File::from_raw_fd(pipe[1]) };
            if mode == "protected" {
                configure_request_pipe(writer.as_raw_fd()).unwrap();
            } else {
                set_nonblocking(writer.as_raw_fd()).unwrap();
            }
            drop(reader);
            let error = write_request(
                &mut writer,
                b"request",
                &AtomicBool::new(false),
                Duration::from_secs(1),
            )
            .unwrap_err();
            assert_eq!(mode, "protected", "the negative control did not signal");
            assert_eq!(error.raw_os_error(), Some(libc::EPIPE));
            return;
        }

        for mode in ["unprotected", "protected"] {
            let output = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "scan_worker::tests::broken_request_pipe_returns_error_with_default_sigpipe",
                    "--nocapture",
                ])
                .env(CHILD_MODE, mode)
                .output()
                .unwrap();
            if mode == "unprotected" {
                assert_eq!(output.status.signal(), Some(libc::SIGPIPE));
            } else {
                assert!(
                    output.status.success(),
                    "protected subprocess failed: {}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        }
    }

    #[test]
    fn helper_resolver_requires_owned_nonwritable_file_and_context() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        std::fs::set_permissions(directory.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let executable = directory.path().join("chippytea-cli");
        let helper = directory.path().join("chippytea-scan-helper");
        std::fs::write(&executable, b"cli").unwrap();
        std::fs::write(&helper, b"helper").unwrap();
        for path in [&executable, &helper] {
            let mut permissions = std::fs::metadata(path).unwrap().permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(path, permissions).unwrap();
        }
        assert_eq!(
            resolve_helper_for(&executable),
            Some(std::fs::canonicalize(&helper).unwrap())
        );

        for mode in [0o720, 0o702, 0o4700, 0o2700] {
            let mut permissions = std::fs::metadata(&helper).unwrap().permissions();
            permissions.set_mode(mode);
            std::fs::set_permissions(&helper, permissions).unwrap();
            assert!(resolve_helper_for(&executable).is_none());
        }
        let mut permissions = std::fs::metadata(&helper).unwrap().permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&helper, permissions).unwrap();

        let redirected = directory.path().join("redirect-target");
        std::fs::write(&redirected, b"redirected").unwrap();
        let redirected_helper = directory.path().join("redirected-helper");
        std::os::unix::fs::symlink(&redirected, &redirected_helper).unwrap();
        assert!(trusted_file(&redirected_helper).is_none());

        let mut context_permissions = std::fs::metadata(directory.path()).unwrap().permissions();
        context_permissions.set_mode(0o770);
        std::fs::set_permissions(directory.path(), context_permissions).unwrap();
        assert!(resolve_helper_for(&executable).is_none());
    }

    #[test]
    fn helper_resolver_accepts_only_actual_app_contents_helpers_context() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let bundle = directory.path().join("Chippytea.app");
        let macos = bundle.join("Contents/MacOS");
        let helpers = bundle.join("Contents/Helpers");
        std::fs::create_dir_all(&macos).unwrap();
        std::fs::create_dir_all(&helpers).unwrap();
        for context in [
            directory.path(),
            &bundle,
            &bundle.join("Contents"),
            &macos,
            &helpers,
        ] {
            std::fs::set_permissions(context, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let executable = macos.join("Chippytea");
        let helper = helpers.join("chippytea-scan-helper");
        std::fs::write(&executable, b"app").unwrap();
        std::fs::write(&helper, b"helper").unwrap();
        for path in [&executable, &helper] {
            let mut permissions = std::fs::metadata(path).unwrap().permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(path, permissions).unwrap();
        }
        assert_eq!(
            resolve_helper_for(&executable),
            Some(std::fs::canonicalize(&helper).unwrap())
        );

        // A safe leaf is insufficient when another account can replace an
        // ancestor inside the application bundle.
        for context in [&bundle, &bundle.join("Contents"), &macos, &helpers] {
            let original = std::fs::metadata(context).unwrap().permissions();
            let mut writable = original.clone();
            writable.set_mode(0o770);
            std::fs::set_permissions(context, writable).unwrap();
            assert!(resolve_helper_for(&executable).is_none());
            std::fs::set_permissions(context, original).unwrap();
        }

        let redirected_helpers = bundle.join("redirected-helpers");
        std::fs::rename(&helpers, &redirected_helpers).unwrap();
        std::os::unix::fs::symlink(&redirected_helpers, &helpers).unwrap();
        assert!(resolve_helper_for(&executable).is_none());
        std::fs::remove_file(&helpers).unwrap();
        std::fs::rename(&redirected_helpers, &helpers).unwrap();

        let malformed_bundle = directory.path().join("NotABundle");
        let malformed_macos = malformed_bundle.join("Contents/MacOS");
        let malformed_helpers = malformed_bundle.join("Contents/Helpers");
        std::fs::create_dir_all(&malformed_macos).unwrap();
        std::fs::create_dir_all(&malformed_helpers).unwrap();
        let malformed_executable = malformed_macos.join("Chippytea");
        let malformed_helper = malformed_helpers.join("chippytea-scan-helper");
        std::fs::write(&malformed_executable, b"app").unwrap();
        std::fs::write(&malformed_helper, b"helper").unwrap();
        for path in [&malformed_executable, &malformed_helper] {
            let mut permissions = std::fs::metadata(path).unwrap().permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(path, permissions).unwrap();
        }
        assert!(resolve_helper_for(&malformed_executable).is_none());

        let wrong_context = bundle.join("Helpers");
        std::fs::create_dir_all(&wrong_context).unwrap();
        let wrong_helper = wrong_context.join("chippytea-scan-helper");
        std::fs::write(&wrong_helper, b"wrong").unwrap();
        let mut permissions = std::fs::metadata(&wrong_helper).unwrap().permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&wrong_helper, permissions).unwrap();
        // The app resolver never falls back to bundle/Helpers.
        std::fs::remove_file(&helper).unwrap();
        assert!(resolve_helper_for(&executable).is_none());
    }

    #[test]
    fn helper_owner_predicate_rejects_another_uid() {
        let euid = unsafe { libc::geteuid() };
        let other = if euid == u32::MAX { euid - 1 } else { euid + 1 };
        assert!(!trusted_owner(other, euid));
        assert!(trusted_owner(0, euid));
        assert!(trusted_owner(euid, euid));
    }
}
