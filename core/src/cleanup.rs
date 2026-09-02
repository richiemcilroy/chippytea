use crate::{
    accounting,
    model::*,
    safety, scanner,
    store::{Store, err},
};
use rusqlite::{CachedStatement, Statement, params};
use std::{
    collections::HashMap,
    ffi::{CStr, CString, OsStr},
    fs::File,
    os::unix::{
        ffi::OsStrExt,
        io::{AsRawFd, FromRawFd, RawFd},
    },
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicBool, Ordering},
    time::{Duration, Instant},
};

pub type TrashCallback =
    unsafe extern "C" fn(*const libc::c_char, *mut libc::c_char, usize) -> libc::c_int;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CleanupPhase {
    Checking,
    Preparing,
    Comparing,
    Removing,
    Accounting,
}

const MANIFEST_INSERT: &str = "INSERT INTO cleanup_entries VALUES(?1,?2,?3)";
const MANIFEST_IDENTITY: &str =
    "SELECT identity FROM cleanup_entries WHERE operation_id=?1 AND path=?2";
const PROGRESS_INTERVAL: Duration = Duration::from_millis(100);

struct Progress<'a> {
    callback: &'a mut dyn FnMut(CleanupPhase, u64, u64),
    phase: CleanupPhase,
    completed: u64,
    total: u64,
    last: Instant,
    reported: Option<(CleanupPhase, u64, u64)>,
}

impl<'a> Progress<'a> {
    fn new(callback: &'a mut dyn FnMut(CleanupPhase, u64, u64)) -> Self {
        Self {
            callback,
            phase: CleanupPhase::Checking,
            completed: 0,
            total: 0,
            last: Instant::now(),
            reported: None,
        }
    }

    fn start(&mut self, phase: CleanupPhase, total: u64) {
        self.phase = phase;
        self.completed = 0;
        self.total = total;
        self.finish();
    }

    fn update(&mut self, completed: u64) {
        self.completed = completed;
        if completed == 1 || self.last.elapsed() >= PROGRESS_INTERVAL {
            self.finish();
        }
    }

    fn advance(&mut self) {
        self.update(self.completed.saturating_add(1));
    }

    fn complete(&mut self) {
        if self.total == 0 {
            self.total = self.completed;
        } else {
            self.completed = self.total;
        }
        self.finish();
    }

    /// Phase boundaries and the final result bypass the intermediate update
    /// throttle, including when an error leaves this phase incomplete.
    fn finish(&mut self) {
        let value = (self.phase, self.completed, self.total);
        if self.reported == Some(value) {
            return;
        }
        (self.callback)(self.phase, self.completed, self.total);
        self.reported = Some(value);
        self.last = Instant::now();
    }
}

fn cancelled(cancel: &AtomicBool) -> Result<()> {
    if cancel.load(Ordering::Relaxed) {
        Err("Cancelled. Completed removals cannot be undone.".into())
    } else {
        Ok(())
    }
}
fn cstr(name: &OsStr) -> Result<CString> {
    CString::new(name.as_bytes()).map_err(err)
}
fn ioerr() -> String {
    std::io::Error::last_os_error().to_string()
}

pub fn open_directory(path: &Path) -> Result<File> {
    if !path.is_absolute() {
        return Err("An absolute authorized path is required.".into());
    }
    let fd = unsafe {
        libc::open(
            c"/".as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(ioerr());
    }
    let mut current = unsafe { File::from_raw_fd(fd) };
    for component in path.components() {
        match component {
            Component::RootDir => {}
            Component::Normal(name) => {
                let name = cstr(name)?;
                #[cfg(target_os = "macos")]
                let access = libc::O_SEARCH;
                #[cfg(not(target_os = "macos"))]
                let access = libc::O_RDONLY | libc::O_DIRECTORY;
                let fd = unsafe {
                    libc::openat(
                        current.as_raw_fd(),
                        name.as_ptr(),
                        access | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                    )
                };
                if fd < 0 {
                    return Err(format!(
                        "Cannot safely open {}: {}",
                        path.display(),
                        ioerr()
                    ));
                }
                current = unsafe { File::from_raw_fd(fd) };
            }
            _ => return Err("Relative traversal is not authorized.".into()),
        }
    }
    Ok(current)
}

fn stat_at(parent: RawFd, name: &CStr) -> Result<libc::stat> {
    let mut stat = std::mem::MaybeUninit::uninit();
    if unsafe {
        libc::fstatat(
            parent,
            name.as_ptr(),
            stat.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(ioerr());
    }
    Ok(unsafe { stat.assume_init() })
}
fn identity_stat(stat: &libc::stat) -> Identity {
    Identity {
        device: stat.st_dev as u64,
        inode: stat.st_ino,
        mode: stat.st_mode as u32,
        size: stat.st_size.max(0) as u64,
        modified_ns: stat
            .st_mtime
            .saturating_mul(1_000_000_000)
            .saturating_add(stat.st_mtime_nsec),
        changed_ns: stat
            .st_ctime
            .saturating_mul(1_000_000_000)
            .saturating_add(stat.st_ctime_nsec),
    }
}
fn same_object(a: &Identity, b: &Identity) -> bool {
    a.device == b.device && a.inode == b.inode && a.mode == b.mode
}

fn each_entry(fd: RawFd, mut visit: impl FnMut(&CStr) -> Result<()>) -> Result<()> {
    let duplicate = unsafe { libc::dup(fd) };
    if duplicate < 0 {
        return Err(ioerr());
    }
    let dir = unsafe { libc::fdopendir(duplicate) };
    if dir.is_null() {
        unsafe { libc::close(duplicate) };
        return Err(ioerr());
    }
    struct Directory(*mut libc::DIR);
    impl Drop for Directory {
        fn drop(&mut self) {
            unsafe { libc::closedir(self.0) };
        }
    }
    let _guard = Directory(dir);
    loop {
        #[cfg(target_os = "macos")]
        unsafe {
            *libc::__error() = 0;
        }
        #[cfg(target_os = "linux")]
        unsafe {
            *libc::__errno_location() = 0;
        }
        let entry = unsafe { libc::readdir(dir) };
        if entry.is_null() {
            let code = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
            return if code == 0 { Ok(()) } else { Err(ioerr()) };
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) };
        if name.to_bytes() == b"." || name.to_bytes() == b".." {
            continue;
        }
        visit(name)?;
    }
}

fn record_manifest_entry(
    statement: &mut Statement<'_>,
    op: &str,
    artifact: &Path,
    entry: &safety::Entry,
) -> Result<()> {
    let relative = entry
        .path
        .strip_prefix(artifact)
        .map_err(|_| "A measured entry is outside the reviewed artifact")?;
    statement
        .execute(params![
            op,
            relative.as_os_str().as_bytes(),
            serde_json::to_string(&entry.meta.identity).map_err(err)?
        ])
        .map_err(err)?;
    Ok(())
}

#[derive(Default)]
struct Removed {
    private: u64,
    private_known: bool,
    // Removed regular names, including aliases of the same inode.
    files: u64,
}

struct LinkRemoval {
    reviewed: Identity,
    current: safety::EntryMeta,
}

/// Only completely verified internal groups enter this map. The manifest keeps
/// each path's original identity; current records the exact result of our last
/// unlink so later aliases cannot ignore unrelated ctime or link-count changes.
#[derive(Default)]
struct LinkRemovals {
    groups: HashMap<(u64, u64), LinkRemoval>,
}

impl LinkRemovals {
    fn from_closure(closure: safety::RegularLinkClosure) -> Result<Self> {
        let closed = closure.into_closed()?;
        let mut groups = HashMap::new();
        groups
            .try_reserve(closed.size_hint().0)
            .map_err(|_| "Hard-link removal state is unavailable; cleanup stopped.")?;
        for current in closed {
            groups.insert(
                (current.identity.device, current.identity.inode),
                LinkRemoval {
                    reviewed: current.identity.clone(),
                    current,
                },
            );
        }
        Ok(Self { groups })
    }

    fn ensure_exhausted(&self) -> Result<()> {
        if self.groups.values().any(|group| group.current.links != 0) {
            return Err(
                "A reviewed hard-link alias was not removed. Cleanup stopped without credit."
                    .into(),
            );
        }
        Ok(())
    }
}

/// A separate directory prevents ordinary writers retaining an artifact fd from
/// replacing the name we ultimately unlink. It is never recursively cleaned on
/// error: unexpected or cancelled captures remain available for recovery.
struct LeafRecovery {
    file: File,
    name: CString,
    path: PathBuf,
    identity: Identity,
}

impl LeafRecovery {
    fn path(parent: &Path, operation: &str) -> PathBuf {
        parent.join(format!(".chippytea-recovery-{operation}"))
    }

    fn create(parent: RawFd, parent_path: &Path, operation: &str) -> Result<Self> {
        let path = Self::path(parent_path, operation);
        let name = cstr(path.file_name().ok_or("Recovery directory has no name")?)?;
        if unsafe { libc::mkdirat(parent, name.as_ptr(), 0o700) } != 0 {
            return Err(format!("Cannot reserve recovery directory: {}", ioerr()));
        }
        let expected = identity_stat(&stat_at(parent, &name)?);
        let fd = unsafe {
            libc::openat(
                parent,
                name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            return Err(format!(
                "Cannot safely open recovery directory: {}",
                ioerr()
            ));
        }
        let file = unsafe { File::from_raw_fd(fd) };
        let actual = stat_file(&file)?;
        if !same_object(&expected, &identity_stat(&actual))
            || actual.st_uid != unsafe { libc::geteuid() }
            || actual.st_mode as u32 & 0o777 != 0o700
        {
            return Err("Recovery directory ownership or identity could not be verified.".into());
        }
        Ok(Self {
            file,
            name,
            path,
            identity: expected,
        })
    }

    fn leaf_name(operation: &str, relative: &Path) -> CString {
        // The full original path/identity was committed in cleanup_entries before
        // mutation. This deterministic name maps a retained leaf back to that row
        // without a durable write or an unbounded in-memory map for every file.
        let mut hash = blake3::Hasher::new();
        hash.update(operation.as_bytes());
        hash.update(&[0]);
        hash.update(relative.as_os_str().as_bytes());
        CString::new(format!("leaf-{}", hash.finalize().to_hex())).expect("hex has no NUL")
    }

    fn remove_empty(self, parent: RawFd) -> Result<()> {
        if !same_object(
            &self.identity,
            &identity_stat(&stat_at(parent, &self.name)?),
        ) {
            return Err("Recovery directory changed; its contents were preserved.".into());
        }
        if unsafe { libc::unlinkat(parent, self.name.as_ptr(), libc::AT_REMOVEDIR) } != 0 {
            return Err(format!(
                "Recovery directory was not empty or could not be removed: {}",
                ioerr()
            ));
        }
        // self.file closes here, before the caller samples available capacity.
        Ok(())
    }
}

fn stat_file(file: &File) -> Result<libc::stat> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstat(file.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(ioerr());
    }
    Ok(unsafe { stat.assume_init() })
}

fn same_after_rename(expected: &Identity, current: &Identity) -> bool {
    same_object(expected, current)
        && expected.size == current.size
        && expected.modified_ns == current.modified_ns
}

fn same_link_transition(
    before: &safety::EntryMeta,
    after: &safety::EntryMeta,
    remaining: u64,
) -> bool {
    let mut comparable = after.clone();
    comparable.identity.changed_ns = before.identity.changed_ns;
    comparable.links = before.links;
    after.links == remaining && comparable == *before
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LeafPhase {
    BeforeCapture,
    AfterCapture,
    BeforeUnlink,
    AfterUnlink,
}

#[cfg(test)]
type LeafTestHook = Box<dyn FnMut(LeafPhase, RawFd, &CStr)>;
#[cfg(test)]
thread_local! { static LEAF_TEST_HOOK:std::cell::RefCell<Option<LeafTestHook>>=const{std::cell::RefCell::new(None)}; }

fn leaf_hook(phase: LeafPhase, parent: RawFd, name: &CStr) {
    #[cfg(test)]
    LEAF_TEST_HOOK.with(|hook| {
        if let Some(hook) = hook.borrow_mut().as_mut() {
            hook(phase, parent, name);
        }
    });
    #[cfg(not(test))]
    let _ = (phase, parent, name);
}

struct RemovalContext<'a, 'p> {
    identities: CachedStatement<'a>,
    operation: &'a str,
    recovery: &'a LeafRecovery,
    removed: &'a mut Removed,
    cancel: &'a AtomicBool,
    progress: &'a mut Progress<'p>,
    links: LinkRemovals,
}

impl RemovalContext<'_, '_> {
    fn remove(&mut self, parent: RawFd, name: &CStr, relative: &Path, root: bool) -> Result<()> {
        cancelled(self.cancel)?;
        let expected: Identity = self
            .identities
            .query_row(
                params![self.operation, relative.as_os_str().as_bytes()],
                |row| Ok(serde_json::from_str(row.get_ref(0)?.as_str()?)),
            )
            .map_err(|_| "An unreviewed entry appeared. Cleanup stopped.".to_owned())?
            .map_err(err)?;
        let stat = stat_at(parent, name)?;
        let current = safety::EntryMeta::from_stat(&stat);
        let group = if current.is_file() {
            self.links
                .groups
                .get(&(current.identity.device, current.identity.inode))
        } else {
            None
        };
        let linked = group.is_some();
        let matches = if let Some(group) = group {
            group.reviewed == expected && group.current == current && current.links > 0
        } else if root {
            same_object(&expected, &current.identity)
        } else {
            expected == current.identity
        };
        if !matches {
            return Err("An item changed after review. Cleanup stopped.".into());
        }
        let kind = stat.st_mode as u32 & libc::S_IFMT as u32;
        if kind == libc::S_IFDIR as u32 {
            let fd = unsafe {
                libc::openat(
                    parent,
                    name.as_ptr(),
                    libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                )
            };
            if fd < 0 {
                return Err(ioerr());
            }
            let file = unsafe { File::from_raw_fd(fd) };
            if !same_object(&expected, &identity_stat(&stat_file(&file)?)) {
                return Err("Directory identity changed.".into());
            }
            each_entry(fd, |child| {
                self.remove(
                    fd,
                    child,
                    &relative.join(OsStr::from_bytes(child.to_bytes())),
                    false,
                )
            })?;
            cancelled(self.cancel)?;
            if !same_object(&expected, &identity_stat(&stat_at(parent, name)?)) {
                return Err("Directory was replaced during cleanup.".into());
            }
            // AT_REMOVEDIR cannot remove a replacement regular file/link, and a
            // newly populated directory causes ENOTEMPTY rather than data loss.
            if unsafe { libc::unlinkat(parent, name.as_ptr(), libc::AT_REMOVEDIR) } != 0 {
                return Err(ioerr());
            }
            self.progress.advance();
            Ok(())
        } else if kind == libc::S_IFREG as u32 || kind == libc::S_IFLNK as u32 {
            if !linked && current.links != 1 {
                return Err("A shared hard link appeared. Cleanup stopped.".into());
            }
            self.remove_leaf(parent, name, relative, &current, linked)
        } else {
            Err("Special files cannot be cleaned.".into())
        }
    }

    fn remove_leaf(
        &mut self,
        parent: RawFd,
        name: &CStr,
        relative: &Path,
        expected: &safety::EntryMeta,
        linked: bool,
    ) -> Result<()> {
        cancelled(self.cancel)?;
        let captured = LeafRecovery::leaf_name(self.operation, relative);
        leaf_hook(LeafPhase::BeforeCapture, parent, name);
        cancelled(self.cancel)?;
        if linked && safety::EntryMeta::from_stat(&stat_at(parent, name)?) != *expected {
            return Err("A hard-linked item changed before capture. Cleanup stopped.".into());
        }
        rename_exclusive(parent, name, self.recovery.file.as_raw_fd(), &captured)?;
        let mut unlinked = false;
        let result = (|| -> Result<()> {
            leaf_hook(LeafPhase::AfterCapture, parent, name);
            cancelled(self.cancel)?;
            let stat = stat_at(self.recovery.file.as_raw_fd(), &captured)?;
            let current = safety::EntryMeta::from_stat(&stat);
            // Capture may change ctime only. In particular, it cannot explain an
            // added outside link, different allocation, permissions or flags.
            if !same_link_transition(expected, &current, expected.links)
                || current.uid != unsafe { libc::geteuid() }
            {
                return Err(
                    "A replacement or changed leaf was captured; it was not deleted.".into(),
                );
            }
            if current.is_dataless() {
                return Err(
                    "The captured leaf became a cloud placeholder; it was not opened or deleted."
                        .into(),
                );
            }
            let regular = current.is_file();
            // Ordinary leaves need no descriptor after unlink. Read their
            // private allocation with matching identity metadata in one call;
            // both surrounding full stat checks remain authoritative. Linked
            // groups still require an fd for the post-unlink transition check.
            let direct_private = if regular && !linked && current.links == 1 {
                accounting::private_bytes_at(self.recovery.file.as_raw_fd(), &captured, &current)?
            } else {
                None
            };
            let file = if regular && direct_private.is_none() {
                let fd = unsafe {
                    libc::openat(
                        self.recovery.file.as_raw_fd(),
                        captured.as_ptr(),
                        libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
                    )
                };
                if fd < 0 {
                    return Err(ioerr());
                }
                let file = unsafe { File::from_raw_fd(fd) };
                if safety::EntryMeta::from_stat(&stat_file(&file)?) != current {
                    return Err("Captured file changed while opening.".into());
                }
                Some(file)
            } else {
                None
            };
            let last_link = regular && current.links == 1;
            let private = if last_link {
                direct_private.or_else(|| {
                    file.as_ref()
                        .and_then(|file| accounting::private_bytes(file.as_raw_fd()))
                })
            } else {
                None
            };
            leaf_hook(LeafPhase::BeforeUnlink, parent, name);
            cancelled(self.cancel)?;
            let latest =
                safety::EntryMeta::from_stat(&stat_at(self.recovery.file.as_raw_fd(), &captured)?);
            if latest != current {
                return Err("Captured leaf changed before removal; it was preserved.".into());
            }
            if unsafe { libc::unlinkat(self.recovery.file.as_raw_fd(), captured.as_ptr(), 0) } != 0
            {
                return Err(ioerr());
            }
            // This name is gone even if the following fstat fails. Record the
            // irreversible boundary before running any post-unlink checks.
            unlinked = true;
            if regular {
                self.removed.files += 1;
            }
            self.progress.advance();
            leaf_hook(LeafPhase::AfterUnlink, parent, name);
            if linked {
                let file = file
                    .as_ref()
                    .ok_or("Hard-link capture lost its file descriptor.")?;
                let after = safety::EntryMeta::from_stat(&stat_file(file)?);
                if !same_link_transition(&current, &after, current.links - 1) {
                    return Err("The hard-linked inode changed during removal.".into());
                }
                let group = self
                    .links
                    .groups
                    .get_mut(&(current.identity.device, current.identity.inode))
                    .ok_or("Hard-link removal state was lost.")?;
                group.current = after;
            }
            if last_link {
                self.removed.private = self.removed.private.saturating_add(private.unwrap_or(0));
                self.removed.private_known &= private.is_some();
            }
            drop(file); // close the final inode fd before capacity observation
            Ok(())
        })();
        match result {
            Ok(()) => Ok(()),
            Err(reason) if unlinked => {
                self.removed.private_known = false;
                Err(format!(
                    "{reason} The captured name was already removed. Cleanup stopped before removing another item."
                ))
            }
            Err(reason) => {
                let returned =
                    rename_exclusive(self.recovery.file.as_raw_fd(), &captured, parent, name)
                        .is_ok();
                if returned {
                    Err(format!(
                        "{reason} The captured leaf was put back without overwriting another item."
                    ))
                } else {
                    Err(format!(
                        "{reason} The captured leaf is retained at {} (original relative path: {}). No existing item was overwritten.",
                        self.recovery
                            .path
                            .join(OsStr::from_bytes(captured.to_bytes()))
                            .display(),
                        relative.display()
                    ))
                }
            }
        }
    }
}

fn rename_exclusive(from: RawFd, name: &CStr, to: RawFd, destination: &CStr) -> Result<()> {
    #[cfg(target_os = "macos")]
    let result = unsafe {
        libc::renameatx_np(
            from,
            name.as_ptr(),
            to,
            destination.as_ptr(),
            libc::RENAME_EXCL,
        )
    };
    #[cfg(target_os = "linux")]
    let result = unsafe {
        libc::renameat2(
            from,
            name.as_ptr(),
            to,
            destination.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    };
    if result == 0 { Ok(()) } else { Err(ioerr()) }
}

fn parents(path: &Path) -> Result<Vec<(PathBuf, Identity)>> {
    let mut result = Vec::new();
    let mut current = path.to_path_buf();
    loop {
        let i = safety::identity(&current)?;
        result.push((current.clone(), i));
        if !current.pop() {
            break;
        }
    }
    Ok(result)
}

pub fn execute(
    store: &mut Store,
    root: &Root,
    candidate: &Candidate,
    operation: &str,
    trash: Option<TrashCallback>,
    cancel: &AtomicBool,
) -> Result<Receipt> {
    execute_with_progress(
        store,
        root,
        candidate,
        operation,
        trash,
        cancel,
        |_, _, _| {},
    )
}

/// Progress counts filesystem entries, including directories and symbolic links.
/// A total of zero means the preparing traversal has not established it yet.
pub fn execute_with_progress(
    store: &mut Store,
    root: &Root,
    candidate: &Candidate,
    operation: &str,
    trash: Option<TrashCallback>,
    cancel: &AtomicBool,
    callback: impl FnMut(CleanupPhase, u64, u64),
) -> Result<Receipt> {
    execute_with_duplicate_guard(
        store, root, candidate, operation, trash, cancel, None, callback,
    )
}

/// Duplicate review adds a retained-file guard; it never changes the ordinary
/// single-path scanner evidence or grants permanent-deletion eligibility.
#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_with_duplicate_guard(
    store: &mut Store,
    root: &Root,
    candidate: &Candidate,
    operation: &str,
    trash: Option<TrashCallback>,
    cancel: &AtomicBool,
    duplicate_keeper: Option<&crate::duplicates::Input>,
    mut callback: impl FnMut(CleanupPhase, u64, u64),
) -> Result<Receipt> {
    let _local_io = safety::LocalOnlyIo::new()?;
    let mut progress = Progress::new(&mut callback);
    progress.start(CleanupPhase::Checking, 1);
    let result = execute_inner(
        store,
        root,
        candidate,
        operation,
        trash,
        cancel,
        duplicate_keeper,
        &mut progress,
    );
    progress.finish();
    result
}

#[allow(clippy::too_many_arguments)]
fn execute_inner(
    store: &mut Store,
    root: &Root,
    candidate: &Candidate,
    operation: &str,
    trash: Option<TrashCallback>,
    cancel: &AtomicBool,
    duplicate_keeper: Option<&crate::duplicates::Input>,
    progress: &mut Progress<'_>,
) -> Result<Receipt> {
    cancelled(cancel)?;
    if operation != "trash" && operation != "permanent" {
        return Err("Unsupported cleanup operation.".into());
    }
    if duplicate_keeper.is_some() && operation != "trash" {
        return Err("Duplicate review permits only Move to Trash.".into());
    }
    if operation == "permanent"
        && (!candidate.eligible_permanent
            || !crate::recommendations::permanent_kind(&candidate.kind))
    {
        return Err("Permanent cleanup is restricted to recognized developer artifacts.".into());
    }
    if candidate.blocked_reason.is_some() {
        return Err("This item is for inspection only.".into());
    }
    // Full revalidation below also records the durable manifest. This preflight
    // only establishes authorization and identity before creating its receipt.
    safety::validate_root(root)?;
    if candidate.root_id != root.id
        || candidate.path == root.path
        || !candidate.path.starts_with(&root.path)
    {
        return Err("The item is outside its authorized location".into());
    }
    safety::check_scope_policy(root, &candidate.path)?;
    if !candidate.suggestion_eligible || candidate.provisional {
        return Err("This item is not a completed cleanup suggestion.".into());
    }
    let current = safety::identity(&candidate.path)?;
    if current != candidate.identity || current.device != root.identity.device {
        return Err("The item changed since review; scan it again".into());
    }
    let parent_path = candidate
        .path
        .parent()
        .ok_or("Cannot clean a filesystem root")?;
    let parent = open_directory(parent_path)?;
    progress.complete();
    let name = cstr(candidate.path.file_name().ok_or("Missing filename")?)?;
    let id = unique_id();
    let stage_name = CString::new(format!(".chippytea-{id}")).unwrap();
    let stage = parent_path.join(OsStr::from_bytes(stage_name.to_bytes()));
    let recovery_path = LeafRecovery::path(parent_path, &id);
    let recovery_detail = format!(
        " If interrupted, inspect the staged item at {}. Captured leaves may be preserved at {}. Their original paths and identities remain in this operation's cleanup ledger.",
        stage.display(),
        recovery_path.display()
    );
    let mut receipt = Receipt {
        id: id.clone(),
        path: candidate.path.to_string_lossy().into(),
        title: candidate.title.clone(),
        operation: operation.into(),
        outcome: "prepared".into(),
        detail: if operation == "permanent" {
            format!("Cleanup prepared; no recovery is credited yet.{recovery_detail}")
        } else {
            format!(
                "Trash prepared. If interrupted, inspect {} and native Trash. No chips are earned.",
                stage.display()
            )
        },
        created_at: now(),
        reported_bytes: candidate.allocated_bytes,
        observed_bytes: 0,
        credited_bytes: 0,
        coins: 0,
        trash_path: None,
        can_restore: false,
        seq: None,
    };
    store.prepare_operation(root, candidate, &receipt, &stage)?;
    progress.start(CleanupPhase::Preparing, 0);
    let preparation = (|| -> Result<u64> {
        store.conn.execute_batch("CREATE TABLE IF NOT EXISTS cleanup_entries(operation_id TEXT NOT NULL,path BLOB NOT NULL,identity TEXT NOT NULL,PRIMARY KEY(operation_id,path)); CREATE TABLE IF NOT EXISTS operation_parents(operation_id TEXT PRIMARY KEY,json TEXT NOT NULL);").map_err(err)?;
        let transaction = store
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)
            .map_err(err)?;
        transaction
            .execute(
                "INSERT INTO operation_parents VALUES(?1,?2)",
                params![
                    id,
                    serde_json::to_string(&parents(parent_path)?).map_err(err)?
                ],
            )
            .map_err(err)?;
        let mut entries = 0u64;
        {
            let mut statement = transaction.prepare_cached(MANIFEST_INSERT).map_err(err)?;
            scanner::revalidate_observing(root, candidate, cancel, |entry, _| {
                record_manifest_entry(&mut statement, &id, &candidate.path, entry)?;
                entries = entries.saturating_add(1);
                progress.update(entries);
                cancelled(cancel)
            })?;
        }
        if identity_stat(&stat_at(parent.as_raw_fd(), &name)?) != candidate.identity {
            return Err("Identity changed before staging.".into());
        }
        cancelled(cancel)?;
        // All paths/identities and parent evidence commit before the first
        // rename. Failed observation or cancellation rolls the manifest back.
        transaction.commit().map_err(err)?;
        Ok(entries)
    })();
    let entries = match preparation {
        Ok(entries) => entries,
        Err(reason) => {
            receipt.outcome = if cancel.load(Ordering::Relaxed) {
                "cancelled"
            } else {
                "skipped"
            }
            .into();
            receipt.detail = format!(
                "Cleanup stopped before staging: {reason}. No file was removed and no chips were earned."
            );
            store.finish_operation(&receipt, None)?;
            return Ok(receipt);
        }
    };
    progress.complete();
    if cancel.load(Ordering::Relaxed) {
        receipt.outcome = "cancelled".into();
        receipt.detail =
            "Cancelled before staging. No file was removed and no chips were earned.".into();
        store.finish_operation(&receipt, None)?;
        return Ok(receipt);
    }
    if let Err(reason) =
        rename_exclusive(parent.as_raw_fd(), &name, parent.as_raw_fd(), &stage_name)
    {
        receipt.outcome = "skipped".into();
        receipt.detail = format!(
            "The item could not be staged without overwriting another item: {reason}. No file was removed."
        );
        store.finish_operation(&receipt, None)?;
        return Ok(receipt);
    }
    progress.start(CleanupPhase::Checking, entries);
    let staged_safe = (|| -> Result<(LinkRemovals, Option<crate::duplicates::RetainedFile>)> {
        store
            .conn
            .execute("UPDATE operations SET state='mutating' WHERE id=?1", [&id])
            .map_err(err)?;
        let staged_identity = identity_stat(&stat_at(parent.as_raw_fd(), &stage_name)?);
        let mut links = safety::RegularLinkClosure::default();
        let staged = safety::measure_try_observing_with_policy(
            &stage,
            root.identity.device,
            cancel,
            measurement_policy(candidate),
            |entry, measured| {
                links.observe(&entry.meta)?;
                progress.update(measured.entries);
                Ok(())
            },
        )?;
        if !same_object(&staged_identity, &candidate.identity)
            || staged.fingerprint != candidate.fingerprint
            || staged.unsafe_reason.is_some()
            || staged.pruned
            || staged.errors != 0
        {
            return Err("The staged artifact no longer matches the reviewed contents.".into());
        }
        let retained = if let Some(keeper) = duplicate_keeper {
            progress.start(
                CleanupPhase::Comparing,
                candidate.logical_bytes.saturating_mul(2),
            );
            Some(crate::duplicates::verify_staged(
                root,
                candidate,
                &stage,
                keeper,
                cancel,
                |bytes| progress.update(bytes),
            )?)
        } else {
            None
        };
        Ok((LinkRemovals::from_closure(links)?, retained))
    })();
    let (links, retained) = match staged_safe {
        Ok(links) => links,
        Err(reason) => {
            let restored =
                rename_exclusive(parent.as_raw_fd(), &stage_name, parent.as_raw_fd(), &name)
                    .is_ok();
            receipt.outcome = if cancel.load(Ordering::Relaxed) {
                "cancelled"
            } else {
                "skipped"
            }
            .into();
            receipt.detail = if restored {
                "Staged contents could not be verified; the original item was put back. Refresh to review again. No chips were earned.".into()
            } else {
                format!(
                    "Staged contents could not be verified. Inspect staged item at {}. No credit.",
                    stage.display()
                )
            };
            receipt.detail.push_str(&format!(" {reason}"));
            store.finish_operation(&receipt, None)?;
            return Ok(receipt);
        }
    };
    progress.complete();
    if operation == "trash" {
        progress.start(CleanupPhase::Removing, entries);
        let outcome = (|| -> Result<Identity> {
            let callback = trash
                .ok_or("Native Trash is unavailable. Permanent deletion was not attempted.")?;
            let input = cstr(stage.as_os_str())?;
            let mut output = vec![0i8; 16384];
            cancelled(cancel)?;
            if let Some(keeper) = &retained {
                keeper.validate(cancel)?;
            }
            let status = unsafe { callback(input.as_ptr(), output.as_mut_ptr(), output.len()) };
            let message = unsafe { CStr::from_ptr(output.as_ptr()) }
                .to_string_lossy()
                .into_owned();
            if status != 0 {
                return Err(message);
            }
            let trash_path = PathBuf::from(message);
            receipt.trash_path = Some(trash_path.to_string_lossy().into());
            let identity = safety::identity(&trash_path)?;
            if !same_object(&identity, &candidate.identity) {
                return Err("Native Trash returned an unexpected item identity.".into());
            }
            receipt.trash_path = Some(trash_path.to_string_lossy().into());
            Ok(identity)
        })();
        match outcome {
            Ok(identity) => {
                progress.complete();
                receipt.outcome = "trashed".into();
                receipt.detail="Moved to native Trash. This did not earn chips or establish freed space. You can restore this item while its identity and original destination remain valid.".into();
                receipt.can_restore = true;
                store.finish_operation(&receipt, Some(&identity))?;
            }
            Err(e) => {
                let restored =
                    rename_exclusive(parent.as_raw_fd(), &stage_name, parent.as_raw_fd(), &name)
                        .is_ok();
                receipt.outcome = "failed".into();
                receipt.detail = format!(
                    "Trash failed: {e}. {}",
                    if restored {
                        "The item was put back at its original location.".to_owned()
                    } else {
                        format!(
                            "Inspect {} and Trash; no deletion fallback was used.",
                            stage.display()
                        )
                    }
                );
                store.finish_operation(&receipt, None)?;
            }
        }
    } else {
        let recovery = match LeafRecovery::create(parent.as_raw_fd(), parent_path, &id) {
            Ok(recovery) => recovery,
            Err(reason) => {
                receipt.outcome = "failed".into();
                receipt.detail =
                    format!("Cleanup stopped before permanent removal: {reason}.{recovery_detail}");
                store.finish_operation(&receipt, None)?;
                return Ok(receipt);
            }
        };
        let window = accounting::begin(store, parent_path).ok();
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        progress.start(CleanupPhase::Removing, entries);
        let result = (|| {
            // Keep the already committed manifest in one read snapshot. Without
            // this scope SQLite starts and ends a transaction for every leaf.
            // Drop the statement before releasing the snapshot, and release it
            // on errors too, before capacity accounting writes the receipt.
            let transaction = store.conn.transaction().map_err(err)?;
            let identities = transaction.prepare_cached(MANIFEST_IDENTITY).map_err(err)?;
            let mut context = RemovalContext {
                identities,
                operation: &id,
                recovery: &recovery,
                removed: &mut removed,
                cancel,
                progress,
                links,
            };
            context.remove(parent.as_raw_fd(), &stage_name, Path::new(""), true)?;
            context.links.ensure_exhausted()?;
            drop(context);
            transaction.commit().map_err(err)
        })();
        let result = result.and_then(|()| recovery.remove_empty(parent.as_raw_fd()));
        progress.finish();
        match result {
            Ok(()) => {
                receipt.outcome = "removed".into();
                receipt.detail="Permanently removed the reviewed developer artifacts. Reinstalling or rebuilding creates new artifacts; it does not restore these contents.".into();
            }
            Err(e) => {
                receipt.outcome = if cancel.load(Ordering::Relaxed) {
                    "cancelled"
                } else {
                    "partial"
                }
                .into();
                receipt.detail = format!(
                    "{e} {} files were removed. No partial cleanup earns chips.{recovery_detail}",
                    removed.files
                );
            }
        }
        progress.start(CleanupPhase::Accounting, 1);
        if let Some(window) = window {
            if let Err(e) = accounting::finish(
                store,
                window,
                parent_path,
                &mut receipt,
                removed.private,
                removed.private_known,
            ) {
                receipt.credited_bytes = 0;
                receipt.coins = 0;
                receipt
                    .detail
                    .push_str(&format!(" Accounting remains uncredited: {e}"));
                store.finish_operation(&receipt, None)?;
            }
        } else {
            receipt
                .detail
                .push_str(" Storage accounting was unavailable; no chips were earned.");
            store.finish_operation(&receipt, None)?;
        }
    }
    store.discard_candidate(&candidate.id)?;
    // Retained manifest rows map deterministic recovery names to original paths.
    // Never erase that evidence after a partial or cancelled mutation.
    if matches!(receipt.outcome.as_str(), "removed" | "trashed") {
        store
            .conn
            .execute("DELETE FROM cleanup_entries WHERE operation_id=?1", [id])
            .map_err(err)?;
    }
    if operation == "permanent" {
        progress.complete();
    }
    Ok(receipt)
}

pub fn restore(store: &mut Store, id: &str, cancel: &AtomicBool) -> Result<Receipt> {
    let _local_io = safety::LocalOnlyIo::new()?;
    let (root, candidate, mut receipt, trash_identity, _) = store.operation(id)?;
    if receipt.operation != "trash" || receipt.outcome != "trashed" || !receipt.can_restore {
        return Err("This operation has no restorable Trash item.".into());
    }
    let current_root = store
        .roots()?
        .into_iter()
        .find(|authorized| {
            candidate.path.starts_with(&authorized.path)
                && root.identity.device == authorized.identity.device
        })
        .ok_or("Authorize the original destination before restoring.")?;
    // A user may have broadened Projects to their home folder since using Trash.
    // Both the new grant and the original recorded root must still be the same objects.
    safety::validate_root(&current_root)?;
    safety::validate_root(&root)?;
    let parent_path = candidate
        .path
        .parent()
        .ok_or("Missing destination parent")?;
    let recorded: String = store
        .conn
        .query_row(
            "SELECT json FROM operation_parents WHERE operation_id=?1",
            [id],
            |r| r.get(0),
        )
        .map_err(err)?;
    let recorded: Vec<(PathBuf, Identity)> = serde_json::from_str(&recorded).map_err(err)?;
    for (path, identity) in recorded {
        if !same_object(&identity, &safety::identity(&path)?) {
            return Err("A destination parent changed; restore was refused.".into());
        }
    }
    let destination = open_directory(parent_path)?;
    let trash = PathBuf::from(receipt.trash_path.as_ref().ok_or("Missing Trash path")?);
    let source = open_directory(trash.parent().ok_or("Missing Trash parent")?)?;
    let source_name = cstr(trash.file_name().ok_or("Missing Trash filename")?)?;
    let destination_name = cstr(
        candidate
            .path
            .file_name()
            .ok_or("Missing destination filename")?,
    )?;
    let observed = identity_stat(&stat_at(source.as_raw_fd(), &source_name)?);
    let expected = trash_identity.ok_or("Missing Trash identity")?;
    // Native Trash can update a directory's metadata after returning. Only its
    // historical root ctime may drift; the full contents fingerprint remains
    // mandatory. File roots need exact ctime because Digest normalizes it.
    let matches = if expected.mode & libc::S_IFMT as u32 == libc::S_IFDIR as u32 {
        same_after_rename(&expected, &observed)
    } else {
        expected == observed
    };
    if !matches {
        return Err("Trash item changed; restore was refused.".into());
    }
    let measured = safety::measure_with_policy(
        &trash,
        root.identity.device,
        cancel,
        measurement_policy(&candidate),
    )?;
    if measured.fingerprint != candidate.fingerprint || measured.unsafe_reason.is_some() {
        return Err("Trash contents changed; inspect them in Finder.".into());
    }
    cancelled(cancel)?;
    store
        .conn
        .execute("UPDATE operations SET state='restoring' WHERE id=?1", [id])
        .map_err(err)?;
    let moved = (|| -> Result<()> {
        #[cfg(test)]
        restore_hook(source.as_raw_fd(), &source_name);
        cancelled(cancel)?;
        // Tolerance is historical only. Any identity change during validation,
        // including directory ctime, invalidates the object about to be moved.
        if identity_stat(&stat_at(source.as_raw_fd(), &source_name)?) != observed {
            return Err("Trash item changed during validation; restore was refused.".into());
        }
        rename_exclusive(
            source.as_raw_fd(),
            &source_name,
            destination.as_raw_fd(),
            &destination_name,
        )
    })();
    if let Err(reason) = moved {
        store
            .conn
            .execute("UPDATE operations SET state='trashed' WHERE id=?1", [id])
            .map_err(err)?;
        return Err(reason);
    }
    receipt.outcome = "restored".into();
    receipt.can_restore = false;
    receipt.detail="Restored to the original authorized location without overwriting another file. No chips were earned.".into();
    store.finish_operation(&receipt, None)?;
    Ok(receipt)
}

#[cfg(test)]
type RestoreTestHook = Box<dyn FnMut(RawFd, &CStr)>;
#[cfg(test)]
thread_local! { static RESTORE_TEST_HOOK: std::cell::RefCell<Option<RestoreTestHook>> = const { std::cell::RefCell::new(None) }; }
#[cfg(test)]
fn restore_hook(parent: RawFd, name: &CStr) {
    RESTORE_TEST_HOOK.with(|hook| {
        if let Some(callback) = hook.borrow_mut().as_mut() {
            callback(parent, name);
        }
    });
}

// Staging renames the artifact root. Its validated kind, not the temporary
// filename, selects the same traversal policy used for review fingerprints.
fn measurement_policy(candidate: &Candidate) -> safety::MeasurementPolicy {
    if crate::recommendations::developer_measurement(&candidate.kind) {
        safety::MeasurementPolicy::Developer
    } else {
        safety::MeasurementPolicy::Strict
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        cell::RefCell,
        io::{Read, Write},
        os::unix::fs::PermissionsExt,
        rc::Rc,
        sync::Arc,
    };

    struct RestoreFixture {
        store: Store,
        candidate: Candidate,
        trash: PathBuf,
        _temp: tempfile::TempDir,
    }

    fn restore_fixture(directory: bool) -> RestoreFixture {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let scope = base.join("authorized");
        let trash_parent = base.join("disposable-trash");
        std::fs::create_dir(&scope).unwrap();
        std::fs::create_dir(&trash_parent).unwrap();
        let path = scope.join("restored");
        if directory {
            std::fs::create_dir(&path).unwrap();
            std::fs::write(path.join("payload"), b"reviewed payload").unwrap();
        } else {
            std::fs::write(&path, b"reviewed payload").unwrap();
        }
        let root = safety::authorize(&scope, "folder").unwrap();
        let measured = safety::measure_with_policy(
            &path,
            root.identity.device,
            &AtomicBool::new(false),
            if directory {
                safety::MeasurementPolicy::Developer
            } else {
                safety::MeasurementPolicy::Strict
            },
        )
        .unwrap();
        assert!(measured.unsafe_reason.is_none());
        let identity = safety::identity(&path).unwrap();
        // A synthetic historical Trash record exercises restore with tiny files.
        // No cleanup gate is bypassed and execute is never called by this fixture.
        let candidate = Candidate {
            id: "restore-candidate".into(),
            root_id: root.id.clone(),
            path: path.clone(),
            title: "Disposable restore fixture".into(),
            kind: if directory { "node" } else { "download" }.into(),
            logical_bytes: measured.logical_bytes,
            allocated_bytes: measured.allocated_bytes,
            file_count: measured.files,
            modified_ns: identity.modified_ns,
            explanation: "Synthetic historical record".into(),
            consequence: "Restore disposable contents".into(),
            eligible_permanent: false,
            blocked_reason: None,
            identity,
            fingerprint: measured.fingerprint,
            evidence: String::new(),
            suggestion_eligible: false,
            provisional: false,
        };
        let trash = trash_parent.join("item");
        let receipt = Receipt {
            id: "restore-operation".into(),
            path: path.to_string_lossy().into(),
            title: candidate.title.clone(),
            operation: "trash".into(),
            outcome: "trashed".into(),
            detail: "Disposable historical Trash fixture".into(),
            created_at: now(),
            reported_bytes: measured.allocated_bytes,
            observed_bytes: 0,
            credited_bytes: 0,
            coins: 0,
            trash_path: Some(trash.to_string_lossy().into()),
            can_restore: true,
            seq: None,
        };
        let mut store = Store::open(&base.join("ledger.sqlite")).unwrap();
        store.add_root(&root).unwrap();
        store
            .prepare_operation(&root, &candidate, &receipt, &base.join("unused-stage"))
            .unwrap();
        store
            .conn
            .execute_batch(
                "CREATE TABLE operation_parents(operation_id TEXT PRIMARY KEY,json TEXT NOT NULL);",
            )
            .unwrap();
        store
            .conn
            .execute(
                "INSERT INTO operation_parents VALUES(?1,?2)",
                params![
                    receipt.id,
                    serde_json::to_string(&parents(&scope).unwrap()).unwrap()
                ],
            )
            .unwrap();
        std::fs::rename(&path, &trash).unwrap();
        store
            .finish_operation(&receipt, Some(&safety::identity(&trash).unwrap()))
            .unwrap();
        RestoreFixture {
            store,
            candidate,
            trash,
            _temp: temp,
        }
    }

    fn change_only_ctime(path: &Path) {
        let before = safety::identity(path).unwrap();
        let permissions = std::fs::metadata(path).unwrap().permissions();
        std::fs::set_permissions(
            path,
            std::fs::Permissions::from_mode(permissions.mode() ^ 0o010),
        )
        .unwrap();
        std::fs::set_permissions(path, permissions).unwrap();
        let after = safety::identity(path).unwrap();
        assert_ne!(before.changed_ns, after.changed_ns);
        let mut expected = before;
        expected.changed_ns = after.changed_ns;
        assert_eq!(after, expected, "Only ctime may change in this fixture");
    }

    fn refused_restore(fixture: &mut RestoreFixture) -> String {
        let reason = restore(
            &mut fixture.store,
            "restore-operation",
            &AtomicBool::new(false),
        )
        .unwrap_err();
        assert!(!fixture.candidate.path.exists());
        let (_, _, receipt, _, _) = fixture.store.operation("restore-operation").unwrap();
        assert_eq!(receipt.outcome, "trashed");
        assert!(receipt.can_restore);
        let state: String = fixture
            .store
            .conn
            .query_row(
                "SELECT state FROM operations WHERE id='restore-operation'",
                [],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(
            state, "trashed",
            "A refused restore must remain recoverable"
        );
        let wallet = fixture.store.wallet().unwrap();
        assert_eq!(
            (
                wallet.collected_coins,
                wallet.pending_coins,
                wallet.fractional_bytes,
                wallet.credited_bytes
            ),
            (0, 0, 0, 0)
        );
        reason
    }

    struct RestoreHookGuard;
    impl Drop for RestoreHookGuard {
        fn drop(&mut self) {
            RESTORE_TEST_HOOK.with(|hook| *hook.borrow_mut() = None);
        }
    }
    fn restore_test_hook(callback: impl FnMut(RawFd, &CStr) + 'static) -> RestoreHookGuard {
        RESTORE_TEST_HOOK.with(|hook| *hook.borrow_mut() = Some(Box::new(callback)));
        RestoreHookGuard
    }

    #[test]
    fn restore_allows_only_historical_directory_root_ctime_drift() {
        let mut fixture = restore_fixture(true);
        change_only_ctime(&fixture.trash);
        let receipt = restore(
            &mut fixture.store,
            "restore-operation",
            &AtomicBool::new(false),
        )
        .unwrap();
        assert_eq!(receipt.outcome, "restored");
        assert!(!receipt.can_restore);
        assert!(!fixture.trash.exists());
        assert_eq!(
            std::fs::read(fixture.candidate.path.join("payload")).unwrap(),
            b"reviewed payload"
        );
        assert_eq!((receipt.credited_bytes, receipt.coins), (0, 0));
        assert_eq!(fixture.store.wallet().unwrap().credited_bytes, 0);
    }

    #[test]
    fn restore_refuses_directory_root_permission_size_and_mtime_changes() {
        for change in ["permissions", "size", "mtime"] {
            let mut fixture = restore_fixture(true);
            let before = std::fs::metadata(&fixture.trash).unwrap();
            match change {
                "permissions" => std::fs::set_permissions(
                    &fixture.trash,
                    std::fs::Permissions::from_mode(before.permissions().mode() ^ 0o010),
                )
                .unwrap(),
                "size" => {
                    for index in 0..512 {
                        std::fs::write(fixture.trash.join(format!("extra-{index}")), b"").unwrap();
                        if std::fs::metadata(&fixture.trash).unwrap().len() != before.len() {
                            break;
                        }
                    }
                    assert_ne!(
                        std::fs::metadata(&fixture.trash).unwrap().len(),
                        before.len()
                    );
                    File::open(&fixture.trash)
                        .unwrap()
                        .set_times(
                            std::fs::FileTimes::new().set_modified(before.modified().unwrap()),
                        )
                        .unwrap();
                }
                "mtime" => {
                    File::open(&fixture.trash)
                        .unwrap()
                        .set_times(std::fs::FileTimes::new().set_modified(
                            std::time::SystemTime::UNIX_EPOCH + Duration::from_secs(123),
                        ))
                        .unwrap()
                }
                _ => unreachable!(),
            }
            let reason = refused_restore(&mut fixture);
            assert!(reason.contains("Trash item changed"), "{change}: {reason}");
            assert_eq!(
                std::fs::read(fixture.trash.join("payload")).unwrap(),
                b"reviewed payload"
            );
        }
    }

    #[test]
    fn restore_refuses_changed_descendant_even_when_its_mtime_is_reset() {
        let mut fixture = restore_fixture(true);
        let root_before = safety::identity(&fixture.trash).unwrap();
        let payload = fixture.trash.join("payload");
        let modified = std::fs::metadata(&payload).unwrap().modified().unwrap();
        std::fs::write(&payload, b"modified payload").unwrap();
        File::open(&payload)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(modified))
            .unwrap();
        assert_eq!(safety::identity(&fixture.trash).unwrap(), root_before);
        let reason = refused_restore(&mut fixture);
        assert!(reason.contains("Trash contents changed"), "{reason}");
        assert_eq!(std::fs::read(payload).unwrap(), b"modified payload");
    }

    #[test]
    fn restore_never_ignores_regular_file_root_ctime() {
        for rewrite in [false, true] {
            let mut fixture = restore_fixture(false);
            if rewrite {
                let before = std::fs::metadata(&fixture.trash).unwrap();
                std::fs::write(&fixture.trash, b"modified payload").unwrap();
                File::open(&fixture.trash)
                    .unwrap()
                    .set_times(std::fs::FileTimes::new().set_modified(before.modified().unwrap()))
                    .unwrap();
            } else {
                change_only_ctime(&fixture.trash);
            }
            let measured = safety::measure_with_policy(
                &fixture.trash,
                fixture.candidate.identity.device,
                &AtomicBool::new(false),
                safety::MeasurementPolicy::Strict,
            )
            .unwrap();
            assert_eq!(
                measured.fingerprint, fixture.candidate.fingerprint,
                "Root ctime is deliberately absent from the digest"
            );
            let reason = refused_restore(&mut fixture);
            assert!(reason.contains("Trash item changed"), "{reason}");
            assert_eq!(
                std::fs::read(&fixture.trash).unwrap(),
                if rewrite {
                    b"modified payload"
                } else {
                    b"reviewed payload"
                }
            );
        }
    }

    #[test]
    fn restore_rechecks_exact_directory_ctime_after_measurement() {
        let mut fixture = restore_fixture(true);
        let path = fixture.trash.clone();
        let _hook = restore_test_hook(move |_, _| change_only_ctime(&path));
        let reason = refused_restore(&mut fixture);
        assert!(reason.contains("during validation"), "{reason}");
        assert_eq!(
            std::fs::read(fixture.trash.join("payload")).unwrap(),
            b"reviewed payload"
        );
    }

    #[test]
    fn restore_refuses_root_symlinks_before_or_after_measurement() {
        for late in [false, true] {
            let mut fixture = restore_fixture(true);
            let path = fixture.trash.clone();
            let saved = path.with_file_name("saved-original");
            let saved_for_hook = saved.clone();
            let substitute = move || {
                std::fs::rename(&path, &saved_for_hook).unwrap();
                std::os::unix::fs::symlink(&saved_for_hook, &path).unwrap();
            };
            let _hook = if late {
                Some(restore_test_hook(move |_, _| substitute()))
            } else {
                substitute();
                None
            };
            refused_restore(&mut fixture);
            assert_eq!(std::fs::read_link(&fixture.trash).unwrap(), saved);
            assert_eq!(
                std::fs::read(saved.join("payload")).unwrap(),
                b"reviewed payload"
            );
        }
    }

    #[test]
    fn restore_refuses_a_directory_substituted_after_measurement() {
        let mut fixture = restore_fixture(true);
        let path = fixture.trash.clone();
        let saved = path.with_file_name("saved-original");
        let saved_for_hook = saved.clone();
        let _hook = restore_test_hook(move |_, _| {
            std::fs::rename(&path, &saved_for_hook).unwrap();
            std::fs::create_dir(&path).unwrap();
            std::fs::write(path.join("payload"), b"replacement payload").unwrap();
        });
        let reason = refused_restore(&mut fixture);
        assert!(reason.contains("during validation"), "{reason}");
        assert_eq!(
            std::fs::read(fixture.trash.join("payload")).unwrap(),
            b"replacement payload"
        );
        assert_eq!(
            std::fs::read(saved.join("payload")).unwrap(),
            b"reviewed payload"
        );
    }

    struct Fixture {
        store: Store,
        parent: File,
        recovery: LeafRecovery,
        base: PathBuf,
        artifact: PathBuf,
        _temp: tempfile::TempDir,
    }

    fn fixture(link: bool) -> Fixture {
        populated_fixture(|artifact, base| {
            if link {
                std::fs::write(base.join("outside"), b"personal outside target").unwrap();
                std::os::unix::fs::symlink("../outside", artifact.join("payload")).unwrap();
            } else {
                std::fs::write(artifact.join("payload"), b"reviewed payload").unwrap();
            }
        })
    }

    fn linked_fixture() -> Fixture {
        populated_fixture(|artifact, _| {
            std::fs::create_dir(artifact.join("left")).unwrap();
            std::fs::create_dir(artifact.join("right")).unwrap();
            std::fs::write(artifact.join("left/payload"), [0x61; 8192]).unwrap();
            std::fs::hard_link(
                artifact.join("left/payload"),
                artifact.join("right/payload"),
            )
            .unwrap();
        })
    }

    fn populated_fixture(populate: impl FnOnce(&Path, &Path)) -> Fixture {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let artifact = base.join("artifact");
        std::fs::create_dir(&artifact).unwrap();
        populate(&artifact, &base);
        let store = Store::open(&base.join("ledger.sqlite")).unwrap();
        store.conn.execute_batch("CREATE TABLE cleanup_entries(operation_id TEXT NOT NULL,path BLOB NOT NULL,identity TEXT NOT NULL,PRIMARY KEY(operation_id,path));").unwrap();
        let parent = open_directory(&base).unwrap();
        let device = safety::identity(&artifact).unwrap().device;
        {
            let mut statement = store.conn.prepare_cached(MANIFEST_INSERT).unwrap();
            safety::measure_observing_with_policy(
                &artifact,
                device,
                &AtomicBool::new(false),
                safety::MeasurementPolicy::Developer,
                |entry, _| {
                    record_manifest_entry(&mut statement, "fixture", &artifact, entry).unwrap();
                },
            )
            .unwrap();
        }
        let recovery = LeafRecovery::create(parent.as_raw_fd(), &base, "fixture").unwrap();
        Fixture {
            store,
            parent,
            recovery,
            base,
            artifact,
            _temp: temp,
        }
    }

    struct HookGuard;
    impl Drop for HookGuard {
        fn drop(&mut self) {
            LEAF_TEST_HOOK.with(|hook| *hook.borrow_mut() = None);
        }
    }
    fn hook(callback: impl FnMut(LeafPhase, RawFd, &CStr) + 'static) -> HookGuard {
        LEAF_TEST_HOOK.with(|hook| *hook.borrow_mut() = Some(Box::new(callback)));
        HookGuard
    }

    fn write_at(parent: RawFd, name: &CStr, bytes: &[u8]) {
        let fd = unsafe {
            libc::openat(
                parent,
                name.as_ptr(),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0o600,
            )
        };
        assert!(fd >= 0, "{}", ioerr());
        let mut file = unsafe { File::from_raw_fd(fd) };
        file.write_all(bytes).unwrap();
    }

    fn fixture_links(fixture: &Fixture, cancel: &AtomicBool) -> Result<(LinkRemovals, u64)> {
        let mut closure = safety::RegularLinkClosure::default();
        let measured = safety::measure_try_observing_with_policy(
            &fixture.artifact,
            safety::identity(&fixture.artifact)?.device,
            cancel,
            safety::MeasurementPolicy::Developer,
            |entry, _| closure.observe(&entry.meta),
        )?;
        Ok((LinkRemovals::from_closure(closure)?, measured.entries))
    }

    fn remove_fixture(fixture: &Fixture, cancel: &AtomicBool, removed: &mut Removed) -> Result<()> {
        let (links, entries) = fixture_links(fixture, cancel)?;
        let mut callback = |_, _, _| {};
        let mut progress = Progress::new(&mut callback);
        progress.start(CleanupPhase::Removing, entries);
        let mut context = RemovalContext {
            identities: fixture
                .store
                .conn
                .prepare_cached(MANIFEST_IDENTITY)
                .unwrap(),
            operation: "fixture",
            recovery: &fixture.recovery,
            removed,
            cancel,
            progress: &mut progress,
            links,
        };
        context.remove(fixture.parent.as_raw_fd(), c"artifact", Path::new(""), true)?;
        context.links.ensure_exhausted()
    }

    fn remaining_alias(artifact: &Path) -> PathBuf {
        [
            artifact.join("left/payload"),
            artifact.join("right/payload"),
        ]
        .into_iter()
        .find(|path| path.exists())
        .expect("A reviewed alias remains")
    }

    #[test]
    fn closed_aliases_follow_own_ctime_changes_and_count_private_bytes_only_once() {
        let fixture = linked_fixture();
        let recovery = fixture.recovery.path.clone();
        let observations = Rc::new(RefCell::new(Vec::new()));
        let recorded = Rc::clone(&observations);
        let _hook = hook(move |phase, _, _| {
            if phase == LeafPhase::BeforeUnlink {
                let captured = std::fs::read_dir(&recovery)
                    .unwrap()
                    .next()
                    .unwrap()
                    .unwrap()
                    .path();
                let file = File::open(captured).unwrap();
                let current = safety::EntryMeta::from_stat(&stat_file(&file).unwrap());
                let private = (current.links == 1)
                    .then(|| accounting::private_bytes(file.as_raw_fd()))
                    .flatten();
                recorded.borrow_mut().push((current.links, private));
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).unwrap();
        assert!(!fixture.artifact.exists());
        assert_eq!(removed.files, 2);
        let records = observations.borrow();
        assert_eq!(
            records.iter().map(|record| record.0).collect::<Vec<_>>(),
            vec![2, 1]
        );
        let final_private = records[1].1;
        assert_eq!(removed.private, final_private.unwrap_or(0));
        assert_eq!(removed.private_known, final_private.is_some());
        assert!(
            std::fs::read_dir(&fixture.recovery.path)
                .unwrap()
                .next()
                .is_none()
        );
    }

    #[test]
    fn an_outside_link_added_after_closure_is_preserved_before_any_unlink() {
        for boundary in [LeafPhase::BeforeCapture, LeafPhase::AfterCapture] {
            let fixture = linked_fixture();
            let artifact = fixture.artifact.clone();
            let outside = fixture.base.join("new-outside-link");
            let destination = outside.clone();
            let _hook = hook(move |phase, _, _| {
                if phase == boundary {
                    std::fs::hard_link(remaining_alias(&artifact), &destination).unwrap();
                }
            });
            let mut removed = Removed {
                private_known: true,
                ..Default::default()
            };
            assert!(remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).is_err());
            for path in [
                fixture.artifact.join("left/payload"),
                fixture.artifact.join("right/payload"),
                outside,
            ] {
                assert_eq!(std::fs::read(path).unwrap(), [0x61; 8192]);
            }
            assert_eq!((removed.files, removed.private), (0, 0));
            assert!(
                std::fs::read_dir(&fixture.recovery.path)
                    .unwrap()
                    .next()
                    .is_none()
            );
        }
    }

    #[test]
    fn a_same_size_rewrite_with_restored_mtime_between_aliases_stops_cleanup() {
        let fixture = linked_fixture();
        let artifact = fixture.artifact.clone();
        let mut captures = 0;
        let _hook = hook(move |phase, _, _| {
            if phase == LeafPhase::BeforeCapture {
                captures += 1;
                if captures == 2 {
                    let path = remaining_alias(&artifact);
                    let mut file = std::fs::OpenOptions::new().write(true).open(path).unwrap();
                    let before = safety::EntryMeta::from_stat(&stat_file(&file).unwrap());
                    let modified = file.metadata().unwrap().modified().unwrap();
                    file.write_all(&[0x62; 8192]).unwrap();
                    file.set_times(std::fs::FileTimes::new().set_modified(modified))
                        .unwrap();
                    let after = safety::EntryMeta::from_stat(&stat_file(&file).unwrap());
                    assert_eq!(before.identity.size, after.identity.size);
                    assert_eq!(before.identity.modified_ns, after.identity.modified_ns);
                    assert_ne!(before.identity.changed_ns, after.identity.changed_ns);
                }
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let reason = remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).unwrap_err();
        assert!(reason.contains("changed before capture"), "{reason}");
        assert_eq!(
            std::fs::read(remaining_alias(&fixture.artifact)).unwrap(),
            [0x62; 8192]
        );
        assert_eq!((removed.files, removed.private), (1, 0));
    }

    #[test]
    fn a_post_unlink_link_count_failure_reports_the_removed_name_without_false_restore() {
        let fixture = linked_fixture();
        let artifact = fixture.artifact.clone();
        let outside = fixture.base.join("new-outside-link");
        let destination = outside.clone();
        let _hook = hook(move |phase, _, _| {
            if phase == LeafPhase::AfterUnlink {
                std::fs::hard_link(remaining_alias(&artifact), &destination).unwrap();
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let reason = remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).unwrap_err();
        assert!(
            reason.contains("captured name was already removed"),
            "{reason}"
        );
        assert!(!reason.contains("put back"));
        assert!(!reason.contains("retained at"));
        assert_eq!(
            (removed.files, removed.private, removed.private_known),
            (1, 0, false)
        );
        assert_eq!(std::fs::read(outside).unwrap(), [0x61; 8192]);
        assert_eq!(
            std::fs::read(remaining_alias(&fixture.artifact)).unwrap(),
            [0x61; 8192]
        );
        assert!(
            std::fs::read_dir(&fixture.recovery.path)
                .unwrap()
                .next()
                .is_none()
        );
    }

    #[test]
    fn cancellation_after_one_alias_keeps_remaining_contents_and_manifest_without_credit() {
        let fixture = linked_fixture();
        let cancel = Arc::new(AtomicBool::new(false));
        let signal = Arc::clone(&cancel);
        let _hook = hook(move |phase, _, _| {
            if phase == LeafPhase::AfterUnlink {
                signal.store(true, Ordering::Relaxed);
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let reason = remove_fixture(&fixture, &cancel, &mut removed).unwrap_err();
        assert!(reason.contains("Cancelled"), "{reason}");
        assert_eq!(
            (removed.files, removed.private, removed.private_known),
            (1, 0, true)
        );
        let remaining = remaining_alias(&fixture.artifact);
        assert_eq!(std::fs::read(&remaining).unwrap(), [0x61; 8192]);
        let file = File::open(remaining).unwrap();
        assert_eq!(stat_file(&file).unwrap().st_nlink, 1);
        let recorded: u64 = fixture
            .store
            .conn
            .query_row(
                "SELECT count(*) FROM cleanup_entries WHERE operation_id='fixture'",
                [],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(recorded, 5);
        assert_eq!(fixture.store.wallet().unwrap().credited_bytes, 0);
    }

    #[test]
    fn missing_aliases_cannot_satisfy_the_terminal_group_proof() {
        let fixture = linked_fixture();
        let cancel = AtomicBool::new(false);
        let (links, entries) = fixture_links(&fixture, &cancel).unwrap();
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let mut callback = |_, _, _| {};
        let mut progress = Progress::new(&mut callback);
        progress.start(CleanupPhase::Removing, entries);
        let parent = open_directory(&fixture.artifact.join("left")).unwrap();
        let mut context = RemovalContext {
            identities: fixture
                .store
                .conn
                .prepare_cached(MANIFEST_IDENTITY)
                .unwrap(),
            operation: "fixture",
            recovery: &fixture.recovery,
            removed: &mut removed,
            cancel: &cancel,
            progress: &mut progress,
            links,
        };
        context
            .remove(
                parent.as_raw_fd(),
                c"payload",
                Path::new("left/payload"),
                false,
            )
            .unwrap();
        let outside = fixture.base.join("moved-alias");
        std::fs::rename(fixture.artifact.join("right/payload"), &outside).unwrap();
        // A live directory iterator may omit a name removed before it is read.
        // Reaching its end therefore cannot substitute for exhausting the group.
        let reason = context.links.ensure_exhausted().unwrap_err();
        assert!(reason.contains("alias was not removed"), "{reason}");
        drop(context);
        assert_eq!((removed.files, removed.private), (1, 0));
        assert_eq!(std::fs::read(outside).unwrap(), [0x61; 8192]);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn review_fixture(large: bool) -> (tempfile::TempDir, Store, Root, Candidate) {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let scope = base.join("scope");
        let project = scope.join("project");
        let artifact = project.join("node_modules");
        std::fs::create_dir_all(&artifact).unwrap();
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
        let payload = artifact.join("payload");
        {
            let mut file = File::create(&payload).unwrap();
            if large {
                let block = vec![0x71; 1024 * 1024];
                for _ in 0..100 {
                    file.write_all(&block).unwrap();
                }
            } else {
                file.write_all(b"disposable reviewed payload").unwrap();
            }
            file.sync_all().unwrap();
        }
        let modified = std::time::SystemTime::now() - Duration::from_secs(8 * 86_400);
        for path in [
            payload,
            artifact.clone(),
            project.join("package.json"),
            project.join("package-lock.json"),
            project,
        ] {
            File::open(path)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(modified))
                .unwrap();
        }
        let root = safety::authorize(&scope, "projects").unwrap();
        let mut found = None;
        scanner::scan(&root, None, &AtomicBool::new(false), |batch| {
            for candidate in batch.candidates {
                if candidate.path == artifact && !candidate.provisional {
                    found = Some(candidate);
                }
            }
        })
        .unwrap();
        let mut candidate = found.expect("The disposable dependency directory was recognized");
        assert!(candidate.blocked_reason.is_none(), "{candidate:?}");
        if large {
            assert!(candidate.suggestion_eligible, "{candidate:?}");
        } else {
            // Small fixtures inject a failure during manifest observation,
            // before the final minimum-size check can authorize any mutation.
            candidate.suggestion_eligible = true;
            candidate.eligible_permanent = true;
        }
        let store = Store::open(&base.join("ledger.sqlite")).unwrap();
        (temp, store, root, candidate)
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct FakeTrashState {
        destination: PathBuf,
        calls: usize,
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    thread_local! {
        static FAKE_TRASH_STATE: RefCell<Option<FakeTrashState>> = const { RefCell::new(None) };
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct FakeTrashGuard;

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl Drop for FakeTrashGuard {
        fn drop(&mut self) {
            FAKE_TRASH_STATE.with(|state| *state.borrow_mut() = None);
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn install_fake_trash(destination: PathBuf) -> FakeTrashGuard {
        FAKE_TRASH_STATE.with(|state| {
            let mut state = state.borrow_mut();
            assert!(
                state.is_none(),
                "A fake Trash destination is already installed"
            );
            *state = Some(FakeTrashState {
                destination,
                calls: 0,
            });
        });
        FakeTrashGuard
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn fake_trash_calls() -> usize {
        FAKE_TRASH_STATE.with(|state| state.borrow().as_ref().map_or(0, |state| state.calls))
    }

    /// Test Trash never invokes AppKit or touches the user's Trash. It only
    /// moves the staged file to a preconfigured sibling inside the temp fixture.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    unsafe extern "C" fn fake_trash(
        input: *const libc::c_char,
        output: *mut libc::c_char,
        output_len: usize,
    ) -> libc::c_int {
        if input.is_null() || output.is_null() {
            return 1;
        }
        let source = PathBuf::from(OsStr::from_bytes(unsafe {
            CStr::from_ptr(input).to_bytes()
        }));
        FAKE_TRASH_STATE.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(state) = slot.as_mut() else {
                return 2;
            };
            state.calls += 1;
            let bytes = state.destination.as_os_str().as_bytes();
            if bytes.len().saturating_add(1) > output_len {
                return 3;
            }
            if std::fs::rename(&source, &state.destination).is_err() {
                return 4;
            }
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), output.cast(), bytes.len());
                *output.add(bytes.len()) = 0;
            }
            0
        })
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct DuplicateCleanupFixture {
        store: Store,
        root: Root,
        copy: Candidate,
        keeper: crate::duplicates::Input,
        fake_trash: PathBuf,
        _temp: tempfile::TempDir,
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn write_old_installer(path: &Path) {
        let mut file = File::create(path).unwrap();
        let block = vec![0x5a; 1024 * 1024];
        for _ in 0..20 {
            file.write_all(&block).unwrap();
        }
        drop(file);
        File::open(path)
            .unwrap()
            .set_times(
                std::fs::FileTimes::new()
                    .set_modified(std::time::SystemTime::now() - Duration::from_secs(16 * 86_400)),
            )
            .unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn duplicate_cleanup_fixture() -> DuplicateCleanupFixture {
        let temp = tempfile::Builder::new()
            .prefix("chippytea-duplicate-cleanup-")
            .tempdir_in("/var/tmp")
            .unwrap();
        // macOS exposes /var through /private/var. Authorize and retain only the
        // canonical path so root identity and later cleanup ancestry agree.
        let base = temp.path().canonicalize().unwrap();
        let downloads = base.join("Downloads");
        std::fs::create_dir(&downloads).unwrap();
        let copy_path = downloads.join("disposable-copy.dmg");
        let keeper_path = downloads.join("retained-keeper.dmg");
        write_old_installer(&copy_path);
        write_old_installer(&keeper_path);
        let root = safety::authorize(&downloads, "downloads").unwrap();
        let mut candidates = std::collections::HashMap::new();
        let stats = scanner::scan(&root, None, &AtomicBool::new(false), |batch| {
            for candidate in batch.candidates {
                if !candidate.provisional
                    && (candidate.path == copy_path || candidate.path == keeper_path)
                {
                    candidates.insert(candidate.path.clone(), candidate);
                }
            }
        })
        .unwrap();
        assert!(stats.complete && stats.errors == 0, "{}", stats.message);
        let copy = candidates
            .remove(&copy_path)
            .expect("The old disposable DMG was indexed");
        let keeper = candidates
            .remove(&keeper_path)
            .expect("The independent old keeper DMG was indexed");
        for candidate in [&copy, &keeper] {
            assert_eq!(candidate.kind, "installer");
            assert!(candidate.suggestion_eligible, "{candidate:?}");
            assert!(candidate.blocked_reason.is_none(), "{candidate:?}");
            assert!(!candidate.eligible_permanent);
            assert_eq!(candidate.file_count, 1);
        }
        assert_ne!(
            (copy.identity.device, copy.identity.inode),
            (keeper.identity.device, keeper.identity.inode),
            "The retained file must be an independent copy"
        );
        let fake_trash = base.join("fake-trash-item.dmg");
        let store = Store::open(&base.join("ledger.sqlite")).unwrap();
        DuplicateCleanupFixture {
            store,
            root: root.clone(),
            copy,
            keeper: crate::duplicates::Input {
                root,
                candidate: keeper,
                keeper_only: false,
            },
            fake_trash,
            _temp: temp,
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn read_prefix(path: &Path) -> [u8; 8] {
        let mut prefix = [0; 8];
        File::open(path).unwrap().read_exact(&mut prefix).unwrap();
        prefix
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn assert_no_cleanup_credit(store: &Store, receipt: &Receipt) {
        assert_eq!((receipt.credited_bytes, receipt.coins), (0, 0));
        let wallet = store.wallet().unwrap();
        assert_eq!(
            (
                wallet.collected_coins,
                wallet.pending_coins,
                wallet.fractional_bytes,
                wallet.credited_bytes,
            ),
            (0, 0, 0, 0)
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn duplicate_guard_restores_copy_when_keeper_changes_after_staging() {
        let mut fixture = duplicate_cleanup_fixture();
        let _trash = install_fake_trash(fixture.fake_trash.clone());
        let keeper_path = fixture.keeper.candidate.path.clone();
        let copy_path = fixture.copy.path.clone();
        let mut changed = false;
        let receipt = execute_with_duplicate_guard(
            &mut fixture.store,
            &fixture.root,
            &fixture.copy,
            "trash",
            Some(fake_trash),
            &AtomicBool::new(false),
            Some(&fixture.keeper),
            |phase, completed, _| {
                if phase == CleanupPhase::Comparing && completed == 0 && !changed {
                    assert!(!copy_path.exists(), "The copy must already be staged");
                    let mut keeper = std::fs::OpenOptions::new()
                        .write(true)
                        .open(&keeper_path)
                        .unwrap();
                    keeper.write_all(b"changed!").unwrap();
                    changed = true;
                }
            },
        )
        .unwrap();
        assert!(changed);
        assert_eq!(receipt.outcome, "skipped", "{}", receipt.detail);
        assert_eq!(read_prefix(&fixture.copy.path), [0x5a; 8]);
        assert_eq!(read_prefix(&keeper_path), *b"changed!");
        assert_eq!(fake_trash_calls(), 0);
        assert!(!fixture.fake_trash.exists());
        assert!(
            !fixture
                .copy
                .path
                .parent()
                .unwrap()
                .join(format!(".chippytea-{}", receipt.id))
                .exists()
        );
        assert_no_cleanup_credit(&fixture.store, &receipt);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn duplicate_guard_restores_copy_when_cancelled_after_staging() {
        let mut fixture = duplicate_cleanup_fixture();
        let _trash = install_fake_trash(fixture.fake_trash.clone());
        let cancel = AtomicBool::new(false);
        let copy_path = fixture.copy.path.clone();
        let mut cancelled_after_stage = false;
        let receipt = execute_with_duplicate_guard(
            &mut fixture.store,
            &fixture.root,
            &fixture.copy,
            "trash",
            Some(fake_trash),
            &cancel,
            Some(&fixture.keeper),
            |phase, completed, _| {
                if phase == CleanupPhase::Comparing && completed == 0 && !cancelled_after_stage {
                    assert!(!copy_path.exists(), "The copy must already be staged");
                    cancel.store(true, Ordering::Relaxed);
                    cancelled_after_stage = true;
                }
            },
        )
        .unwrap();
        assert!(cancelled_after_stage);
        assert_eq!(receipt.outcome, "cancelled", "{}", receipt.detail);
        assert_eq!(read_prefix(&fixture.copy.path), [0x5a; 8]);
        assert_eq!(read_prefix(&fixture.keeper.candidate.path), [0x5a; 8]);
        assert_eq!(fake_trash_calls(), 0);
        assert!(!fixture.fake_trash.exists());
        assert!(
            !fixture
                .copy
                .path
                .parent()
                .unwrap()
                .join(format!(".chippytea-{}", receipt.id))
                .exists()
        );
        assert_no_cleanup_credit(&fixture.store, &receipt);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn duplicate_guard_fake_trash_preserves_the_verified_keeper() {
        let mut fixture = duplicate_cleanup_fixture();
        let _trash = install_fake_trash(fixture.fake_trash.clone());
        let receipt = execute_with_duplicate_guard(
            &mut fixture.store,
            &fixture.root,
            &fixture.copy,
            "trash",
            Some(fake_trash),
            &AtomicBool::new(false),
            Some(&fixture.keeper),
            |_, _, _| {},
        )
        .unwrap();
        assert_eq!(receipt.outcome, "trashed", "{}", receipt.detail);
        assert_eq!(receipt.trash_path.as_deref(), fixture.fake_trash.to_str());
        assert!(receipt.can_restore);
        assert!(!fixture.copy.path.exists());
        assert_eq!(read_prefix(&fixture.fake_trash), [0x5a; 8]);
        assert_eq!(read_prefix(&fixture.keeper.candidate.path), [0x5a; 8]);
        assert_eq!(fake_trash_calls(), 1);
        assert_no_cleanup_credit(&fixture.store, &receipt);
    }

    /// A recognized Python environment holding internal symbolic links, the
    /// shape every venv's bin directory takes.
    fn venv_review_fixture() -> (tempfile::TempDir, Store, Root, Candidate, PathBuf) {
        let temp = tempfile::tempdir().unwrap();
        let base = temp.path().canonicalize().unwrap();
        let scope = base.join("scope");
        let project = scope.join("service");
        let artifact = project.join(".venv");
        std::fs::create_dir_all(artifact.join("bin")).unwrap();
        std::fs::write(
            artifact.join("pyvenv.cfg"),
            b"home = /usr/local/bin\nversion = 3.12.1\n",
        )
        .unwrap();
        let interpreter = project.join("interpreter");
        std::fs::write(&interpreter, b"preserve the linked interpreter").unwrap();
        {
            let mut file = File::create(artifact.join("payload")).unwrap();
            let block = vec![0x2c; 1024 * 1024];
            for _ in 0..100 {
                file.write_all(&block).unwrap();
            }
            file.sync_all().unwrap();
        }
        let modified = std::time::SystemTime::now() - Duration::from_secs(9 * 86_400);
        for path in [
            artifact.join("payload"),
            artifact.join("pyvenv.cfg"),
            artifact.join("bin"),
            artifact.clone(),
            project.clone(),
        ] {
            File::open(path)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(modified))
                .unwrap();
        }
        // Add the internal link after dating regular files (dating follows
        // links), then date the link itself and its refreshed parents.
        let link = artifact.join("bin/python");
        std::os::unix::fs::symlink("../../interpreter", &link).unwrap();
        let encoded = CString::new(link.as_os_str().as_bytes()).unwrap();
        let seconds = modified
            .duration_since(std::time::SystemTime::UNIX_EPOCH)
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
                    encoded.as_ptr(),
                    times.as_ptr(),
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            },
            0
        );
        for path in [artifact.join("bin"), artifact.clone()] {
            File::open(path)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(modified))
                .unwrap();
        }
        let root = safety::authorize(&scope, "projects").unwrap();
        let mut found = None;
        scanner::scan(&root, None, &AtomicBool::new(false), |batch| {
            for candidate in batch.candidates {
                if candidate.path == artifact && !candidate.provisional {
                    found = Some(candidate);
                }
            }
        })
        .unwrap();
        let candidate = found.expect("The disposable environment was recognized");
        assert_eq!(candidate.kind, "venv");
        assert!(candidate.suggestion_eligible, "{candidate:?}");
        assert!(candidate.eligible_permanent);
        let store = Store::open(&base.join("ledger.sqlite")).unwrap();
        (temp, store, root, candidate, interpreter)
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn venv_with_internal_symlink_is_measured_and_permanently_removed() {
        let (_temp, mut store, root, candidate, interpreter) = venv_review_fixture();
        let receipt = execute(
            &mut store,
            &root,
            &candidate,
            "permanent",
            None,
            &AtomicBool::new(false),
        )
        .unwrap();
        assert_eq!(receipt.outcome, "removed", "{}", receipt.detail);
        assert!(!candidate.path.exists());
        assert_eq!(
            std::fs::read(&interpreter).unwrap(),
            b"preserve the linked interpreter",
            "The link's target outside the environment is preserved"
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn manifest_storage_failure_preserves_contents_and_rolls_back_parent_evidence() {
        let (_temp, mut store, root, candidate) = review_fixture(false);
        store.conn.execute_batch(
            "CREATE TABLE cleanup_entries(operation_id TEXT NOT NULL,path BLOB NOT NULL,identity TEXT NOT NULL,PRIMARY KEY(operation_id,path));
             CREATE TRIGGER reject_manifest BEFORE INSERT ON cleanup_entries BEGIN SELECT RAISE(FAIL,'fixture manifest write failed'); END;"
        ).unwrap();
        let receipt = execute(
            &mut store,
            &root,
            &candidate,
            "permanent",
            None,
            &AtomicBool::new(false),
        )
        .unwrap();
        assert_eq!(receipt.outcome, "skipped");
        assert!(receipt.detail.contains("fixture manifest write failed"));
        assert_eq!(
            std::fs::read(candidate.path.join("payload")).unwrap(),
            b"disposable reviewed payload"
        );
        for table in ["cleanup_entries", "operation_parents"] {
            let count: u64 = store
                .conn
                .query_row(&format!("SELECT count(*) FROM {table}"), [], |row| {
                    row.get(0)
                })
                .unwrap();
            assert_eq!(count, 0, "Failed preparation must roll back {table}");
        }
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn cancellation_during_manifest_capture_never_stages_the_artifact() {
        let (_temp, mut store, root, candidate) = review_fixture(false);
        let cancel = AtomicBool::new(false);
        let mut updates = Vec::new();
        let receipt = execute_with_progress(
            &mut store,
            &root,
            &candidate,
            "permanent",
            None,
            &cancel,
            |phase, completed, total| {
                updates.push((phase, completed, total));
                if phase == CleanupPhase::Preparing && completed == 1 {
                    cancel.store(true, Ordering::Relaxed);
                }
            },
        )
        .unwrap();
        assert_eq!(receipt.outcome, "cancelled");
        assert_eq!(
            std::fs::read(candidate.path.join("payload")).unwrap(),
            b"disposable reviewed payload"
        );
        let count: u64 = store
            .conn
            .query_row("SELECT count(*) FROM cleanup_entries", [], |row| row.get(0))
            .unwrap();
        assert_eq!(count, 0);
        assert!(updates.contains(&(CleanupPhase::Preparing, 1, 0)));
        assert!(
            !updates
                .iter()
                .any(|update| update.0 == CleanupPhase::Removing)
        );
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn changed_contents_after_manifest_commit_are_preserved_by_staged_verification() {
        let (_temp, mut store, root, candidate) = review_fixture(true);
        let mut replaced = false;
        let receipt = execute_with_progress(
            &mut store,
            &root,
            &candidate,
            "permanent",
            None,
            &AtomicBool::new(false),
            |phase, completed, total| {
                if phase == CleanupPhase::Preparing && total > 0 && completed == total {
                    std::fs::write(candidate.path.join("payload"), b"new personal replacement")
                        .unwrap();
                    replaced = true;
                }
            },
        )
        .unwrap();
        assert!(replaced);
        assert_eq!(receipt.outcome, "skipped");
        assert!(
            receipt
                .detail
                .contains("Staged contents could not be verified")
        );
        assert_eq!(
            std::fs::read(candidate.path.join("payload")).unwrap(),
            b"new personal replacement"
        );
        assert_eq!(store.wallet().unwrap().credited_bytes, 0);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn completed_cleanup_reports_real_entry_counts_and_preserves_project_sources() {
        let (_temp, mut store, root, candidate) = review_fixture(true);
        let mut updates = Vec::new();
        let receipt = execute_with_progress(
            &mut store,
            &root,
            &candidate,
            "permanent",
            None,
            &AtomicBool::new(false),
            |phase, completed, total| updates.push((phase, completed, total)),
        )
        .unwrap();
        assert_eq!(receipt.outcome, "removed", "{}", receipt.detail);
        assert!(store.conn.is_autocommit());
        assert!(!candidate.path.exists());
        assert!(
            candidate
                .path
                .parent()
                .unwrap()
                .join("package.json")
                .is_file()
        );
        assert_eq!(updates.first(), Some(&(CleanupPhase::Checking, 0, 1)));
        assert!(updates.contains(&(CleanupPhase::Preparing, 2, 2)));
        assert!(updates.contains(&(CleanupPhase::Checking, 2, 2)));
        assert!(updates.contains(&(CleanupPhase::Removing, 2, 2)));
        assert_eq!(updates.last(), Some(&(CleanupPhase::Accounting, 1, 1)));
        assert!(updates.windows(2).all(|pair| pair[0] != pair[1]));
        assert!(
            updates
                .iter()
                .all(|(_, completed, total)| *total == 0 || completed <= total)
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn cancellation_after_removal_releases_manifest_snapshot_and_persists_recovery() {
        let (temp, mut store, root, candidate) = review_fixture(true);
        let cancel = Arc::new(AtomicBool::new(false));
        let signal = Arc::clone(&cancel);
        let _hook = hook(move |phase, _, _| {
            if phase == LeafPhase::AfterUnlink {
                signal.store(true, Ordering::Relaxed);
            }
        });
        let receipt = execute(&mut store, &root, &candidate, "permanent", None, &cancel).unwrap();
        assert_eq!(receipt.outcome, "cancelled", "{}", receipt.detail);
        assert!(store.conn.is_autocommit());
        assert_eq!((receipt.credited_bytes, receipt.coins), (0, 0));
        let stage = candidate
            .path
            .parent()
            .unwrap()
            .join(format!(".chippytea-{}", receipt.id));
        assert!(stage.is_dir());
        assert!(!stage.join("payload").exists());
        assert!(
            candidate
                .path
                .parent()
                .unwrap()
                .join("package.json")
                .is_file()
        );
        drop(store);

        let reopened = Store::open(&temp.path().join("ledger.sqlite")).unwrap();
        let history = reopened.history().unwrap();
        assert_eq!(history.len(), 1);
        assert_eq!(history[0].id, receipt.id);
        assert_eq!(history[0].outcome, "cancelled");
        assert_eq!((history[0].credited_bytes, history[0].coins), (0, 0));
        assert_eq!(reopened.wallet().unwrap().credited_bytes, 0);
        let retained: u64 = reopened
            .conn
            .query_row(
                "SELECT count(*) FROM cleanup_entries WHERE operation_id=?1",
                [&receipt.id],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(
            retained, 2,
            "Recovery evidence must survive a partial removal"
        );
        let open_windows: u64 = reopened
            .conn
            .query_row(
                "SELECT count(*) FROM windows WHERE state='open'",
                [],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(open_windows, 0);
    }

    #[test]
    fn a_leaf_swapped_between_stat_and_capture_is_put_back_without_deletion() {
        let fixture = fixture(false);
        let _hook = hook(|phase, parent, name| {
            if phase == LeafPhase::BeforeCapture {
                rename_exclusive(parent, name, parent, c"saved-reviewed").unwrap();
                write_at(parent, name, b"new personal replacement");
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let reason = remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).unwrap_err();
        assert!(reason.contains("not deleted"), "{reason}");
        assert_eq!(
            std::fs::read(fixture.artifact.join("payload")).unwrap(),
            b"new personal replacement"
        );
        assert_eq!(
            std::fs::read(fixture.artifact.join("saved-reviewed")).unwrap(),
            b"reviewed payload"
        );
        assert_eq!(removed.files, 0);
        assert!(
            std::fs::read_dir(&fixture.recovery.path)
                .unwrap()
                .next()
                .is_none()
        );
    }

    #[test]
    fn a_writer_with_the_old_artifact_fd_cannot_replace_the_unlink_target() {
        let fixture = fixture(false);
        let _hook = hook(|phase, parent, name| {
            if phase == LeafPhase::BeforeUnlink {
                write_at(parent, name, b"new personal replacement");
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        assert!(remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).is_err());
        assert_eq!(
            std::fs::read(fixture.artifact.join("payload")).unwrap(),
            b"new personal replacement"
        );
        assert_eq!(
            removed.files, 1,
            "Only the reviewed, captured file was removed"
        );
        assert!(
            std::fs::read_dir(&fixture.recovery.path)
                .unwrap()
                .next()
                .is_none()
        );
    }

    #[test]
    fn cancellation_preserves_a_relocated_leaf_when_its_original_name_is_occupied() {
        let fixture = fixture(false);
        let cancel = Arc::new(AtomicBool::new(false));
        let signal = Arc::clone(&cancel);
        let _hook = hook(move |phase, parent, name| {
            if phase == LeafPhase::AfterCapture {
                write_at(parent, name, b"new personal replacement");
                signal.store(true, Ordering::Relaxed);
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        let reason = remove_fixture(&fixture, &cancel, &mut removed).unwrap_err();
        assert!(reason.contains("retained"), "{reason}");
        assert_eq!(
            std::fs::read(fixture.artifact.join("payload")).unwrap(),
            b"new personal replacement"
        );
        let name = LeafRecovery::leaf_name("fixture", Path::new("payload"));
        assert_eq!(
            std::fs::read(
                fixture
                    .recovery
                    .path
                    .join(OsStr::from_bytes(name.to_bytes()))
            )
            .unwrap(),
            b"reviewed payload"
        );
        assert_eq!((removed.files, removed.private), (0, 0));
        let recorded: u64 = fixture
            .store
            .conn
            .query_row(
                "SELECT count(*) FROM cleanup_entries WHERE operation_id='fixture'",
                [],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(
            recorded, 2,
            "Original path and identity evidence remains available"
        );
    }

    #[test]
    fn a_symlink_capture_never_deletes_a_replacement_or_follows_the_target() {
        let fixture = fixture(true);
        let _hook = hook(|phase, parent, name| {
            if phase == LeafPhase::BeforeUnlink {
                write_at(parent, name, b"new personal replacement");
            }
        });
        let mut removed = Removed {
            private_known: true,
            ..Default::default()
        };
        assert!(remove_fixture(&fixture, &AtomicBool::new(false), &mut removed).is_err());
        assert_eq!(
            std::fs::read(fixture.artifact.join("payload")).unwrap(),
            b"new personal replacement"
        );
        assert_eq!(
            std::fs::read(fixture.base.join("outside")).unwrap(),
            b"personal outside target"
        );
        assert_eq!((removed.files, removed.private), (0, 0));
    }

    #[test]
    fn recovery_reservation_never_reuses_an_existing_directory() {
        let fixture = fixture(false);
        std::fs::write(fixture.recovery.path.join("keep"), b"preserve me").unwrap();
        assert!(
            LeafRecovery::create(fixture.parent.as_raw_fd(), &fixture.base, "fixture").is_err()
        );
        assert_eq!(
            std::fs::read(fixture.recovery.path.join("keep")).unwrap(),
            b"preserve me"
        );
        assert_eq!(
            stat_file(&fixture.recovery.file).unwrap().st_mode as u32 & 0o777,
            0o700
        );
    }
}
