//! Same-account process activity with bounded snapshot and identifier storage.
use crate::model::Result;
use crate::safety;
use std::cell::OnceCell;
use std::collections::BTreeSet;
use std::ffi::OsStr;
#[cfg(any(target_os = "macos", test))]
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant};

#[cfg(any(target_os = "macos", test))]
const MAX_ACTIVITY_PROCESSES: usize = 4096;
#[cfg(any(target_os = "macos", test))]
const MAX_EXECUTABLE_PATH_BYTES: usize = 4096;
#[cfg(any(target_os = "macos", test))]
const MAX_APP_BUNDLES: usize = 1024;
#[cfg(any(target_os = "macos", test))]
const MAX_BUNDLE_IDENTIFIER_BYTES: usize = 1024;
#[cfg(any(target_os = "macos", test))]
const BUNDLE_ACTIVITY_LIMIT: &str =
    "Running application ownership exceeded its bounded activity check; cleanup is withheld";

pub(crate) struct ActivitySnapshot {
    pub(crate) working_directories: Vec<PathBuf>,
    pub(crate) executable_paths: Vec<PathBuf>,
    pub(crate) running_app_bundle_ids: OnceCell<Result<BTreeSet<String>>>,
}

impl ActivitySnapshot {
    #[cfg(target_os = "macos")]
    pub(crate) fn capture(cancel: &AtomicBool) -> Result<Self> {
        // Query only this account. Kernel/system services that cannot be inspected
        // are outside the per-user build activity signal, rather than silently
        // treated as known idle processes.
        let mut pids = [0i32; MAX_ACTIVITY_PROCESSES];
        let bytes = unsafe {
            libc::proc_listpids(
                4,
                libc::geteuid(),
                pids.as_mut_ptr().cast(),
                std::mem::size_of_val(&pids) as i32,
            )
        };
        if bytes <= 0 || bytes as usize >= std::mem::size_of_val(&pids) {
            return Err("Running-project activity could not be completely checked".into());
        }
        let mut working_directories = Vec::new();
        let mut executable_paths = Vec::new();
        for pid in pids
            .into_iter()
            .take(bytes as usize / std::mem::size_of::<i32>())
        {
            safety::cancelled(cancel)?;
            if pid <= 0 {
                continue;
            }
            let mut executable = [0u8; MAX_EXECUTABLE_PATH_BYTES];
            let length = unsafe {
                libc::proc_pidpath(pid, executable.as_mut_ptr().cast(), executable.len() as u32)
            };
            if length <= 0 {
                // proc_listpids includes unreaped zombies. Their pid can still
                // satisfy kill(pid, 0), while libproc reports ESRCH because they
                // have no running executable or working directory.
                if std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
                    continue;
                }
                return Err(
                    "A running executable could not be identified; cleanup is withheld".into(),
                );
            }
            let length = executable
                .iter()
                .position(|byte| *byte == 0)
                .ok_or("A running executable path was truncated")?;
            executable_paths.push(PathBuf::from(OsStr::from_bytes(&executable[..length])));
            // The scanner's cwd alone is not development activity, but its
            // executable still must not be removed from a live build directory.
            if pid == std::process::id() as i32 {
                continue;
            }
            let mut info: libc::proc_vnodepathinfo = unsafe { std::mem::zeroed() };
            let read = unsafe {
                libc::proc_pidinfo(
                    pid,
                    libc::PROC_PIDVNODEPATHINFO,
                    0,
                    (&mut info as *mut libc::proc_vnodepathinfo).cast(),
                    std::mem::size_of_val(&info) as i32,
                )
            };
            if read != std::mem::size_of_val(&info) as i32 {
                // A process that exited during enumeration has no ongoing cwd.
                if std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
                    continue;
                }
                return Err(
                    "A running process's project activity is unavailable; cleanup is withheld"
                        .into(),
                );
            }
            let path_storage = &info.pvi_cdir.vip_path;
            let raw = unsafe {
                std::slice::from_raw_parts(
                    path_storage.as_ptr().cast::<u8>(),
                    std::mem::size_of_val(path_storage),
                )
            };
            let length = raw
                .iter()
                .position(|byte| *byte == 0)
                .ok_or("A process working directory was truncated")?;
            if length == 0 {
                return Err("A process working directory could not be identified".into());
            }
            let path = PathBuf::from(OsStr::from_bytes(&raw[..length]));
            if !path.is_absolute() {
                return Err("A process working directory is ambiguous".into());
            }
            working_directories.push(path);
        }
        Ok(Self {
            working_directories,
            executable_paths,
            running_app_bundle_ids: OnceCell::new(),
        })
    }

    #[cfg(target_os = "linux")]
    pub(crate) fn capture(cancel: &AtomicBool) -> Result<Self> {
        let euid = unsafe { libc::geteuid() };
        let proc_dir = std::fs::read_dir("/proc").map_err(|e| format!("Cannot read /proc: {e}"))?;
        let mut working_directories = Vec::new();
        let mut executable_paths = Vec::new();
        let self_pid = std::process::id();

        for entry in proc_dir {
            safety::cancelled(cancel)?;
            let Ok(entry) = entry else { continue };
            let file_name = entry.file_name();
            let Some(name_str) = file_name.to_str() else {
                continue;
            };
            let Ok(pid) = name_str.parse::<u32>() else {
                continue;
            };

            use std::os::unix::fs::MetadataExt;
            let Ok(metadata) = entry.metadata() else {
                continue;
            };
            if metadata.uid() != euid {
                continue;
            }

            let exe_link = format!("/proc/{pid}/exe");
            if let Some(exe) = std::fs::read_link(&exe_link)
                .ok()
                .filter(|p| p.is_absolute())
            {
                executable_paths.push(exe);
            }

            if pid == self_pid {
                continue;
            }

            let cwd_link = format!("/proc/{pid}/cwd");
            if let Some(cwd) = std::fs::read_link(&cwd_link)
                .ok()
                .filter(|p| p.is_absolute())
            {
                working_directories.push(cwd);
            }
        }

        Ok(Self {
            working_directories,
            executable_paths,
            running_app_bundle_ids: OnceCell::new(),
        })
    }

    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    pub(crate) fn capture(_cancel: &AtomicBool) -> Result<Self> {
        Err("Reliable activity checks are supported only on macOS and Linux".into())
    }

    /// Reuse one bounded-age snapshot across nearby gates. A failed capture is
    /// cached too: an unreadable process table stays an exclusion, never
    /// silently retried into apparent idleness within the same window.
    pub(crate) fn capture_with_max_age<'a>(
        cached: &'a mut Option<(Instant, Result<Self>)>,
        max_age: Duration,
        cancel: &AtomicBool,
    ) -> &'a Result<Self> {
        if cached
            .as_ref()
            .is_none_or(|(captured, _)| captured.elapsed() >= max_age)
        {
            *cached = Some((Instant::now(), Self::capture(cancel)));
        }
        &cached.as_ref().unwrap().1
    }

    pub(crate) fn blocked(&self, project: &Path) -> Option<String> {
        self.working_directories.iter().chain(&self.executable_paths).any(|directory| directory.starts_with(project))
            .then(|| "A running process uses this project or one of its compiled applications; close its build, install, server, app, or terminal before cleanup".into())
    }

    pub(crate) fn blocked_for(
        &self,
        kind: &str,
        location: &Path,
        cancel: &AtomicBool,
    ) -> Option<String> {
        // A global managed host can load project output named only in its
        // arguments or open handles while its cwd is elsewhere. We do not
        // inspect those private arguments or infer which project it uses.
        // For the additional review-only ecosystems, known hosts therefore
        // make activity ambiguous even when the path-overlap check is clear.
        if crate::recommendations::review_project_kind(kind)
            && self.executable_paths.iter().any(|path| {
                let Some(name) = path.file_name().and_then(OsStr::to_str) else {
                    return false;
                };
                matches!(
                    (kind, name),
                    ("dotnet", "dotnet")
                        | ("gradle", "java" | "gradle")
                        | (
                            "dart" | "flutter",
                            "dart" | "dartaotruntime" | "flutter_tester"
                        )
                        | ("swiftpm", "swift" | "swift-frontend" | "swift-build")
                        | ("zig", "zig")
                )
            })
        {
            return Some("A runtime or build tool for this ecosystem is running. Its project references cannot be attributed reliably; close it before reviewing this generated data for cleanup".into());
        }
        if kind == "xcode"
            && self.executable_paths.iter().any(|path| {
                path.file_name()
                    .and_then(OsStr::to_str)
                    .is_some_and(|name| {
                        matches!(
                            name,
                            "Xcode"
                                | "xcodebuild"
                                | "XCBBuildService"
                                | "SWBBuildService"
                                | "swift-frontend"
                                | "clang"
                                | "clang++"
                        )
                    })
            })
        {
            return Some("Xcode or a build tool is running; close it before reviewing DerivedData for cleanup".into());
        }
        if let Some(reason) = self.blocked(location) {
            return Some(if kind == "cache" {
                "A running process uses this cache location; close the owning app before cleanup"
                    .into()
            } else {
                reason
            });
        }
        if kind != "cache" {
            return None;
        }
        if let Err(reason) = safety::cancelled(cancel) {
            return Some(reason);
        }
        // Developer-only discovery does not read app metadata. The first cache
        // gate captures identifiers once; even failures remain cached for the
        // same 5s scan / 1s preparation lifetime as the process snapshot.
        let identifiers = self.running_app_bundle_ids.get_or_init(|| {
            #[cfg(target_os = "macos")]
            {
                collect_running_app_bundle_ids(
                    &self.executable_paths,
                    cancel,
                    native::bundle_identifier,
                )
            }
            #[cfg(target_os = "linux")]
            {
                let _ = cancel;
                Ok(BTreeSet::new())
            }
            #[cfg(not(any(target_os = "macos", target_os = "linux")))]
            {
                Err("Reliable activity checks are supported only on macOS and Linux".into())
            }
        });
        match identifiers {
            Err(reason) => Some(reason.clone()),
            Ok(identifiers) => {
                let browser_owner = crate::recommendations::browser_cache_owner(location);
                let final_name = location.file_name().and_then(OsStr::to_str);
                (browser_owner.is_some_and(|owner| identifiers.contains(owner))
                    || final_name.is_some_and(|name| identifiers.contains(name)))
                .then(|| {
                    "The app that owns this cache is running; close it before reviewing cleanup"
                        .into()
                })
            }
        }
    }
}

/// The executable's name is not a bundle. Inspect all enclosing app directories,
/// including the outer app when only one of its nested helpers is running.
/// Sorting and deduplication happen before native reads, once per capture.
#[cfg(any(target_os = "macos", test))]
fn collect_running_app_bundle_ids(
    executable_paths: &[PathBuf],
    cancel: &AtomicBool,
    mut read_identifier: impl FnMut(&Path, &AtomicBool) -> Result<Option<String>>,
) -> Result<BTreeSet<String>> {
    safety::cancelled(cancel)?;
    if executable_paths.len() > MAX_ACTIVITY_PROCESSES {
        return Err(BUNDLE_ACTIVITY_LIMIT.into());
    }
    let mut bundles = BTreeSet::new();
    for executable in executable_paths {
        safety::cancelled(cancel)?;
        if executable.as_os_str().as_bytes().len() > MAX_EXECUTABLE_PATH_BYTES {
            return Err(BUNDLE_ACTIVITY_LIMIT.into());
        }
        if !executable.is_absolute() {
            return Err("A running executable's application location is ambiguous".into());
        }
        for directory in executable.ancestors().skip(1) {
            safety::cancelled(cancel)?;
            if directory
                .extension()
                .is_some_and(|extension| extension.as_bytes().eq_ignore_ascii_case(b"app"))
                && !bundles.contains(directory)
            {
                if bundles.len() >= MAX_APP_BUNDLES {
                    return Err(BUNDLE_ACTIVITY_LIMIT.into());
                }
                bundles.insert(directory.to_path_buf());
            }
        }
    }
    let mut identifiers = BTreeSet::new();
    for bundle in bundles {
        safety::cancelled(cancel)?;
        let identifier = read_identifier(&bundle, cancel)?;
        safety::cancelled(cancel)?;
        if let Some(identifier) = identifier {
            // Keep the exact identifier and case. Missing/malformed metadata
            // leaves ownership unknown; it never proves the app is idle.
            if identifier.len() <= MAX_BUNDLE_IDENTIFIER_BYTES
                && !identifier.is_empty()
                && !matches!(identifier.as_str(), "." | "..")
                && !identifier.bytes().any(|byte| byte == 0 || byte == b'/')
            {
                identifiers.insert(identifier);
            }
        }
    }
    safety::cancelled(cancel)?;
    Ok(identifiers)
}

#[cfg(target_os = "macos")]
mod native {
    use super::*;
    use std::ffi::{CString, c_void};
    use std::fs::File;
    use std::io::Read;
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
    use std::ptr;

    const UTF8: u32 = 0x0800_0100;
    const MAX_INFO_PLIST_BYTES: usize = 256 * 1024;
    const INFO_PLIST_READ_CHUNK: usize = 16 * 1024;
    const METADATA_UNAVAILABLE: &str = "Running application metadata is unavailable";

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct CFRange {
        location: isize,
        length: isize,
    }

    // Signatures match the macOS SDK's CoreFoundation headers:
    // CFIndex is signed long, CFTypeID unsigned long, and Boolean UInt8.
    #[link(name = "CoreFoundation", kind = "framework")]
    unsafe extern "C" {
        fn CFDataCreateWithBytesNoCopy(
            allocator: *const c_void,
            bytes: *const u8,
            length: isize,
            bytes_deallocator: *const c_void,
        ) -> *const c_void;
        static kCFAllocatorNull: *const c_void;
        fn CFPropertyListCreateWithData(
            allocator: *const c_void,
            data: *const c_void,
            options: usize,
            format: *mut isize,
            error: *mut *const c_void,
        ) -> *const c_void;
        static kCFBundleIdentifierKey: *const c_void;
        fn CFDictionaryGetTypeID() -> usize;
        fn CFDictionaryGetValue(dictionary: *const c_void, key: *const c_void) -> *const c_void;
        fn CFGetTypeID(value: *const c_void) -> usize;
        fn CFStringGetTypeID() -> usize;
        fn CFStringGetLength(value: *const c_void) -> isize;
        fn CFStringGetBytes(
            value: *const c_void,
            range: CFRange,
            encoding: u32,
            loss_byte: u8,
            external_representation: u8,
            buffer: *mut u8,
            maximum_bytes: isize,
            used_bytes: *mut isize,
        ) -> isize;
        fn CFRelease(value: *const c_void);
    }

    /// Only non-null, +1 references returned by Create/Copy enter this wrapper.
    struct OwnedCF(*const c_void);

    impl Drop for OwnedCF {
        fn drop(&mut self) {
            unsafe { CFRelease(self.0) };
        }
    }

    pub(super) fn bundle_identifier(bundle: &Path, cancel: &AtomicBool) -> Result<Option<String>> {
        safety::cancelled(cancel)?;
        let plist_bytes = match read_info_plist(bundle, cancel, || {}) {
            Ok(bytes) => bytes,
            Err(reason) if reason == "Cancelled" => return Err(reason),
            // Missing, oversized, redirected, remote/cloud, or changing
            // metadata leaves ownership unknown; caches remain manual review.
            Err(_) => return Ok(None),
        };
        safety::cancelled(cancel)?;
        // The capped Rust buffer outlives CFData and its immutable plist. The
        // null deallocator prevents CoreFoundation from freeing Rust's bytes.
        let data = unsafe {
            CFDataCreateWithBytesNoCopy(
                ptr::null(),
                plist_bytes.as_ptr(),
                plist_bytes.len() as isize,
                kCFAllocatorNull,
            )
        };
        if data.is_null() {
            return Ok(None);
        }
        let data = OwnedCF(data);
        safety::cancelled(cancel)?;
        // Parsing has only bounded in-memory input, never a URL or stream. It
        // cannot enumerate a bundle, hydrate a file, or load an app executable.
        let dictionary = unsafe {
            CFPropertyListCreateWithData(ptr::null(), data.0, 0, ptr::null_mut(), ptr::null_mut())
        };
        if dictionary.is_null() {
            safety::cancelled(cancel)?;
            return Ok(None);
        }
        let dictionary = OwnedCF(dictionary);
        safety::cancelled(cancel)?;
        if unsafe { CFGetTypeID(dictionary.0) != CFDictionaryGetTypeID() } {
            return Ok(None);
        }
        let identifier = unsafe { CFDictionaryGetValue(dictionary.0, kCFBundleIdentifierKey) };
        // The value is borrowed from the owned dictionary, so keep that owner
        // alive until the complete, non-lossy UTF-8 copy has finished.
        if identifier.is_null() || unsafe { CFGetTypeID(identifier) != CFStringGetTypeID() } {
            return Ok(None);
        }
        let length = unsafe { CFStringGetLength(identifier) };
        if length <= 0 {
            return Ok(None);
        }
        if length as usize > MAX_BUNDLE_IDENTIFIER_BYTES {
            return Ok(None);
        }
        let range = CFRange {
            location: 0,
            length,
        };
        let mut needed = 0;
        let converted = unsafe {
            CFStringGetBytes(
                identifier,
                range,
                UTF8,
                0,
                0,
                ptr::null_mut(),
                0,
                &mut needed,
            )
        };
        if converted != length || needed < 0 {
            return Ok(None);
        }
        if needed as usize > MAX_BUNDLE_IDENTIFIER_BYTES {
            return Ok(None);
        }
        let mut bytes = [0u8; MAX_BUNDLE_IDENTIFIER_BYTES];
        let mut used = 0;
        let converted = unsafe {
            CFStringGetBytes(
                identifier,
                range,
                UTF8,
                0,
                0,
                bytes.as_mut_ptr(),
                bytes.len() as isize,
                &mut used,
            )
        };
        safety::cancelled(cancel)?;
        if converted != length || used != needed {
            return Ok(None);
        }
        // CFStringGetBytes does not terminate strings, so embedded NULs cannot
        // truncate an identifier into a different app's cache name.
        Ok(std::str::from_utf8(&bytes[..used as usize])
            .ok()
            .map(str::to_owned))
    }

    /// Read one physical Contents/Info.plist with no directory enumeration.
    /// Every app is processed and released before the next one is inspected.
    fn read_info_plist(
        bundle: &Path,
        cancel: &AtomicBool,
        mut checkpoint: impl FnMut(),
    ) -> Result<Vec<u8>> {
        safety::cancelled(cancel)?;
        let _local_io = safety::LocalOnlyIo::new()?;
        let contents = bundle.join("Contents");
        let (parent, parent_meta) = open_local_contents(&contents, cancel)?;
        let before = info_metadata(parent.as_raw_fd(), cancel)?;
        if !before.is_file()
            || before.is_dataless()
            || before.identity.size == 0
            || before.identity.size > MAX_INFO_PLIST_BYTES as u64
        {
            return Err(METADATA_UNAVAILABLE.into());
        }
        safety::cancelled(cancel)?;
        let raw = unsafe {
            libc::openat(
                parent.as_raw_fd(),
                c"Info.plist".as_ptr(),
                libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
            )
        };
        if raw < 0 {
            return Err(METADATA_UNAVAILABLE.into());
        }
        let fd = unsafe { OwnedFd::from_raw_fd(raw) };
        safety::cancelled(cancel)?;
        if safety::stat_fd(fd.as_raw_fd())? != before {
            return Err(METADATA_UNAVAILABLE.into());
        }
        check_local_volume(fd.as_raw_fd())?;
        let mut file = File::from(fd);
        let mut bytes = vec![0; before.identity.size as usize];
        let mut read = 0;
        while read < bytes.len() {
            safety::cancelled(cancel)?;
            let end = bytes.len().min(read + INFO_PLIST_READ_CHUNK);
            let count = file
                .read(&mut bytes[read..end])
                .map_err(|_| METADATA_UNAVAILABLE)?;
            safety::cancelled(cancel)?;
            if count == 0 {
                return Err(METADATA_UNAVAILABLE.into());
            }
            read += count;
            checkpoint();
        }
        // Detect growth without extending the original bounded allocation.
        safety::cancelled(cancel)?;
        if file.read(&mut [0u8; 1]).map_err(|_| METADATA_UNAVAILABLE)? != 0 {
            return Err(METADATA_UNAVAILABLE.into());
        }
        safety::cancelled(cancel)?;
        if safety::stat_fd(file.as_raw_fd())? != before {
            return Err(METADATA_UNAVAILABLE.into());
        }
        let (current_parent, current_parent_meta) = open_local_contents(&contents, cancel)?;
        safety::cancelled(cancel)?;
        if !safety::same_object(&parent_meta.identity, &current_parent_meta.identity)
            || info_metadata(current_parent.as_raw_fd(), cancel)? != before
        {
            return Err(METADATA_UNAVAILABLE.into());
        }
        Ok(bytes)
    }

    fn info_metadata(parent: RawFd, cancel: &AtomicBool) -> Result<safety::EntryMeta> {
        safety::cancelled(cancel)?;
        let mut stat: libc::stat = unsafe { std::mem::zeroed() };
        let status = unsafe {
            libc::fstatat(
                parent,
                c"Info.plist".as_ptr(),
                &mut stat,
                libc::AT_SYMLINK_NOFOLLOW,
            )
        };
        safety::cancelled(cancel)?;
        if status != 0 {
            return Err(METADATA_UNAVAILABLE.into());
        }
        Ok(safety::EntryMeta::from_stat(&stat))
    }

    fn open_local_contents(
        path: &Path,
        cancel: &AtomicBool,
    ) -> Result<(OwnedFd, safety::EntryMeta)> {
        let names = safety::absolute_components(path)?;
        if names.len() > safety::MAX_DEPTH
            || names.iter().any(|name| safety::is_cloud_component(name))
        {
            return Err(METADATA_UNAVAILABLE.into());
        }
        safety::cancelled(cancel)?;
        let mut directory = safety::open_directory(Path::new("/"))?;
        let mut meta = check_directory(directory.as_raw_fd(), None, cancel)?;
        for name in names {
            safety::cancelled(cancel)?;
            let name = CString::new(name.as_bytes()).map_err(|_| METADATA_UNAVAILABLE)?;
            let raw = unsafe {
                libc::openat(
                    directory.as_raw_fd(),
                    name.as_ptr(),
                    libc::O_RDONLY
                        | libc::O_DIRECTORY
                        | libc::O_NOFOLLOW
                        | libc::O_NONBLOCK
                        | libc::O_CLOEXEC,
                )
            };
            if raw < 0 {
                return Err(METADATA_UNAVAILABLE.into());
            }
            let next = unsafe { OwnedFd::from_raw_fd(raw) };
            meta = check_directory(next.as_raw_fd(), Some(meta.identity.device), cancel)?;
            directory = next;
        }
        Ok((directory, meta))
    }

    fn check_directory(
        fd: RawFd,
        previous_device: Option<u64>,
        cancel: &AtomicBool,
    ) -> Result<safety::EntryMeta> {
        safety::cancelled(cancel)?;
        let meta = safety::stat_fd(fd)?;
        if !meta.is_dir() || meta.is_dataless() {
            return Err(METADATA_UNAVAILABLE.into());
        }
        if previous_device != Some(meta.identity.device) {
            check_local_volume(fd)?;
        }
        safety::cloud_directory_check(fd)?;
        safety::cancelled(cancel)?;
        Ok(meta)
    }

    fn check_local_volume(fd: RawFd) -> Result<()> {
        let mut info: libc::statfs = unsafe { std::mem::zeroed() };
        if unsafe { libc::fstatfs(fd, &mut info) } != 0
            || info.f_flags & libc::MNT_LOCAL as u32 == 0
        {
            return Err(METADATA_UNAVAILABLE.into());
        }
        // Read-only local system volumes are valid metadata sources too. This
        // observation does not grant permission to clean up the application.
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::os::unix::fs::symlink;

        fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf) {
            let temp = tempfile::tempdir().unwrap();
            let base = std::fs::canonicalize(temp.path()).unwrap();
            let bundle = base.join("Fixture.app");
            std::fs::create_dir_all(bundle.join("Contents")).unwrap();
            let plist = bundle.join("Contents/Info.plist");
            (temp, bundle, plist)
        }

        #[test]
        fn plist_reader_rejects_oversized_nonregular_and_redirected_inputs() {
            let (_temp, bundle, plist) = fixture();
            File::create(&plist)
                .unwrap()
                .set_len(MAX_INFO_PLIST_BYTES as u64 + 1)
                .unwrap();
            let cancel = AtomicBool::new(false);
            let result = read_info_plist(&bundle, &cancel, || {
                panic!("Oversized metadata must not be read")
            });
            assert!(result.is_err());
            assert!(bundle_identifier(&bundle, &cancel).unwrap().is_none());
            std::fs::remove_file(&plist).unwrap();
            let real = bundle.join("Contents/Real.plist");
            std::fs::write(&real, b"fixture metadata").unwrap();
            symlink("Real.plist", &plist).unwrap();
            assert!(read_info_plist(&bundle, &cancel, || {}).is_err());
            std::fs::remove_file(&plist).unwrap();
            let pipe = CString::new(plist.as_os_str().as_bytes()).unwrap();
            assert_eq!(unsafe { libc::mkfifo(pipe.as_ptr(), 0o600) }, 0);
            assert!(read_info_plist(&bundle, &cancel, || {}).is_err());
            std::fs::remove_file(&plist).unwrap();
            std::fs::write(&plist, b"fixture metadata").unwrap();
            std::fs::rename(bundle.join("Contents"), bundle.join("Redirected")).unwrap();
            symlink("Redirected", bundle.join("Contents")).unwrap();
            assert!(read_info_plist(&bundle, &cancel, || {}).is_err());
            assert_eq!(
                std::fs::read(bundle.join("Redirected/Info.plist")).unwrap(),
                b"fixture metadata"
            );
        }

        #[test]
        fn plist_reader_rejects_changed_metadata_and_checks_chunk_cancellation() {
            let (_temp, bundle, plist) = fixture();
            let bytes = vec![b'a'; INFO_PLIST_READ_CHUNK * 2];
            std::fs::write(&plist, &bytes).unwrap();
            let mut changed = false;
            let result = read_info_plist(&bundle, &AtomicBool::new(false), || {
                if !changed {
                    changed = true;
                    std::fs::write(&plist, vec![b'b'; bytes.len()]).unwrap();
                }
            });
            assert!(changed);
            assert!(result.is_err());
            std::fs::write(&plist, &bytes).unwrap();
            let mut replaced = false;
            let result = read_info_plist(&bundle, &AtomicBool::new(false), || {
                if !replaced {
                    replaced = true;
                    std::fs::rename(&plist, plist.with_file_name("Original.plist")).unwrap();
                    std::fs::write(&plist, &bytes).unwrap();
                }
            });
            assert!(replaced);
            assert!(result.is_err());
            let cancel = AtomicBool::new(false);
            let result = read_info_plist(&bundle, &cancel, || {
                cancel.store(true, std::sync::atomic::Ordering::Relaxed);
            });
            assert_eq!(result.unwrap_err(), "Cancelled");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn snapshot(identifiers: &[&str]) -> ActivitySnapshot {
        ActivitySnapshot {
            working_directories: Vec::new(),
            executable_paths: Vec::new(),
            running_app_bundle_ids: OnceCell::from(Ok(identifiers
                .iter()
                .map(|id| (*id).into())
                .collect())),
        }
    }

    #[test]
    fn review_ecosystems_withhold_cleanup_for_external_managed_hosts() {
        let project = Path::new("/Projects/Example");
        let cancel = AtomicBool::new(false);
        for (kind, host) in [
            ("dotnet", "dotnet"),
            ("gradle", "java"),
            ("gradle", "gradle"),
            ("dart", "dart"),
            ("dart", "dartaotruntime"),
            ("flutter", "dart"),
            ("flutter", "flutter_tester"),
            ("swiftpm", "swift"),
            ("swiftpm", "swift-frontend"),
            ("swiftpm", "swift-build"),
            ("zig", "zig"),
        ] {
            let mut activity = ActivitySnapshot {
                working_directories: vec![PathBuf::from("/Unrelated")],
                executable_paths: vec![Path::new("/Global/SDK").join(host)],
                running_app_bundle_ids: OnceCell::new(),
            };
            assert!(activity.blocked(project).is_none());
            assert!(
                activity.blocked_for(kind, project, &cancel).is_some(),
                "{kind} cannot attribute the external {host} runtime to an idle project"
            );
            assert!(activity.running_app_bundle_ids.get().is_none());
            // This conservative ambiguity policy does not change the existing
            // developer categories or declare all unrelated hosts active.
            assert!(activity.blocked_for("cargo", project, &cancel).is_none());
            activity.executable_paths.clear();
            assert!(activity.blocked_for(kind, project, &cancel).is_none());
        }
    }

    #[test]
    fn cache_activity_matches_only_the_exact_final_bundle_identifier() {
        let snapshot = snapshot(&["com.example.Editor"]);
        let cancel = AtomicBool::new(false);
        assert!(
            snapshot
                .blocked_for(
                    "cache",
                    Path::new("/Users/fixture/Library/Caches/com.example.Editor"),
                    &cancel,
                )
                .is_some()
        );
        for name in [
            "com.example",
            "com.example.Editor.extra",
            "prefix.com.example.Editor",
            "com.example.editor",
            "com.example.Editor/child",
        ] {
            assert!(
                snapshot
                    .blocked_for(
                        "cache",
                        &Path::new("/Users/fixture/Library/Caches").join(name),
                        &cancel,
                    )
                    .is_none(),
                "Non-exact cache names must not imply ownership: {name}"
            );
        }
        assert!(
            snapshot
                .blocked_for(
                    "logs",
                    Path::new("/Users/fixture/Library/Logs/com.example.Editor"),
                    &cancel,
                )
                .is_none()
        );
    }

    #[test]
    fn browser_cache_activity_uses_browser_bundle_owner_and_exact_paths() {
        let cancel = AtomicBool::new(false);
        for (path, owner, unrelated) in [
            (
                "/Users/fixture/Library/Caches/Google/Chrome/Default",
                "com.google.Chrome",
                "org.chromium.Chromium",
            ),
            (
                "/Users/fixture/Library/Caches/Chromium/Profile 1",
                "org.chromium.Chromium",
                "com.google.Chrome",
            ),
        ] {
            let active = snapshot(&[owner]);
            assert!(
                active
                    .blocked_for("cache", Path::new(path), &cancel)
                    .is_some(),
                "{path} must be blocked while its browser is running"
            );
            let other = snapshot(&[unrelated]);
            assert!(
                other
                    .blocked_for("cache", Path::new(path), &cancel)
                    .is_none(),
                "{path} must not be blocked by an unrelated browser"
            );
        }
        let snapshot = snapshot(&["com.google.Chrome"]);
        assert!(
            snapshot
                .blocked_for(
                    "cache",
                    Path::new("/Users/fixture/Library/Caches/Google/Chrome/Default/Cache"),
                    &cancel,
                )
                .is_none(),
            "Only the validated profile root is an owner-matching location"
        );
    }

    #[test]
    fn cache_activity_still_checks_working_directories_and_executable_paths() {
        let mut snapshot = snapshot(&[]);
        let cancel = AtomicBool::new(false);
        snapshot.working_directories = vec![PathBuf::from("/cache/terminal/nested")];
        snapshot.executable_paths = vec![PathBuf::from("/cache/worker/bin/process")];
        for path in ["/cache/terminal", "/cache/worker"] {
            assert!(
                snapshot
                    .blocked_for("cache", Path::new(path), &cancel)
                    .is_some()
            );
        }
        assert!(
            snapshot
                .blocked_for("cache", Path::new("/cache/terminal-sibling"), &cancel)
                .is_none()
        );
    }

    #[test]
    fn xcode_build_tool_exclusion_is_preserved() {
        let mut snapshot = snapshot(&[]);
        let cancel = AtomicBool::new(false);
        snapshot.executable_paths = vec![PathBuf::from("/toolchain/bin/clang")];
        assert!(
            snapshot
                .blocked_for(
                    "xcode",
                    Path::new("/Users/fixture/Library/Developer/Xcode/DerivedData"),
                    &cancel,
                )
                .is_some()
        );
        assert!(
            snapshot
                .blocked_for("cache", Path::new("/cache/unknown"), &cancel)
                .is_none()
        );
    }

    #[test]
    fn developer_and_already_active_cache_gates_do_not_read_owner_metadata() {
        let snapshot = ActivitySnapshot {
            working_directories: Vec::new(),
            executable_paths: vec![PathBuf::from(
                "/Applications/Fixture.app/Contents/MacOS/app",
            )],
            running_app_bundle_ids: OnceCell::new(),
        };
        let cancel = AtomicBool::new(false);
        assert!(
            snapshot
                .blocked_for("cargo", Path::new("/projects/fixture"), &cancel)
                .is_none()
        );
        assert!(snapshot.running_app_bundle_ids.get().is_none());
        assert!(
            snapshot
                .blocked_for("cache", Path::new("/Applications/Fixture.app"), &cancel)
                .is_some()
        );
        assert!(snapshot.running_app_bundle_ids.get().is_none());
    }

    #[test]
    fn running_bundle_collection_is_deduplicated_and_includes_outer_apps() {
        let outer = PathBuf::from("/Applications/Editor.app");
        let helper = outer.join("Contents/Frameworks/Helper.app");
        let executable = helper.join("Contents/MacOS/helper");
        let executables = vec![
            executable.clone(),
            outer.join("Contents/MacOS/editor"),
            executable,
        ];
        let mut reads = Vec::new();
        let identifiers =
            collect_running_app_bundle_ids(&executables, &AtomicBool::new(false), |path, _| {
                reads.push(path.to_path_buf());
                Ok(Some(if path == outer {
                    "com.example.Editor".into()
                } else {
                    "com.example.Editor.Helper".into()
                }))
            })
            .unwrap();
        assert_eq!(reads, vec![outer, helper]);
        assert_eq!(
            identifiers,
            BTreeSet::from([
                "com.example.Editor".into(),
                "com.example.Editor.Helper".into()
            ])
        );
    }

    #[test]
    fn executable_names_and_partial_app_extensions_do_not_supply_owners() {
        let executables = [
            PathBuf::from("/tools/executable.app"),
            PathBuf::from("/Applications/Editor.app.backup/Contents/MacOS/editor"),
            PathBuf::from("/usr/local/bin/compiler"),
        ];
        let identifiers =
            collect_running_app_bundle_ids(&executables, &AtomicBool::new(false), |_, _| {
                panic!("No enclosing app bundle exists")
            })
            .unwrap();
        assert!(identifiers.is_empty());
    }

    #[test]
    fn bundle_collection_cancellation_and_limits_fail_closed() {
        let cancelled = collect_running_app_bundle_ids(&[], &AtomicBool::new(true), |_, _| {
            panic!("A cancelled capture must not read bundle metadata")
        });
        assert_eq!(cancelled.unwrap_err(), "Cancelled");
        let cancel = AtomicBool::new(false);
        let interrupted = collect_running_app_bundle_ids(
            &[PathBuf::from(
                "/Applications/Fixture.app/Contents/MacOS/app",
            )],
            &cancel,
            |_, cancel| {
                cancel.store(true, std::sync::atomic::Ordering::Relaxed);
                Ok(Some("com.example.Fixture".into()))
            },
        );
        assert_eq!(interrupted.unwrap_err(), "Cancelled");
        let executables: Vec<_> = (0..=MAX_APP_BUNDLES)
            .map(|index| {
                PathBuf::from(format!(
                    "/Applications/Fixture{index}.app/Contents/MacOS/app"
                ))
            })
            .collect();
        let limited =
            collect_running_app_bundle_ids(&executables, &AtomicBool::new(false), |_, _| {
                panic!("Collect and bound distinct bundles before native metadata reads")
            });
        assert_eq!(limited.unwrap_err(), BUNDLE_ACTIVITY_LIMIT);
        let long_path = PathBuf::from(format!(
            "/{}.app/process",
            "x".repeat(MAX_EXECUTABLE_PATH_BYTES)
        ));
        let limited =
            collect_running_app_bundle_ids(&[long_path], &AtomicBool::new(false), |_, _| {
                panic!("Overlong process paths must be excluded")
            });
        assert_eq!(limited.unwrap_err(), BUNDLE_ACTIVITY_LIMIT);
        let unknown = collect_running_app_bundle_ids(
            &[PathBuf::from(
                "/Applications/Fixture.app/Contents/MacOS/app",
            )],
            &AtomicBool::new(false),
            |_, _| Ok(Some("x".repeat(MAX_BUNDLE_IDENTIFIER_BYTES + 1))),
        );
        assert!(unknown.unwrap().is_empty());
    }

    #[test]
    fn malformed_identifiers_never_become_partial_cache_owner_matches() {
        for identifier in [
            "",
            ".",
            "..",
            "com.example.Editor\0.extra",
            "com.example/Editor",
        ] {
            let identifiers = collect_running_app_bundle_ids(
                &[PathBuf::from(
                    "/Applications/Fixture.app/Contents/MacOS/app",
                )],
                &AtomicBool::new(false),
                |_, _| Ok(Some(identifier.into())),
            )
            .unwrap();
            assert!(identifiers.is_empty());
        }
    }

    #[test]
    fn failed_activity_capture_remains_cached_without_retrying_processes() {
        let mut cached = Some((
            Instant::now(),
            Err("Fixture activity is unavailable".into()),
        ));
        let result = ActivitySnapshot::capture_with_max_age(
            &mut cached,
            Duration::from_secs(60),
            &AtomicBool::new(false),
        );
        assert_eq!(
            result.as_ref().err().unwrap(),
            "Fixture activity is unavailable"
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn native_bundle_fixture_reads_nested_owners_and_fresh_metadata() {
        fn write_info(bundle: &Path, identifier_value: &str) {
            std::fs::create_dir_all(bundle.join("Contents/MacOS")).unwrap();
            std::fs::write(
                bundle.join("Contents/Info.plist"),
                format!(
                    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
                     <plist version=\"1.0\"><dict>\
                     <key>CFBundlePackageType</key><string>APPL</string>\
                     <key>CFBundleIdentifier</key>{identifier_value}\
                     </dict></plist>"
                ),
            )
            .unwrap();
        }

        let temp = tempfile::tempdir().unwrap();
        let outer = std::fs::canonicalize(temp.path())
            .unwrap()
            .join("Fixture.app");
        let helper = outer.join("Contents/Frameworks/Helper.app");
        write_info(&outer, "<string>com.example.Fixture</string>");
        write_info(&helper, "<string>com.example.Fixture.Helper</string>");
        // These paths describe disposable fixtures only. No executable is
        // created or launched, and the test never queries the host process list.
        let executable = helper.join("Contents/MacOS/fixture");
        let capture = || {
            collect_running_app_bundle_ids(
                std::slice::from_ref(&executable),
                &AtomicBool::new(false),
                native::bundle_identifier,
            )
            .unwrap()
        };
        assert_eq!(
            capture(),
            BTreeSet::from([
                "com.example.Fixture".into(),
                "com.example.Fixture.Helper".into(),
            ])
        );
        let activity = ActivitySnapshot {
            working_directories: Vec::new(),
            executable_paths: vec![executable.clone()],
            running_app_bundle_ids: OnceCell::new(),
        };
        let cache = outer.parent().unwrap().join("Caches/com.example.Fixture");
        assert!(activity.running_app_bundle_ids.get().is_none());
        assert!(
            activity
                .blocked_for("cache", &cache, &AtomicBool::new(false))
                .is_some()
        );
        write_info(&outer, "<string>com.example.RevisedFixture</string>");
        // Repeated cache gates reuse this snapshot instead of reopening plists.
        assert!(
            activity
                .blocked_for("cache", &cache, &AtomicBool::new(false))
                .is_some()
        );
        let refreshed = capture();
        assert!(refreshed.contains("com.example.RevisedFixture"));
        assert!(!refreshed.contains("com.example.Fixture"));
        write_info(&outer, "<integer>123</integer>");
        assert_eq!(
            capture(),
            BTreeSet::from(["com.example.Fixture.Helper".into()])
        );
        std::fs::remove_file(outer.join("Contents/Info.plist")).unwrap();
        assert_eq!(
            capture(),
            BTreeSet::from(["com.example.Fixture.Helper".into()])
        );
        let at_capacity = "a".repeat(MAX_BUNDLE_IDENTIFIER_BYTES);
        write_info(&outer, &format!("<string>{at_capacity}</string>"));
        assert!(capture().contains(&at_capacity));
        // This fits the UTF-16 unit cap but not the UTF-8 byte cap. It remains
        // unknown metadata instead of becoming a truncated cache identifier.
        let oversized_multibyte = "é".repeat(MAX_BUNDLE_IDENTIFIER_BYTES / 2 + 1);
        write_info(&outer, &format!("<string>{oversized_multibyte}</string>"));
        assert_eq!(
            capture(),
            BTreeSet::from(["com.example.Fixture.Helper".into()])
        );
        std::fs::write(
            outer.join("Contents/Info.plist"),
            b"<plist version=\"1.0\"><array><string>com.example.NotADictionary</string></array></plist>",
        ).unwrap();
        assert_eq!(
            capture(),
            BTreeSet::from(["com.example.Fixture.Helper".into()])
        );
    }
}
