use std::{
    fs,
    io::{self, Write},
    os::unix::fs::PermissionsExt,
    path::Path,
    sync::{Mutex, MutexGuard, OnceLock},
};

/// Independent test engines share the production process-global helper pool.
/// Keep a test's guard until its engines and disposable fixtures are dropped.
pub(crate) fn engine_guard() -> MutexGuard<'static, ()> {
    static SERIAL: Mutex<()> = Mutex::new(());
    static STAGED: OnceLock<()> = OnceLock::new();
    let guard = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    STAGED.get_or_init(|| stage_helper().expect("Could not stage Cargo's scan helper"));
    guard
}

fn stage_helper() -> io::Result<()> {
    let source = Path::new(env!("CARGO_BIN_EXE_chippytea-scan-helper"));
    let metadata = fs::symlink_metadata(source)?;
    if !metadata.is_file() || metadata.permissions().mode() & 0o111 == 0 {
        return Err(io::Error::other("Cargo helper is not a regular executable"));
    }
    let bytes = fs::read(source)?;
    if bytes.is_empty() {
        return Err(io::Error::other("Cargo helper is empty"));
    }

    // Cargo places integration runners in deps/ and binaries one level above.
    // Stage the real helper beside this runner to use the production resolver,
    // without an environment override or an in-process scanner fallback.
    let executable = std::env::current_exe()?;
    let directory = executable
        .parent()
        .ok_or_else(|| io::Error::other("Test executable has no parent"))?;
    let mut dir_perms = fs::metadata(directory)?.permissions();
    if dir_perms.mode() & 0o022 != 0 {
        dir_perms.set_mode(dir_perms.mode() & !0o022);
        fs::set_permissions(directory, dir_perms)?;
    }
    let destination = directory.join("chippytea-scan-helper");
    let mut temporary = tempfile::NamedTempFile::new_in(directory)?;
    temporary.write_all(&bytes)?;
    temporary
        .as_file()
        .set_permissions(fs::Permissions::from_mode(0o700))?;
    // Atomic persistence replaces the generated helper directory entry, never
    // following a stale destination symlink or exposing a partial executable.
    temporary
        .persist(&destination)
        .map_err(|error| error.error)?;
    if fs::read(destination)? != bytes {
        return Err(io::Error::other(
            "Staged helper differs from Cargo's binary",
        ));
    }
    Ok(())
}
