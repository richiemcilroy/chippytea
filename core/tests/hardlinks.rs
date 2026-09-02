#![cfg(any(target_os = "macos", target_os = "linux"))]
#![allow(clippy::useless_conversion, clippy::unnecessary_cast)]

use chippytea_core::{Engine, model::*};
use serde_json::json;
use std::{
    fs::{self, File, FileTimes},
    io::{Read, Write},
    os::unix::fs::MetadataExt,
    path::PathBuf,
    sync::Arc,
    time::{Duration, Instant, SystemTime},
};

mod support;

struct Fixture {
    engine: Arc<Engine>,
    database: PathBuf,
    artifact: PathBuf,
    payload: PathBuf,
    alias: PathBuf,
    sibling: PathBuf,
    outside: PathBuf,
    allocated: u64,
    _temporary: tempfile::TempDir,
}

fn settled(engine: &Arc<Engine>) -> Snapshot {
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        let snapshot = engine.snapshot().unwrap();
        if !snapshot.scanning && Arc::strong_count(engine) == 1 {
            return snapshot;
        }
        assert!(
            Instant::now() < deadline,
            "Disposable discovery did not settle"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn fixture() -> Fixture {
    let temporary = tempfile::tempdir().unwrap();
    let base = temporary.path().canonicalize().unwrap();
    let path = std::ffi::CString::new(base.as_os_str().as_encoded_bytes()).unwrap();
    let mut capacity: libc::statvfs = unsafe { std::mem::zeroed() };
    assert_eq!(unsafe { libc::statvfs(path.as_ptr(), &mut capacity) }, 0);
    assert!(
        u64::from(capacity.f_bavail).saturating_mul(capacity.f_frsize)
            > 3 * 1024 * 1024 * 1024 + 110_000_000
    );
    let projects = base.join("Projects");
    let project = projects.join("disposable");
    let artifact = project.join("target");
    fs::create_dir_all(artifact.join("a")).unwrap();
    fs::create_dir(artifact.join("b")).unwrap();
    let manifest = project.join("Cargo.toml");
    fs::write(
        &manifest,
        "[package]\nname=\"disposable\"\nversion=\"0.1.0\"\n",
    )
    .unwrap();
    let marker = artifact.join("CACHEDIR.TAG");
    fs::write(&marker, "Signature: 8a477f597d28d172789f06886806bc55\n").unwrap();
    let sibling = project.join("source.rs");
    fs::write(&sibling, "Preserve the project's source.").unwrap();
    let payload = artifact.join("a/output");
    let alias = artifact.join("b/output");
    let mut file = File::create(&payload).unwrap();
    let block = vec![0x5a; 1024 * 1024];
    for _ in 0..100 {
        file.write_all(&block).unwrap();
    }
    file.sync_all().unwrap();
    drop(file);
    fs::hard_link(&payload, &alias).unwrap();
    let old = SystemTime::now() - Duration::from_secs(9 * 86_400);
    for path in [
        &payload,
        &manifest,
        &marker,
        &artifact.join("a"),
        &artifact.join("b"),
        &artifact,
        &project,
        &projects,
    ] {
        File::open(path)
            .unwrap()
            .set_times(FileTimes::new().set_modified(old))
            .unwrap();
    }
    let allocated =
        (fs::metadata(&payload).unwrap().blocks() + fs::metadata(&marker).unwrap().blocks()) * 512;
    let database = base.join("library.sqlite");
    let engine = Engine::open(&database, None).unwrap();
    engine
        .request(json!({"action":"authorize","path":projects,"kind":"projects"}))
        .unwrap();
    engine.request(json!({"action":"scan"})).unwrap();
    assert!(settled(&engine).stats.complete);
    Fixture {
        engine,
        database,
        artifact,
        payload,
        alias,
        sibling,
        outside: base.join("outside-output"),
        allocated,
        _temporary: temporary,
    }
}

fn review(fixture: &Fixture) -> (Candidate, String) {
    let snapshot = fixture.engine.snapshot().unwrap();
    assert_eq!(snapshot.candidates.len(), 1);
    let candidate = snapshot.candidates[0].clone();
    assert_eq!(candidate.kind, "cargo");
    assert_eq!(
        candidate.file_count, 3,
        "File counts retain both alias names"
    );
    assert_eq!(
        candidate.allocated_bytes, fixture.allocated,
        "Allocation counts the linked inode once"
    );
    assert!(candidate.suggestion_eligible && candidate.eligible_permanent);
    let review = fixture
        .engine
        .request(json!({
            "action":"prepare","operation":"permanent","items":[candidate]
        }))
        .unwrap();
    (candidate, review["token"].as_str().unwrap().to_owned())
}

fn digest(path: &std::path::Path) -> blake3::Hash {
    let mut file = File::open(path).unwrap();
    let mut hash = blake3::Hasher::new();
    let mut buffer = [0; 64 * 1024];
    loop {
        let count = file.read(&mut buffer).unwrap();
        if count == 0 {
            return hash.finalize();
        }
        hash.update(&buffer[..count]);
    }
}

#[test]
fn internal_cargo_links_are_reviewable_and_cleanup_cannot_reward_them_twice() {
    let _engine_guard = support::engine_guard();
    let fixture = fixture();
    let (_, token) = review(&fixture);
    assert!(
        fixture
            .engine
            .request(json!({"action":"execute","token":token,"confirmed":false}))
            .is_err()
    );
    assert_eq!(fs::metadata(&fixture.payload).unwrap().nlink(), 2);
    let receipts: Vec<Receipt> = serde_json::from_value(
        fixture
            .engine
            .request(json!({
                "action":"execute","token":token,"confirmed":true
            }))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(receipts.len(), 1);
    let receipt = &receipts[0];
    assert_eq!(receipt.outcome, "removed", "{}", receipt.detail);
    assert!(!fixture.artifact.exists());
    assert_eq!(
        fs::read_to_string(&fixture.sibling).unwrap(),
        "Preserve the project's source."
    );
    assert_eq!(receipt.reported_bytes, fixture.allocated);
    assert!(
        receipt.credited_bytes <= fixture.allocated
            && receipt.credited_bytes <= receipt.observed_bytes
    );
    assert_eq!(receipt.coins, receipt.credited_bytes / COIN_BYTES);
    let saved = settled(&fixture.engine);
    assert_eq!(saved.wallet.credited_bytes, receipt.credited_bytes);
    assert_eq!(saved.history.len(), 1);
    assert!(
        fixture
            .engine
            .request(json!({"action":"execute","token":token,"confirmed":true}))
            .is_err()
    );
    fixture.engine.request(json!({"action":"collect"})).unwrap();
    let wallet = serde_json::to_value(fixture.engine.snapshot().unwrap().wallet).unwrap();
    fixture.engine.request(json!({"action":"collect"})).unwrap();
    assert_eq!(
        serde_json::to_value(fixture.engine.snapshot().unwrap().wallet).unwrap(),
        wallet
    );
    let database = fixture.database.clone();
    drop(fixture.engine);
    let reopened = Engine::open(&database, None).unwrap();
    assert_eq!(
        serde_json::to_value(reopened.snapshot().unwrap().wallet).unwrap(),
        wallet
    );
    assert_eq!(reopened.snapshot().unwrap().history.len(), 1);
    assert!(
        reopened
            .request(json!({"action":"execute","token":token,"confirmed":true}))
            .is_err()
    );
    drop(reopened);
}

#[test]
fn an_external_alias_created_after_review_preserves_every_name_and_earns_nothing() {
    let _engine_guard = support::engine_guard();
    let fixture = fixture();
    let (_, token) = review(&fixture);
    let before = digest(&fixture.payload);
    fs::hard_link(&fixture.payload, &fixture.outside).unwrap();
    let receipts: Vec<Receipt> = serde_json::from_value(
        fixture
            .engine
            .request(json!({
                "action":"execute","token":token,"confirmed":true
            }))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(receipts[0].outcome, "skipped", "{}", receipts[0].detail);
    assert_eq!(receipts[0].credited_bytes, 0);
    assert_eq!(receipts[0].coins, 0);
    for path in [&fixture.payload, &fixture.alias, &fixture.outside] {
        assert_eq!(fs::metadata(path).unwrap().nlink(), 3);
        assert_eq!(digest(path), before);
    }
    let snapshot = settled(&fixture.engine);
    assert!(snapshot.candidates.is_empty());
    assert_eq!(snapshot.wallet.credited_bytes, 0);
    assert_eq!(snapshot.wallet.pending_coins, 0);
}
