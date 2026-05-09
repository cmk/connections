//! Integration test for `scripts/check_no_ext_ext_conn.sh`.
//!
//! Drives the guardrail in a throwaway git repo so the test can stage
//! fixtures without touching the real repo's index. Verifies the
//! three behaviors required by `plan-2026-05-08-04` §Verification:
//!
//! - `clean_tree`: exits 0 when no Ext-Ext shapes are staged.
//! - `blocks_violation`: exits 1 when an Ext-Ext shape is staged.
//! - `allow_pragma`: exits 0 when the violation is preceded by
//!   `// allow(ext-ext-conn): <reason>`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is always set when a test is run by cargo and
    // points at the crate root containing Cargo.toml.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn script_path() -> PathBuf {
    repo_root().join("scripts/check_no_ext_ext_conn.sh")
}

/// Build a fresh scratch git repo with a staged file. Returns the
/// scratch dir; caller cleans it up.
fn scratch_with_file(filename: &str, contents: &str) -> tempfile::TempDir {
    let scratch = tempfile::tempdir().expect("tempdir");
    let scratch_path = scratch.path();

    sh(scratch_path, &["git", "init", "--quiet"]);
    sh(scratch_path, &["git", "config", "user.email", "test@local"]);
    sh(scratch_path, &["git", "config", "user.name", "test"]);

    fs::create_dir_all(scratch_path.join("src")).unwrap();
    fs::create_dir_all(scratch_path.join("scripts")).unwrap();

    let dst_script = scratch_path.join("scripts/check_no_ext_ext_conn.sh");
    fs::copy(script_path(), &dst_script).expect("copy script");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&dst_script).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&dst_script, perms).unwrap();
    }

    let target = scratch_path.join("src").join(filename);
    fs::write(&target, contents).expect("write fixture");

    sh(scratch_path, &["git", "add", "--all"]);
    scratch
}

fn run_guardrail(scratch: &Path) -> std::process::Output {
    let mut cmd = Command::new("bash");
    cmd.arg("scripts/check_no_ext_ext_conn.sh")
        .current_dir(scratch);
    scrub_git_env(&mut cmd);
    cmd.output().expect("run guardrail")
}

fn sh(cwd: &Path, args: &[&str]) {
    let mut cmd = Command::new(args[0]);
    cmd.args(&args[1..]).current_dir(cwd);
    scrub_git_env(&mut cmd);
    let status = cmd.status().expect("spawn");
    assert!(status.success(), "command failed: {:?}", args);
}

/// Drop `GIT_*` env vars that git's pre-commit / pre-push hooks
/// export to child processes. Without this, `cargo test` invoked
/// from a hook inherits `GIT_DIR` pointing at the host repo, and
/// `git init` in the scratch dir would then operate on the host
/// repo's config (failing under cross-test parallelism with a
/// "config file lock" error).
fn scrub_git_env(cmd: &mut Command) {
    for var in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_PREFIX",
        "GIT_OBJECT_DIRECTORY",
    ] {
        cmd.env_remove(var);
    }
}

#[test]
fn clean_tree_exits_zero() {
    let scratch = scratch_with_file("clean.rs", "pub fn ok() {}\n");
    let out = run_guardrail(scratch.path());
    assert!(
        out.status.success(),
        "expected exit 0 on clean tree; stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn blocks_violation() {
    let scratch = scratch_with_file(
        "bad.rs",
        // allow(ext-ext-conn): fixture text, not a real Conn decl
        "crate::conn_l! {\n    pub BAD : Extended<u32> => Extended<u64> {\n        ceil:  bad_ceil,\n        inner: bad_inner,\n    }\n}\n",
    );
    let out = run_guardrail(scratch.path());
    assert!(
        !out.status.success(),
        "expected non-zero exit on Ext-Ext violation"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("antipattern"),
        "expected 'antipattern' in stderr; got: {}",
        stderr
    );
}

#[test]
fn allow_pragma_suppresses() {
    let scratch = scratch_with_file(
        "allowed.rs",
        // allow(ext-ext-conn): fixture text, not a real Conn decl
        "crate::conn_l! {\n    // allow(ext-ext-conn): integration-test fixture\n    pub ALLOWED : Extended<u32> => Extended<u64> {\n        ceil:  fake_ceil,\n        inner: fake_inner,\n    }\n}\n",
    );
    let out = run_guardrail(scratch.path());
    assert!(
        out.status.success(),
        "expected exit 0 with allow pragma; stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}
