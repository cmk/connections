#!/usr/bin/env bash
set -euo pipefail

base_ref="${CI_MERGE_REQUEST_DIFF_BASE_SHA:-${CI_COMMIT_BEFORE_SHA:-}}"
if [[ -z "${base_ref}" || "${base_ref}" =~ ^0+$ ]]; then
    base_ref="HEAD~1"
fi

changed=()
while IFS= read -r path; do
    changed+=("${path}")
done < <(git diff --name-only "${base_ref}"...HEAD)

run_nextest() {
    cargo nextest run --workspace --profile ci "$@"
}

run_family() {
    local feature_args=()
    if [[ "$1" == "--features" ]]; then
        feature_args=(--features "$2")
        shift 2
    fi

    local pattern="$1"
    local test_file test_name
    shopt -s nullglob
    for test_file in tests/${pattern}.rs; do
        test_name="$(basename "${test_file}" .rs)"
        if ((${#feature_args[@]})); then
            run_nextest "${feature_args[@]}" --test "${test_name}"
        else
            run_nextest --test "${test_name}"
        fi
    done
    shopt -u nullglob
}

matches_any() {
    local path pattern
    for path in "${changed[@]}"; do
        for pattern in "$@"; do
            [[ "${path}" == ${pattern} ]] && return 0
        done
    done
    return 1
}

if ((${#changed[@]} == 0)); then
    run_nextest --features fixed,time,hifi,testing,macros
    cargo test --workspace --doc --features fixed,time,hifi,testing,macros
    exit 0
fi

if matches_any \
    Cargo.toml Cargo.lock rust-toolchain.toml .config/nextest.toml .gitlab-ci.yml \
    scripts/ci-select-tests.sh src/lib.rs src/conn.rs src/lattice.rs src/interval.rs \
    src/extended.rs src/float.rs 'src/prop.rs' 'src/prop/*' 'tests/common/*' \
    'tests/compile_fail.rs' 'tests/compile_fail/*'
then
    run_nextest --features fixed,time,hifi,testing,macros
    cargo test --workspace --doc --features fixed,time,hifi,testing,macros
    exit 0
fi

run_nextest --lib --test compile_fail

if matches_any 'src/core.rs' 'src/core/*' 'tests/int_*'; then
    run_family 'int_*'
fi

if matches_any 'src/fixed.rs' 'src/fixed/*' 'tests/fixed_*'; then
    run_nextest --features fixed --lib
    run_family --features fixed 'fixed_*'
fi

if matches_any 'src/time.rs' 'src/time/*'; then
    run_nextest --features time --lib
fi

if matches_any 'src/hifi.rs' 'src/hifi/*'; then
    run_nextest --features hifi --lib
fi

if matches_any 'tests/macros_feature_smoke.rs'; then
    run_nextest --features macros --test macros_feature_smoke
fi

cargo test --workspace --doc
