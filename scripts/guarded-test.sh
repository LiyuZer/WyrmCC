#!/usr/bin/env bash
set -euo pipefail

# Guarded test runner for CI/local use
# - Runs all workspace tests with --nocapture and single-threaded execution
# - Applies a global timeout when `timeout` is available (GNU coreutils)
# - Duration is configurable via TIMEOUT_DURATION (default: 20m)
#
# Usage:
#   ./scripts/guarded-test.sh
#   TIMEOUT_DURATION=30m ./scripts/guarded-test.sh
#   # You can pass extra args that will be forwarded after `--` to the test binary:
#   ./scripts/guarded-test.sh --ignored

DUR="${TIMEOUT_DURATION:-20m}"
TIMEOUT_BIN="$(command -v timeout || true)"

# Collect any extra args to pass after the `--` separator to the test runner
EXTRA_ARGS=("$@")

if [[ -n "${TIMEOUT_BIN}" ]]; then
  # --foreground helps not detach from the controlling terminal in some environments
  exec "${TIMEOUT_BIN}" --foreground "${DUR}" \
    cargo test --workspace -- --nocapture --test-threads=1 "${EXTRA_ARGS[@]}"
else
  echo "warning: 'timeout' not found; running tests without a global timeout" >&2
  exec cargo test --workspace -- --nocapture --test-threads=1 "${EXTRA_ARGS[@]}"
fi
