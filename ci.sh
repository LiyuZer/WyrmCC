#!/usr/bin/env bash
set -euo pipefail
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env" || true
export LLVM_SYS_180_PREFIX=${LLVM_SYS_180_PREFIX:-/usr/lib/llvm-18}
export PATH="/usr/lib/llvm-18/bin:${PATH}"

cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
WYRMC_CLANG=${WYRMC_CLANG:-/usr/lib/llvm-18/bin/clang-18} cargo test --workspace
