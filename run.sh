#!/usr/bin/env bash
set -euo pipefail

# Installer for Rust toolchain, LLVM/Clang 18, CMake, Ninja on Ubuntu 24.04
# Idempotent: safe to re-run. Requires sudo.

trap 'echo "[!] Installation failed at line $LINENO" >&2' ERR

step() { echo -e "\n==> $*"; }
has_cmd() { command -v "$1" >/dev/null 2>&1; }
append_once() {
  local line="$1"; local file="$2"
  grep -qxF "$line" "$file" 2>/dev/null || echo "$line" >> "$file"
}

step "Detecting OS and prerequisites"
if ! has_cmd sudo; then
  echo "sudo is required to install packages." >&2
  exit 1
fi

if ! has_cmd apt-get; then
  echo "This script currently supports Debian/Ubuntu with apt-get." >&2
  exit 1
fi

if has_cmd lsb_release; then
  DISTRO=$(lsb_release -is 2>/dev/null || echo "")
  CODENAME=$(lsb_release -cs 2>/dev/null || echo "")
  echo "Detected: ${DISTRO:-unknown} ${CODENAME:-unknown}"
fi

sudo -v
export DEBIAN_FRONTEND=noninteractive

step "Updating apt and installing base tools"
sudo apt-get update -y
sudo apt-get install -y \
  build-essential \
  curl \
  pkg-config \
  libssl-dev \
  cmake \
  ninja-build \
  ca-certificates

step "Installing Rust toolchain (rustup)"
if ! has_cmd rustup; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
else
  echo "rustup already installed"
fi
# Ensure current shell sees cargo
if [ -f "$HOME/.cargo/env" ]; then
  # shellcheck source=/dev/null
  source "$HOME/.cargo/env"
fi

step "Ensuring stable toolchain and components"
rustup toolchain install stable
rustup default stable
rustup component add rust-src rustfmt clippy || true

step "Installing LLVM/Clang 18 and LLD"
sudo apt-get install -y \
  llvm-18 llvm-18-dev llvm-18-tools \
  clang-18 \
  lld-18 \
  libclang-18-dev

step "Configuring environment variables (LLVM_SYS_180_PREFIX and PATH)"
export LLVM_SYS_180_PREFIX=/usr/lib/llvm-18
export PATH=/usr/lib/llvm-18/bin:$PATH

BASHRC="$HOME/.bashrc"
append_once "export LLVM_SYS_180_PREFIX=/usr/lib/llvm-18" "$BASHRC"
append_once "export PATH=/usr/lib/llvm-18/bin:\$PATH" "$BASHRC"

step "Verification"
# Do not abort on missing tools during verification
set +e
# Ensure current shell has env
[ -f "$HOME/.bashrc" ] && . "$HOME/.bashrc"
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"

set -x
uname -srm
echo "LLVM_SYS_180_PREFIX=${LLVM_SYS_180_PREFIX:-<unset>}"
echo -n "PATH has /usr/lib/llvm-18/bin: "; echo "$PATH" | tr ':' '\n' | grep -qx "/usr/lib/llvm-18/bin" && echo yes || echo no
set +x

print_ver() {
  local cmd="$1"
  if command -v "$cmd" >/dev/null 2>&1; then
    echo -n "$cmd: "
    "$cmd" --version 2>&1 | head -n 1
  else
    echo "$cmd: not found"
  fi
}

for c in rustup rustc cargo clang-18 llvm-config-18 lld-18 cmake ninja; do
  print_ver "$c"
done

which clang-18 >/dev/null 2>&1 && echo "clang-18 path: $(which clang-18)" || true
which llvm-config-18 >/dev/null 2>&1 && echo "llvm-config-18 path: $(which llvm-config-18)" || true
which lld-18 >/dev/null 2>&1 && echo "lld-18 path: $(which lld-18)" || true

# Restore strict mode for any future steps
set -e

step "Done"
echo "All requirements installed. New PATH/vars added to ~/.bashrc."
echo "Open a new shell or run: source ~/.bashrc"