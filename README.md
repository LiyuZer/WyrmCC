# WyrmCC — A C89 compiler in Rust with an LLVM backend

WyrmCC is a work-in-progress C89 compiler written in Rust. It targets LLVM and
initially bootstraps preprocessing via `clang -E`, then moves to a native
preprocessor. The long-term goal is a correct, tested C89 compiler with a
pleasant developer experience.

- Language: C89
- Implementation: Rust
- Backend: LLVM 18 (via Inkwell planned)
- Host: Ubuntu 24.04 (primary), CI on ubuntu-24.04

## Quick start

Prereqs (Ubuntu 24.04): Rust (rustup), LLVM 18, clang-18, lld-18.

```bash
# Build and run tests
cargo test --workspace

# Preprocess a C file (bootstrap)
cargo run -p wyrmcc -- preprocess path/to/file.c
```

If `clang-18` is not auto-discovered, set:

```bash
export WYRMC_CLANG=/usr/lib/llvm-18/bin/clang-18
```

## Development

- Format: `cargo fmt --all`
- Lint: `cargo clippy --workspace --all-targets -- -D warnings`
- Test: `cargo test --workspace`

Run all via:

```bash
./ci.sh
```

## License

Dual-licensed under either of

- Apache License, Version 2.0 (LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license (LICENSE-MIT or http://opensource.org/licenses/MIT)

at your option.
