# Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers

## 📄 Table of Contents
<!-- TOC -->
* [Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers](#improving-sha-2-collisions-using-satisfiability-modulo-theory-smt-solvers)
  * [📄 Table of Contents](#-table-of-contents)
  * [🔨 Building](#-building)
  * [🏳️ Feature Flags](#-feature-flags)
    * [Available Flags](#available-flags)
    * [Default Flags](#default-flags)
  * [🧪 Tested Architectures](#-tested-architectures)
<!-- TOC -->

## 🔨 Building
> [!IMPORTANT]
> This project makes use of Rust 2024 edition, ensure `rustc --version` outputs `1.85.0` or greater.
> Update rustc by invoking `rustup update`.

1) [Ensure Rust is correctly configured](https://www.rust-lang.org/tools/install) on the machine.
2) Invoke `cargo build --release` to build using release profile.

## 🏳️ Feature Flags
> [!TIP]
> To configure compilation flags refer to the [rustc book](https://doc.rust-lang.org/rustc/command-line-arguments.html#--cfg-configure-the-compilation-environment).

### Available Flags
`benchmarking` to enable charting and benchmark module.

### Default Flags
- `benchmarking`

## 🧪 Tested Architectures
- `x86_64-unknown-linux-gnu`
