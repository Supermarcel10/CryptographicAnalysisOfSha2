# Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers

## 📄 Table of Contents
<!-- TOC -->
* [Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers](#improving-sha-2-collisions-using-satisfiability-modulo-theory-smt-solvers)
  * [📄 Table of Contents](#-table-of-contents)
  * [🔨 Building](#-building)
  * [🧪 Tested Architectures](#-tested-architectures)
  * [Runners](#runners)
    * [Runner Specifications](#runner-specifications)
    * [Solver Versions](#solver-versions)
<!-- TOC -->

## 🔨 Building
> [!IMPORTANT]
> This project makes use of Rust 2024 edition, ensure `rustc --version` outputs `1.85.0` or greater.
> Update rustc by invoking `rustup update`.

1) [Ensure Rust is correctly configured](https://www.rust-lang.org/tools/install) on the machine.
2) Invoke `cargo build --release` to build using release profile.

## 🧪 Tested Architectures
- `x86_64-unknown-linux-gnu`

## Runners
### Runner Specifications
|            |                    **R1**                    |                     **R2**                     |
|-----------:|:--------------------------------------------:|:----------------------------------------------:|
|    **CPU** |              AMD Ryzen 5 5600X               |               AMD Ryzen 9 5900X                |
|    **MEM** |         4 x 8GiB DDR4 3600MHz CL 36          |          4 x 32GiB DDR4 3600MHz CL 36          |
|     **OS** | NixOS 24.11.20250103.d29ab98 (Vicuna) x86_64 |          NixOS 25.05 (Warbler) x86_64          |
| **KERNEL** |                 Linux 6.12.8                 |           Linux Realtime 6.6.77-rt50           |

### Solver Versions

| **Solver** | **R1** | **R2** |
|-----------:|:------:|:------:|
|         Z3 | 4.8.17 | 4.13.4 |
|       CVC5 | 1.2.0  | 1.2.1  |
|      Yices | 2.6.5  | 2.6.5  |
|   Bitwuzla | 0.6.0  | 0.7.0  |
|  Boolector | 3.2.3  | 3.2.3  |
|        STP | 2.3.3  | 2.3.4  |
