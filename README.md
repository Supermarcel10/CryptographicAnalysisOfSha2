# Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers

## 📄 Table of Contents
<!-- TOC -->
* [Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers](#improving-sha-2-collisions-using-satisfiability-modulo-theory-smt-solvers)
  * [📄 Table of Contents](#-table-of-contents)
  * [🔨 Building](#-building)
  * [Architectures](#architectures)
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

## Architectures

| OS                 | Supported? |
|--------------------|------------|
| Unix-Like (x86_64) | 🟩         |
| Unix-Like (ARM)    | 🟨         |
| DOS-Like (x86_64)  | 🟥         |
| DOS-Like (ARM)     | 🟥         |

## Runners
### Runner Specifications
|            |      **Specification**       |
|-----------:|:----------------------------:|
|    **CPU** |      AMD Ryzen 9 5900X       |
|    **MEM** | 4 x 32GiB DDR4 3600MHz CL 36 |
|     **OS** | NixOS 25.05 (Warbler) x86_64 |
| **KERNEL** |  Linux Realtime 6.6.77-rt50  |

### Solver Versions

| **Solver** |      **Version**      | **License** |               Notes                |
|-----------:|:---------------------:|:-----------:|:----------------------------------:|
|         Z3 |        4.13.4         |     MIT     |                                    |
|       CVC5 |         1.2.1         |    BSD 3    |                                    |
|      Yices |         2.6.5         |   GPL3.0    |                                    |
|   Bitwuzla |         0.7.0         |     MIT     |                                    |
|  Boolector |         3.2.3         |     MIT     |                                    |
|        STP |         2.3.4         |     MIT     |    Support for SMTLIB 2.0 only     |
|   Colibri2 |       0.4-dirty       |  LGPLv2.1   |   Portable binary in `solvers/`    |
|    MathSAT | 5.6.11 (1a1154baf0ab) |   Custom    | Binary in `solvers/`, autopatchelf |
