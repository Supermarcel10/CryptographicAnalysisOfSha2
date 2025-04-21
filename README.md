# Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers

> [!CAUTION]
> ⚠️ The `sha2-collision sha2` subcommand is not a viable secure replacement for hashing functions! ⚠️
> This subcommand has been made for a simplified and streamlined verification process, by exposing control over compression rounds and the initial vector.
> If you are looking for sha2 hashing functionality for your Rust project, you likely want the [sha2 crate](https://github.com/RustCrypto/hashes).

## 📄 Table of Contents
<!-- TOC -->
* [Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers](#improving-sha-2-collisions-using-satisfiability-modulo-theory-smt-solvers)
  * [📄 Table of Contents](#-table-of-contents)
  * [🔨 Building](#-building)
    * [Running](#running)
    * [Subcommands](#subcommands)
  * [🧪 Architectures](#-architectures)
  * [🖥️ Runners](#-runners)
    * [Runner Specifications](#runner-specifications)
    * [Solver Versions](#solver-versions)
  * [🔬 Testing](#-testing)
  * [📁 Project Structure](#-project-structure)
  * [🔄 Dependencies](#-dependencies)
  * [➕️ Forks & Contributions](#-forks--contributions)
  * [📕 License](#-license)
<!-- TOC -->

## 🔨 Building
> [!IMPORTANT]
> This project makes use of Rust 2024 edition, ensure `rustc --version` outputs `1.85.0` or greater.
> Update rustc by invoking `rustup update`.

1) [Ensure Rust is correctly configured](https://www.rust-lang.org/tools/install) on the machine.
2) Invoke `cargo run --release` to build and run using release profile.
3) An executable binary has been produced in `target/release/sha2-collision`.

### Running
> [!NOTE]
> Separate installation of solvers is required to run the `benchmark` subcommand.
> Ensure that the solvers are exported in CLI path for everything to work properly.
> An error will be thrown if the command does not exist.

To run a specified subcommand, such as `sha2-collision sha2 --help`, you can invoke either:
- `cargo run --release sha2 --help` (This will not invoke a rebuild unless code has been altered)
- `./target/release/sha2-collision sha2 --help`

### Subcommands
Every subcommand and flag has been thorougly documented, with defaults and enumerable options where aplicable.

## 🧪 Architectures

| OS                 | Supported? | Tested? |
|--------------------|:----------:|:-------:|
| Unix-Like (x86_64) |     🟩     |   🟩    |
| Unix-Like (ARM)    |     🟨     |   🟥    |
| DOS-Like (x86_64)  |     🟥     |   🟥    |
| DOS-Like (ARM)     |     🟥     |   🟥    |

## 🖥️ Runners
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

## 🔬 Testing
Some segments of code have unit tests in order to assert corectness over changes.
In order to run these tests invoke `cargo test`.

## 📁 Project Structure
- `docs/`: Source and produced documentation.
- `graphs/`: Output directory containing produced graphs.
- `proofs/`: SMT solver proofs for finding a contradiction.
  - UNSAT implies no contradictions were found, and the encodings are sound.
- `reference/`: Reference documentation, which the project bases on.
- `results/`: Output directory containing deserialized json Benchmark objects, representing each run.
- `smt/`: Output directory containing produced SMTLIB 2.6 format encoding.
- `solvers/`: Helper binaries which were patched, or otherwise modified in some manner.
  - For more details, see the solver version notes.
- `src/`: Source code.

## 🔄 Dependencies
All dependencies and feature flags are defined in `Cargo.toml`.
For a full listing of dependency licenses, run `cargo license`.

## ➕️ Forks & Contributions
Using this as a template and building ground for futher research is much apprechiated.

If you wish to contribute, make a fork of this repository, and when ready, create a PR.

## 📕 License
This project is licensed under [CC BY-NC-SA](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.en).
You are free to share, modify and copy the code with attribution, as long as it is not for commercial purposes.
For more information see [the lincense](LICENSE.md).
