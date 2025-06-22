# Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers

> [!CAUTION]
> ⚠️ The `sha2-collision sha2` subcommand is not a viable secure replacement for hashing functions! ⚠️
> This subcommand has been made for a simplified and streamlined verification process, by exposing control over compression rounds and the initial vector.
> If you are looking for sha2 hashing functionality for your Rust project, you likely want the [sha2 crate](https://github.com/RustCrypto/hashes).

## 📄 Table of Contents
<!-- TOC -->
* [Improving SHA-2 Collisions Using Satisfiability Modulo Theory (SMT) Solvers](#improving-sha-2-collisions-using-satisfiability-modulo-theory-smt-solvers)
  * [📄 Table of Contents](#-table-of-contents)
  * [📖 Context](#-context)
    * [📝 Introduction](#-introduction)
    * [🎯 Aims and Scope](#-aims-and-scope)
    * [📊 Results](#-results)
  * [🔨 Building](#-building)
    * [Running](#running)
    * [Subcommands](#subcommands)
  * [🧪 Architectures](#-architectures)
  * [🖥️ Runners](#-runners)
    * [Runner Specifications](#runner-specifications)
    * [BIOS Settings](#bios-settings)
    * [Solver Versions](#solver-versions)
    * [Reproducability](#reproducability)
  * [🔬 Testing](#-testing)
  * [📁 Project Structure](#-project-structure)
  * [🔄 Dependencies](#-dependencies)
  * [➕️ Forks & Contributions](#-forks--contributions)
  * [📕 License](#-license)
<!-- TOC -->

## 📖 Context
### 📝 Introduction

Inspired by Li et Al. 2024, this dissertation project experimented with practical
feasibility of finding SHA-2 collisions using SMT (Satisfiability Modulo Theories) solvers.
While SHA-2 is considered cryptographically secure against collision attacks,
the theoretical possibility of finding collisions through computational methods remains an active area of research.
Automated reasoning tools, such as SMT solvers, present a compelling approach for differential cryptanalysis.

### 🎯 Aims and Scope

The primary aim of this project was to evaluate and compare the effectiveness of various SMT
solvers in finding SHA-2 hash collisions, with specific focus on performance analysis and parameter optimisation.

The scope encompasses both theoretical analysis of SMTLIB representation and empirical evaluation of solver
performance under controlled benchmarking conditions.

### 📊 Results

The benchmarking revealed significant performance variations between SMT solvers when applied to SHA-2 collision problems.
Detailed metrics can be found in the `results/` directory. Comparative graphs can be found in `graphs/`.

An extended abstract publication for SMT2025 has been approved, and is awaiting publication.
A [dissertation specific report](docs/Report/Report.pdf) has been written outlining in-depth analysis and information.

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
> Ensure solvers are in CLI PATH to work properly.
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
|            |              **Specification**              |
|-----------:|:-------------------------------------------:|
|    **CPU** |              AMD Ryzen 9 5900X              |
|    **MEM** | 4 x 32GiB DDR4 3600MHz 18-22-22-52-64 1.35V |
|     **OS** |        NixOS 25.05 (Warbler) x86_64         |
| **KERNEL** |         Linux Realtime 6.6.77-rt50          |

### BIOS Settings
|                        **Setting** |           **Value**            |
|-----------------------------------:|:------------------------------:|
|                      **CPU Clock** |             37.00              |
|              **CPU Clock Control** |          100.000 MHz           |
|                            **XMP** | DDR4-3600 18-22-22-52-64 1.35V |
|                      **CPU VCore** |             0.818V             |
| **CPU VCore Loadline Calibration** |              LOW               |
|                    **CSM Support** |            ENABLED             |

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

### Reproducability
This runner can be rebuilt at any time, using the [NixOS configuration](https://github.com/Supermarcel10/NixOSConfig/blob/f1d26ec/devices/E01/configuration.nix).

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
- `smt/`: (Auto-Generated) Output directory containing produced SMTLIB 2.6 format encoding.
- `solvers/`: Helper binaries which were patched, or otherwise modified in some manner.
	- For more details, see the solver version notes.
- `src/`: Source code. The code is split into different modules handling each subcommand. Some of these have some overlap, or functions that they share with eachother, but are otherwise independent.
	- `benchmark/`: Handles running and parsing benchmarks.
	- `data/`: A shared utility module for retrieving data in a unified manner.
	- `graphing/`: Handles generation of graphs and any graph components.
	- `sha/`: A custom sha2 implementation, shadowing the standard, but also exposing compression rounds, initial vectors and such. Primarily used for verification purposes.
	- `smt_lib/`: Handles everything for generating smt2 files with various encodings. Also exposes a utility to load smt files.
	- `structs/`: Handles binding structs and traits between modules.
	- `verification/`: Handles verification and display outputs.

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
