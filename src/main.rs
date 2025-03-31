use std::error::Error;
use std::io::{BufReader, Read};
use std::os::unix::prelude::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};
use chrono::Local;
use nix::sys::signal::{killpg, Signal};
use nix::unistd::Pid;
use wait_timeout::ChildExt;
use once_cell::unsync::Lazy;
use plotters::prelude::RGBColor;
use crate::graphing::create_baseline_graph;
use crate::sha::Word;
use crate::smt_lib::smt_lib::generate_smtlib_files;
use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver, SolverArg};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;
use crate::structs::sha_state::ShaState;
use crate::verification::verify_hash::VerifyHash;

// TODO: Look into benchmarking:
// - Different arguments for each solver
// - Different kernels (https://askubuntu.com/a/126671)
// - Different memory timings
// - CPU Core Clock difference

#[cfg(feature = "graphing")] mod graphing;
#[cfg(feature = "smt-gen")] mod smt_lib;
mod sha;
mod verification;
mod structs;

// TODO: Add overrides for these as parameters
const STOP_TOLERANCE_DEFAULT: u8 = 3;
const TIMEOUT_DEFAULT: Duration = Duration::from_secs(15 * 60);
const VERIFY_HASH_DEFAULT: bool = true;
const BENCHMARK_SAVE_PATH_DEFAULT: Lazy<&Path> = Lazy::new(|| Path::new("results/bitwuzla/solver_engine"));
fn main() -> Result<(), Box<dyn Error>> {
	generate_smtlib_files()?;
	// solve_by_brute_force();

	let mut baseline_benchmarks = Benchmark::load_all(&PathBuf::from("results/brute-force"), false)?;
	baseline_benchmarks = baseline_benchmarks
		.into_iter()
		.filter(|b| b.hash_function == HashFunction::SHA256 && b.solver == SmtSolver::Bitwuzla && b.collision_type == CollisionType::Standard)
		.collect();

	let mut deviation_benchmarks = Benchmark::load_all(&PathBuf::from("results/bitwuzla/solver_engine"), false)?;
	deviation_benchmarks = deviation_benchmarks
		.into_iter()
		.filter(|b| b.arguments.contains((&"--bv-solver prop".to_string()).into()))
		.collect();

	let color_palette = vec![
		RGBColor(37, 95, 133),
		RGBColor(140, 33, 85),
		RGBColor(221, 164, 72),
		RGBColor(50, 150, 93),
		RGBColor(0, 0, 0),
	];

	create_baseline_graph(baseline_benchmarks, deviation_benchmarks, color_palette, "test")?;


	Ok(())
}

fn solve_by_brute_force() {
	// , SmtSolver::Yices2, SmtSolver::Boolector, SmtSolver::CVC5, SmtSolver::Z3
	let solvers = [SmtSolver::Bitwuzla];
	let arguments: Vec<SolverArg> = vec![];

	let hash_functions = [HashFunction::SHA256];
	// CollisionType::FreeStart, CollisionType::SemiFreeStart,
	let collision_types = [CollisionType::Standard];

	for solver in solvers {
		for hash_function in hash_functions {
			for collision_type in collision_types {
				for arg in arguments.iter() {
					let mut sequential_fails: u8 = 0;
					for rounds in 9..hash_function.max_rounds() {
						if sequential_fails == STOP_TOLERANCE_DEFAULT {
							println!("Failed {sequential_fails} in a row!\n");
							break;
						}

						let result = BenchmarkRunner::run_solver_with_benchmark(
							hash_function,
							rounds,
							collision_type,
							solver,
							vec![arg.clone()],
						);

						if let Ok(benchmark) = result {
							benchmark.save(*BENCHMARK_SAVE_PATH_DEFAULT).expect("Failed to save benchmark!");

							match benchmark.result {
								BenchmarkResult::SMTError => {
									println!("Received SMT Error: {:?}", benchmark.console_output);
									sequential_fails += 1;
									continue;
								}
								BenchmarkResult::Aborted => {
									println!("Test aborted!");
									break;
								}
								BenchmarkResult::Sat | BenchmarkResult::Unsat => {
									let colliding_pair = benchmark.parse_output().unwrap();

									match colliding_pair {
										None => {
											println!("UNSAT");
										}
										Some(mut colliding_pair) => {
											// TODO: Simplify this!
											if VERIFY_HASH_DEFAULT && colliding_pair.verify(hash_function, rounds).expect("Failed to verify hash output!") {
												colliding_pair.verified_hash = Some(colliding_pair.m0.expected_hash.clone());
											}

											println!("{}", colliding_pair);
										}
									}

									sequential_fails = 0;
								}
								_ => {
									println!("{}", benchmark.result);
									sequential_fails += 1;
								}
							}
							println!();
						} else {
							println!("An error occurred during benchmark runtime: {}", result.unwrap_err());
							break;
						}
					}
				}
			}
		}
	}
}

#[derive(Debug, PartialEq, Clone)]
pub struct MutableShaState {
	pub i: u8,
	pub w: Option<Word>,
	pub a: Option<Word>,
	pub e: Option<Word>,
}

impl Default for MutableShaState {
	fn default() -> Self {
		MutableShaState {
			i: 0,
			w: None,
			a: None,
			e: None,
		}
	}
}

impl MutableShaState {
	fn to_immutable(self) -> Option<ShaState> {
		Some(ShaState {
			i: self.i,
			w: self.w?,
			a: self.a?,
			e: self.e?,
		})
	}
}

fn update_state_variable(state: &mut MutableShaState, variable: char, value: Word) {
	match variable {
		'a' => state.a = Some(value),
		'e' => state.e = Some(value),
		'w' => state.w = Some(value),
		_ => {},
	}
}

struct BenchmarkRunner;

impl BenchmarkRunner {
	fn run_solver_with_benchmark(
		hash_function: HashFunction,
		rounds: u8,
		collision_type: CollisionType,
		solver: SmtSolver,
		arguments: Vec<SolverArg>,
	) -> Result<Benchmark, Box<dyn Error>> {
		// TODO: Ensure that the command exists before attempting to run it, else status code 32512 is returned and this causes an ERRINVAL

		let smt_file = format!("data/{hash_function}_{collision_type}_{rounds}.smt2"); // TODO: Make a neater way of retrieving files!
		let mut full_args: Vec<SolverArg> = vec![
			"-v".into(),
			solver.command(),
		];

		let mut split_args: Vec<String> = vec![];
		for arg in arguments.iter() {
			split_args.extend(arg.split(" ").map(String::from));
		}

		full_args.extend(split_args);
		full_args.push(smt_file);

		let date_time = Local::now().to_utc();
		let start_time = Instant::now();
		let mut child = Command::new("time")
			.args(full_args)
			.process_group(0)
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.spawn()?;

		let pid = child.id();
		let spc = if arguments.len() > 0 { " " } else { "" };
		let arg_string = arguments.join(" ");
		println!("{rounds} rounds; {hash_function} {collision_type} collision; {solver}{spc}{arg_string}; SMT solver PID: {pid}");

		// Await process exit
		let status = child.wait_timeout(TIMEOUT_DEFAULT)?;
		let execution_time = start_time.elapsed();

		// Read output
		let (cout, cerr) = match status {
			None => {
				killpg(Pid::from_raw(pid as i32), Signal::SIGKILL)?;
				child.wait()?;
				(String::new(), String::new())
			},
			Some(_) => {
				let cout = if let Some(stdout) = child.stdout.take() {
					let mut cout = String::new();
					BufReader::new(stdout).read_to_string(&mut cout)?;
					cout
				} else { String::new() };

				let cerr = if let Some(stderr) = child.stderr.take() {
					let mut cerr = String::new();
					BufReader::new(stderr).read_to_string(&mut cerr)?;
					cerr
				} else { String::new() };

				(cout, cerr)
			}
		};

		// Extract memory information
		let mut bytes_rss = 0;
		if let Some(line) = cerr
			.lines()
			.find(|line| line.contains("Maximum resident set size")) {
			if let Some(val_str) = line.split(':').nth(1) {
				if let Ok(value) = val_str.trim().parse::<u64>() {
					// Convert kB to bytes
					bytes_rss = value * 1024;
				}
			}
		}

		Ok(Benchmark {
			date_time,
			solver,
			arguments,
			hash_function,
			rounds,
			collision_type,
			execution_time,
			memory_bytes: bytes_rss,
			result: Self::categorize_status(status, &cout)?,
			console_output: (cout, cerr),
		})
	}

	fn categorize_status(exit_status: Option<ExitStatus>, cout: &String) -> Result<BenchmarkResult, Box<dyn Error>> {
		use Signal::*;
		use BenchmarkResult::*;

		Ok(match exit_status {
			None => CPUOut,
			Some(status) => {
				let code = status.code().ok_or("Failed to retrieve status code!")?;
				let outcome = cout
					.lines()
					.next()
					.unwrap_or("unknown")
					.to_lowercase();

				if outcome.contains("unsat") {
					Unsat
				} else if outcome.contains("sat") {
					Sat
				} else {
					let signal = Signal::try_from(code)?;

					match signal {
						SIGABRT | SIGKILL | SIGSEGV => MemOut,
						SIGALRM | SIGTERM | SIGXCPU => CPUOut,
						SIGHUP | SIGILL | SIGSYS => SMTError,
						_ => Unknown,
					}
				}
			}
		})
	}
}

