use std::error::Error;
use std::io::{BufReader, Read};
use std::os::unix::prelude::CommandExt;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};
use chrono::Local;
use nix::sys::signal::{killpg, Signal};
use nix::unistd::Pid;
use wait_timeout::ChildExt;
use crate::smt_lib::encoding_types::EncodingType;
use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver, SolverArg};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum BenchmarkError {
	#[error("solver {solver} was not found on the host system")]
	SolverNotFound {
		solver: String,
	},
}

pub struct BenchmarkRunner {
	stop_tolerance: u8,
	timeout: Duration,
	benchmark_save_path: PathBuf,
	save_benchmarks: bool,
	continue_on_failure: bool,
}

impl BenchmarkRunner {
	pub fn new(
		stop_tolerance: u8,
		timeout: Duration,
		benchmark_save_path: PathBuf,
		save_benchmarks: bool,
		continue_on_failure: bool,
	) -> Self {
		BenchmarkRunner {
			stop_tolerance,
			timeout,
			benchmark_save_path,
			save_benchmarks,
			continue_on_failure,
		}
	}

	// TODO: Split out somehow
	pub fn run_benchmarks(&self) -> Result<(), Box<dyn Error>> {
		let solvers = [SmtSolver::Bitwuzla];
		let arguments: Vec<SolverArg> = vec![
			"--sat-solver kissat".into()
		];
		let hash_functions = [HashFunction::SHA256];
		let collision_types = [CollisionType::Standard];

		for solver in solvers {
			for hash_function in hash_functions {
				for collision_type in collision_types {
					for arg in arguments.iter() {
						let mut sequential_fails: u8 = 0;
						for rounds in [5, 18] {
							let smt_file = self.retrieve_file(
								hash_function,
								collision_type,
								rounds,
							);

							let result = self.run_solver_with_benchmark(
								hash_function,
								rounds,
								collision_type,
								solver,
								smt_file,
								vec![arg.clone()],
							);

							self.handle_result(result, &mut sequential_fails)?;

							if self.stop_tolerance != 0 && self.stop_tolerance == sequential_fails {
								println!("Failed {sequential_fails} in a row!\n");
								break;
							}
						}
					}
				}
			}
		}

		Ok(())
	}

	fn retrieve_file(
		&self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		rounds: u8,
	) -> String {
		// TODO: Implement properly to do retrieval
		format!("smt/{hash_function}_{collision_type}_{rounds}.smt2")
	}

	fn handle_result(
		&self,
		result: Result<Benchmark, Box<dyn Error>>,
		sequential_fails: &mut u8,
	) -> Result<(), Box<dyn Error>> {
		match result {
			Ok(benchmark) => {
				if self.save_benchmarks {
					benchmark
						.save(&self.benchmark_save_path)
						.expect("Failed to save benchmark!");
				}

				match benchmark.result {
					BenchmarkResult::SMTError => {
						println!("Received SMT Error: {:?}\n", benchmark.console_output);
						*sequential_fails += 1;
					}
					BenchmarkResult::Sat | BenchmarkResult::Unsat => {
						match benchmark.parse_output()? {
							None => println!("UNSAT\n"),
							Some(colliding_pair) => println!("{}\n", colliding_pair),
						}

						*sequential_fails = 0;
					}
					_ => {
						println!("{}\n", benchmark.result);
						*sequential_fails += 1;
					}
				}
				Ok(())
			}
			Err(err) => {
				println!("{}\n", err);
				if !self.continue_on_failure {
					Err(err)
				} else {
					println!("Continuing!\n\n");
					Ok(())
				}
			}
		}
	}

	fn run_solver_with_benchmark(
		&self,
		hash_function: HashFunction,
		rounds: u8,
		collision_type: CollisionType,
		solver: SmtSolver,
		smt_file: String,
		arguments: Vec<SolverArg>,
	) -> Result<Benchmark, Box<dyn Error>> {
		if !check_command_present(&solver.command())? {
			return Err(Box::from(BenchmarkError::SolverNotFound { solver: solver.command() }));
		}

		let mut full_args: Vec<SolverArg> = vec![
			"-v".into(),
			solver.command(),
		];

		let mut split_args: Vec<String> = vec![];
		for arg in arguments.iter() {
			split_args.extend(arg.split(" ").map(String::from));
		}

		full_args.extend(split_args);
		full_args.push(smt_file.clone());

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
		println!("{rounds} rounds; {hash_function} {collision_type} collision; {solver}{spc}{arg_string}; SMT solver PID: {pid}\nFile: {smt_file}");

		// Await process exit
		let status = child.wait_timeout(self.timeout)?;
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

		let is_baseline = arguments.is_empty() && self.timeout == Duration::from_secs(900);

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
			is_baseline,
			is_rerun: false, // TODO
			encoding: EncodingType::BruteForce, // TODO
			stop_tolerance: self.stop_tolerance,
			timeout: self.timeout,
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

fn check_command_present(command: &str) -> Result<bool, Box<dyn Error>> {
	let output = Command::new("sh")
		.arg("-c")
		.arg(format!("command -v {}", command))
		.output()?;

	Ok(output.status.success())
}
