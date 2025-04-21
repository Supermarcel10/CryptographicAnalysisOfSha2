use std::error::Error;
use std::io::{BufReader, Read};
use std::ops::Range;
use std::os::unix::prelude::CommandExt;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};
use chrono::Local;
use nix::sys::signal::{killpg, Signal};
use nix::unistd::Pid;
use wait_timeout::ChildExt;
use crate::smt_lib::smt_retriever::{EncodingType, SmtRetriever};
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
	smt_retriever: SmtRetriever,
	benchmark_save_dir: Option<PathBuf>,
	continue_on_failure: bool,
	encoding_type: EncodingType,
	is_rerun: bool,
}

impl BenchmarkRunner {
	pub fn new(
		stop_tolerance: u8,
		timeout: Duration,
		smt_retriever: SmtRetriever,
		benchmark_save_dir: Option<PathBuf>,
		continue_on_failure: bool,
		encoding_type: EncodingType,
		is_rerun: bool,
	) -> Self {
		BenchmarkRunner {
			stop_tolerance,
			timeout,
			smt_retriever,
			benchmark_save_dir,
			continue_on_failure,
			encoding_type,
			is_rerun,
		}
	}

	pub fn run_benchmarks(
		&self,
		solvers: Vec<SmtSolver>,
		hash_functions: Vec<HashFunction>,
		collision_types: Vec<CollisionType>,
		round_range: Range<u8>,
		arguments: Vec<SolverArg>,
	) -> Result<(), Box<dyn Error>> {
		for solver in solvers {
			for hash_function in &hash_functions {
				for collision_type in &collision_types {
					let mut sequential_fails = 0;
					if arguments.len() == 0 {
						self.invoke(
							solver,
							hash_function,
							collision_type,
							round_range.clone(),
							None,
							&mut sequential_fails,
						)?;
					} else {
						for arg in arguments.clone() {
							self.invoke(
								solver,
								hash_function,
								collision_type,
								round_range.clone(),
								Some(arg),
								&mut sequential_fails,
							)?;
						}
					}
				}
			}
		}

		Ok(())
	}

	fn invoke(
		&self,
		solver: SmtSolver,
		hash_function: &HashFunction,
		collision_type: &CollisionType,
		round_range: Range<u8>,
		arg: Option<SolverArg>,
		sequential_fails: &mut u8,
	) -> Result<(), Box<dyn Error>> {
		for rounds in round_range {
			let smt_file = self.smt_retriever.retrieve_file(
				*hash_function,
				*collision_type,
				rounds,
				self.encoding_type.clone(),
			)?;

			let mut result = self.run_solver_with_benchmark(
				*hash_function,
				rounds,
				*collision_type,
				solver,
				self.is_rerun,
				self.encoding_type.clone(),
				smt_file,
				arg.clone(),
			);

			if let Err(err) = self.handle_result(&mut result, sequential_fails) {
				if !self.continue_on_failure {
					return Err(err);
				}

				continue;
			}

			if self.stop_tolerance != 0 && self.stop_tolerance == *sequential_fails {
				println!("Failed {} in a row!\n", sequential_fails);
				break;
			}
		}

		Ok(())
	}

	fn handle_result(
		&self,
		result: &mut Result<Benchmark, Box<dyn Error>>,
		sequential_fails: &mut u8,
	) -> Result<(), Box<dyn Error>> {
		match result {
			Ok(benchmark) => {
				if let Some(path) = &self.benchmark_save_dir {
					benchmark
						.save(path)
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
					Err(Box::from("Aborting benchmarks!"))
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
		is_rerun: bool,
		encoding: EncodingType,
		smt_file: PathBuf,
		arguments: Option<SolverArg>,
	) -> Result<Benchmark, Box<dyn Error>> {
		if !check_command_present(&solver.command())? {
			return Err(Box::from(BenchmarkError::SolverNotFound { solver: solver.command() }));
		}

		let mut full_args: Vec<SolverArg> = vec![
			"-v".into(),
			solver.command(),
		];

		let mut split_args: Vec<String> = vec![];
		let mut has_args = false;
		if let Some(args) = &arguments {
			split_args.extend(args.split(" ").map(String::from));
			has_args = true;
		}

		let file_path = smt_file.to_str().ok_or("Failed to get smt file path")?;
		full_args.extend(split_args);
		full_args.push(file_path.into());

		let date_time = Local::now().to_utc();
		let start_time = Instant::now();
		let mut child = Command::new("time")
			.args(full_args)
			.process_group(0)
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.spawn()?;

		let pid = child.id();
		let arg_str = if let Some(args) = &arguments {
			if args.len() > 0 {
				&format!(" {args}")
			} else { "" }
		} else { "" };

		println!("{rounds} rounds; {hash_function} {collision_type} collision; {solver}{arg_str}; SMT solver PID: {pid}\nFile: {file_path}");

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

		let is_baseline = !has_args && self.timeout == Duration::from_secs(900);

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
			is_valid: None,
			is_baseline,
			is_rerun,
			encoding,
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
