use std::io::{BufReader, Read};
use std::ops::Range;
use std::os::unix::prelude::CommandExt;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use chrono::Local;
use nix::sys::signal::{Signal, killpg};
use nix::unistd::Pid;
use sha2_core::structs::collision_type::CollisionType;
use sha2_core::structs::hash_function::HashFunction;
use sha2_smt::smt_lib::smt_retriever::{EncodingType, SmtRetriever};
use wait_timeout::ChildExt;

use crate::benchmark::{Benchmark, BenchmarkResult, SmtSolver, SolverArg};

pub struct BenchmarkRunner {
	stop_tolerance : u8,
	timeout : Duration,
	smt_retriever : SmtRetriever,
	benchmark_save_dir : Option<PathBuf>,
	continue_on_failure : bool,
	encoding_type : EncodingType,
	is_rerun : bool
}

impl BenchmarkRunner {
	pub fn new(
		stop_tolerance : u8,
		timeout : Duration,
		smt_retriever : SmtRetriever,
		benchmark_save_dir : Option<PathBuf>,
		continue_on_failure : bool,
		encoding_type : EncodingType,
		is_rerun : bool
	) -> Self {
		BenchmarkRunner {
			stop_tolerance,
			timeout,
			smt_retriever,
			benchmark_save_dir,
			continue_on_failure,
			encoding_type,
			is_rerun
		}
	}

	pub fn run_benchmarks(
		&self,
		solvers : Vec<SmtSolver>,
		hash_functions : Vec<HashFunction>,
		collision_types : Vec<CollisionType>,
		round_range : Range<u8>,
		arguments : Vec<SolverArg>
	) -> Result<()> {
		for solver in solvers {
			for hash_function in &hash_functions {
				for collision_type in &collision_types {
					let mut sequential_fails = 0;
					if arguments.is_empty() {
						self.invoke(
							solver,
							hash_function,
							collision_type,
							round_range.clone(),
							None,
							&mut sequential_fails
						)?;
					} else {
						for arg in arguments.clone() {
							self.invoke(
								solver,
								hash_function,
								collision_type,
								round_range.clone(),
								Some(arg),
								&mut sequential_fails
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
		solver : SmtSolver,
		hash_function : &HashFunction,
		collision_type : &CollisionType,
		round_range : Range<u8>,
		arg : Option<SolverArg>,
		sequential_fails : &mut u8
	) -> Result<()> {
		// Ensure range max does not exceed hash function max rounds.
		let hash_max = hash_function.max_rounds();
		let min = round_range.clone().min().unwrap_or(1).max(1);
		let max = round_range.clone().max().unwrap_or(hash_max).min(hash_max) + 1;

		for rounds in min..max {
			let smt_path = self.smt_retriever.get_file(
				*hash_function,
				*collision_type,
				rounds,
				self.encoding_type
			);

			let mut result = self.run_solver_with_benchmark(
				*hash_function,
				rounds,
				*collision_type,
				solver,
				self.is_rerun,
				self.encoding_type,
				smt_path,
				arg.clone()
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
		result : &mut Result<Benchmark>,
		sequential_fails : &mut u8
	) -> Result<()> {
		match result {
			Ok(benchmark) => {
				if let Some(path) = &self.benchmark_save_dir {
					benchmark.save(path).with_context(|| {
						format!("failed to save benchmark to {}", path.display())
					})?;
				}

				match benchmark.result {
					BenchmarkResult::SMTError => {
						println!("Received SMT Error: {:?}\n", benchmark.console_output);
						*sequential_fails += 1;
					}
					BenchmarkResult::Sat | BenchmarkResult::Unsat => {
						match benchmark.parse_output()? {
							None => println!("UNSAT\n"),
							Some(colliding_pair) => println!("{}\n", colliding_pair)
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
				println!("{err}\n");
				if !self.continue_on_failure {
					Err(anyhow::anyhow!("{err:#}\nAborting benchmarks!"))
				} else {
					println!("Continuing!\n\n");
					Ok(())
				}
			}
		}
	}

	#[allow(clippy::too_many_arguments)]
	fn run_solver_with_benchmark(
		&self,
		hash_function : HashFunction,
		rounds : u8,
		collision_type : CollisionType,
		solver : SmtSolver,
		is_rerun : bool,
		encoding : EncodingType,
		smt_file : PathBuf,
		arguments : Option<SolverArg>
	) -> Result<Benchmark> {
		ensure_solver_present(&solver)?;

		let mut full_args : Vec<SolverArg> = vec!["-v".into(), solver.command()];

		let mut split_args : Vec<String> = vec![];
		let mut has_args = false;
		if let Some(args) = &arguments {
			split_args.extend(args.split(" ").map(String::from));
			has_args = true;
		}

		let file_path = smt_file.to_str().ok_or_else(|| {
			anyhow::anyhow!(
				"failed to get smt file path for solver {solver} (file: {})",
				smt_file.display()
			)
		})?;
		full_args.extend(split_args);
		full_args.push(file_path.into());

		let date_time = Local::now().to_utc();
		let start_time = Instant::now();
		let mut child = Command::new("time")
			.args(full_args)
			.process_group(0)
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.spawn()
			.with_context(|| {
				format!(
					"failed to spawn solver {solver} (command: {})",
					solver.command()
				)
			})?;

		let pid = child.id();
		let arg_str = if let Some(args) = &arguments {
			if !args.is_empty() {
				&format!(" {args}")
			} else {
				""
			}
		} else {
			""
		};

		println!(
			"{rounds} rounds; {hash_function} {collision_type} collision; {solver}{arg_str}; SMT solver PID: {pid}\nFile: {file_path}"
		);

		// Await process exit
		let status = child.wait_timeout(self.timeout).with_context(|| {
			format!(
				"failed to await solver {solver} (command: {})",
				solver.command()
			)
		})?;
		let execution_time = start_time.elapsed();

		// Read output
		let (cout, cerr) = match status {
			None => {
				killpg(Pid::from_raw(pid as i32), Signal::SIGKILL).with_context(|| {
					format!("failed to kill timed-out solver {solver} (pid: {pid})")
				})?;
				child.wait().with_context(|| {
					format!("failed to reap timed-out solver {solver} (pid: {pid})")
				})?;
				(String::new(), String::new())
			}
			Some(_) => {
				let cout = if let Some(stdout) = child.stdout.take() {
					let mut cout = String::new();
					BufReader::new(stdout)
						.read_to_string(&mut cout)
						.with_context(|| format!("failed to read stdout of solver {solver}"))?;
					cout
				} else {
					String::new()
				};

				let cerr = if let Some(stderr) = child.stderr.take() {
					let mut cerr = String::new();
					BufReader::new(stderr)
						.read_to_string(&mut cerr)
						.with_context(|| format!("failed to read stderr of solver {solver}"))?;
					cerr
				} else {
					String::new()
				};

				(cout, cerr)
			}
		};

		// Extract memory information
		let bytes_rss = max_resident_set_size(&cerr).unwrap_or(0);

		let is_baseline = !has_args && self.timeout == Duration::from_secs(900);

		Ok(Benchmark {
			date_time,
			solver,
			arguments,
			hash_function,
			rounds,
			collision_type,
			execution_time,
			memory_bytes : bytes_rss,
			result : Self::categorize_status(status, &cout)?,
			console_output : (cout, cerr),
			is_valid : None,
			is_baseline,
			is_rerun,
			encoding,
			stop_tolerance : self.stop_tolerance,
			timeout : self.timeout
		})
	}

	fn categorize_status(exit_status : Option<ExitStatus>, cout : &str) -> Result<BenchmarkResult> {
		use BenchmarkResult::*;
		use Signal::*;

		Ok(match exit_status {
			None => CPUOut,
			Some(status) => {
				let code = status
					.code()
					.ok_or_else(|| anyhow::anyhow!("failed to retrieve solver status code"))?;
				let outcome = cout.lines().next().unwrap_or("unknown").to_lowercase();

				if outcome.contains("unsat") {
					Unsat
				} else if outcome.contains("sat") {
					Sat
				} else {
					let signal = Signal::try_from(code)
						.with_context(|| format!("failed to interpret solver exit code {code}"))?;

					match signal {
						SIGABRT | SIGKILL | SIGSEGV => MemOut,
						SIGALRM | SIGTERM | SIGXCPU => CPUOut,
						SIGHUP | SIGILL | SIGSYS => SMTError,
						_ => Unknown
					}
				}
			}
		})
	}
}

fn ensure_solver_present(solver : &SmtSolver) -> Result<()> {
	if !check_command_present(&solver.command()).with_context(|| {
		format!(
			"failed to check for solver {solver} (command: {})",
			solver.command()
		)
	})? {
		return Err(anyhow::anyhow!(
			"solver {} was not found on the host system",
			solver.command()
		));
	}

	Ok(())
}

fn check_command_present(command : &str) -> Result<bool> {
	let output = Command::new("sh")
		.arg("-c")
		.arg(format!("command -v {}", command))
		.output()
		.with_context(|| format!("failed to check for solver command {command}"))?;

	Ok(output.status.success())
}

fn max_resident_set_size(cerr : &str) -> Option<u64> {
	let line = cerr
		.lines()
		.find(|line| line.contains("Maximum resident set size"))?;
	let value = line.split(':').nth(1)?.trim().parse::<u64>().ok()?;
	// Convert kB to bytes
	Some(value * 1024)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn absent_solver_command_reports_not_present() {
		let present = check_command_present("definitely-not-an-installed-solver-xyz").unwrap();

		assert!(!present, "bogus solver command reported as present");
	}

	#[test]
	fn existing_shell_command_reports_present() {
		let present = check_command_present("sh").unwrap();

		assert!(present, "shell command 'sh' reported as absent");
	}
}
