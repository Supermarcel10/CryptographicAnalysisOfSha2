use std::collections::BTreeMap;
use std::error::Error;
use std::io::{BufReader, Read};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};
use nix::sys::signal::{Signal, SIGABRT, SIGALRM, SIGHUP, SIGILL, SIGKILL, SIGSEGV, SIGSYS, SIGTERM, SIGXCPU};
use regex::Regex;
use wait_timeout::ChildExt;
use crate::sha::{MessageBlock, OutputHash, StartVector, Word};
use crate::smt_lib::smt_lib::generate_smtlib_files;
use crate::structs::benchmark::{Benchark, BenchmarkResult, Solver, SolverArg};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;
use crate::structs::sha_state::ShaState;
use crate::verification::colliding_pair::{CollidingPair, MessageData};
use crate::verification::verify_hash::VerifyHash;

#[cfg(feature = "graphing")] mod graphing;
#[cfg(feature = "smt-gen")] mod smt_lib;
mod sha;
mod verification;
mod structs;

// TODO: Add overrides for these as parameters
const STOP_TOLERANCE_DEFAULT: u8 = 3;
const TIMEOUT_DEFAULT: Duration = Duration::from_secs(5);
const VERIFY_HASH_DEFAULT: bool = true;

fn main() {
	generate_smtlib_files().expect("Failed to generate files!");

	let hash_function = HashFunction::SHA256;
	let collision_type = CollisionType::FreeStart;
	let solver = Solver::CVC5;
	let parameters: Vec<SolverArg> = vec![];

	let mut sequential_fails: u8 = 0;
	for rounds in 0..6 {
		if sequential_fails == STOP_TOLERANCE_DEFAULT {
			break;
		}

		let result = run_solver_with_benchmark(
			hash_function,
			rounds,
			collision_type,
			solver,
			parameters.clone()
		);

		if let Ok(benchmark) = result {
			match benchmark.result {
				BenchmarkResult::SMTError => {
					panic!("Received SMT Error: {}", benchmark.console_output)
				}
				BenchmarkResult::Aborted => {
					println!("Test aborted!");
					break;
				}
				BenchmarkResult::Sat => {
					let mut colliding_pair = parse_output(&benchmark.console_output, hash_function).unwrap();

					// TODO: Simplify this!
					if VERIFY_HASH_DEFAULT && colliding_pair.verify(hash_function, rounds).expect("Failed to verify hash output!") {
						colliding_pair.verified_hash = Some(colliding_pair.m0.expected_hash.clone());
					}

					println!("{}", colliding_pair);
					sequential_fails = 0;
				}
				BenchmarkResult::Unsat => {
					println!("UNSAT");
					sequential_fails = 0;
				}
				_ => {
					println!("{}", benchmark.result);
					sequential_fails += 1;
				}
			}
			print!("\n\n\n");
		} else {
			println!("An error occurred during benchmark runtime: {}", result.unwrap_err());
			break;
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

fn parse_output(smt_output: &str, hash_function: HashFunction) -> Result<CollidingPair, Box<dyn Error>> {
	let re = Regex::new(r"\(m([01])_([a-hw]|hash)([0-9]+) #b([01]*)\)")?;
	let default_word = hash_function.default_word();

	let mut hash = Box::new([default_word; 8]);
	let mut start_blocks = [[default_word; 16]; 2];
	let mut start_vectors = [[default_word; 8]; 2];
	let mut states = [BTreeMap::new(), BTreeMap::new()];

	for capture in re.captures_iter(smt_output) {
		let msg: usize = capture[1].parse()?;
		let var = &capture[2];
		let round: usize = capture[3].parse()?;
		let val = Word::from_str_radix(&capture[4], 2, hash_function)?;

		if var == "hash" {
			hash[round] = val;
		} else {
			let var_char: char = var.parse()?;

			// Parse H constants (CV/IV)
			if round == 0 && var_char != 'w' {
				let i = (var_char as u8) - ('a' as u8);
				start_vectors[msg][i as usize] = val;
			}

			// Parse start blocks
			if var_char == 'w' {
				start_blocks[msg][round] = val;
			}

			// Upsert updated state
			states[msg].entry(round).and_modify(|state| {
				update_state_variable(state, var_char, val);
			}).or_insert_with(|| {
				let mut state = MutableShaState::default();
				state.i = round as u8;
				update_state_variable(&mut state, var_char, val);
				state
			});
		}
	}

	let mut messages = vec![];
	for (i, message_states) in states.into_iter().enumerate() {
		let mut states = vec![];
		for (_, state) in message_states {
			states.push(
				state
					.to_immutable()
					.ok_or("Failed to retrieve all message states")?
			);
		}

		messages.push(MessageData {
			m: MessageBlock(start_blocks[i]),
			cv: StartVector::CV(start_vectors[i]),
			states,
			expected_hash: OutputHash(hash.clone()),
		});
	}

	let [m0, m1] = messages.try_into().unwrap();
	Ok(CollidingPair {
		m0,
		m1,
		verified_hash: None,
	})
}

fn run_solver_with_benchmark(
	hash_function: HashFunction,
	rounds: u8,
	collision_type: CollisionType,
	solver: Solver,
	arguments: Vec<SolverArg>,
) -> Result<Benchark, Box<dyn Error>> {
	let mut full_args = Vec::<SolverArg>::new();
	full_args.push(format!("data/{hash_function}_{collision_type}_{rounds}.smt2"));
	full_args.append(&mut arguments.clone());

	let start_time = Instant::now();
	let mut child = Command::new(solver.command())
		.args(full_args)
		.stdout(Stdio::piped())
		.stderr(Stdio::piped())
		.spawn()?;

	let pid = child.id();

	println!("{rounds} rounds; {hash_function} {collision_type} collision\nSMT solver PID: {pid}");

	// TODO: Memory profiling!

	// Await process exit
	let status = child.wait_timeout(TIMEOUT_DEFAULT)?;
	println!("Finished awaiting!");
	let execution_time = start_time.elapsed();

	// Read output
	let cout = match status {
		None => String::new(),
		Some(_) => {
			if let Some(stdout) = child.stdout.take() {
				let mut cout = String::new();
				BufReader::new(stdout).read_to_string(&mut cout)?;
				cout
			} else {
				String::new()
			}
		}
	};

	Ok(Benchark {
		solver,
		arguments,
		hash_function,
		rounds,
		collision_type,
		execution_time,
		memory_bytes: 0,
		result: categorize_status(status, &cout)?,
		console_output: cout,
	})
}

fn categorize_status(exit_status: Option<ExitStatus>, cout: &String) -> Result<BenchmarkResult, Box<dyn Error>> {
	use Signal::*;
	use BenchmarkResult::*;

	Ok(match exit_status {
		None => CPUOut,
		Some(status) => {
			let code = status.code().ok_or("Failed to retrieve status code!")?;
			if code == 0 {
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
					Unknown
				}
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
