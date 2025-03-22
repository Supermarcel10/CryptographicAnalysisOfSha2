use std::collections::BTreeMap;
use std::error::Error;
use std::io::{BufReader, Read};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use regex::Regex;
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

fn main() {
	generate_smtlib_files().expect("Failed to generate files!");

	let hash_function = HashFunction::SHA256;
	let collision_type = CollisionType::Standard;

	let solver = Solver::CVC5;
	let parameters: Vec<SolverArg> = vec![];

	for rounds in 0..6 {
		let result = run_solver_with_benchmark(hash_function, rounds, collision_type, solver, parameters.clone());

		match result {
			Ok(benchmark) => {
				if benchmark.result == BenchmarkResult::SMTError {
					panic!("Received SMT Error: {}", benchmark.console_output)
				} else if benchmark.result == BenchmarkResult::Sat {
					println!("SAT");
					let mut colliding_pair = parse_output(&benchmark.console_output, hash_function).unwrap();

					// TODO: Simplify this!
					if colliding_pair.verify(hash_function, rounds).expect("TODO: panic message") {
						colliding_pair.verified_hash = Some(colliding_pair.m0.expected_hash.clone());
					}
					println!("{}", colliding_pair);
				} else {
					println!("UNSAT");
					println!("{:?}\n", benchmark);
				}
			},
			Err(err) => println!("Error occurred: {}", err),
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

// TODO: Make this work for non FreeStart too
fn parse_output(smt_output: &str, hash_function: HashFunction) -> Result<CollidingPair, Box<dyn Error>> {
	let re = Regex::new(r"\(m([01])_([a-hw]|hash)([0-9]+) #b([01]*)\)")?;
	let default_word = hash_function.default_word();

	let mut hash = Box::new([default_word; 8]);
	let mut start_blocks = [[default_word; 16]; 2];
	let mut start_vectors = [[default_word; 8]; 2];
	// let mut states: [HashMap<usize, MutableShaState>; 2] = [HashMap::new(), HashMap::new()];
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

			// Parse states
			if !['a', 'e', 'w'].contains(&var_char) {
				continue;
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

	let mut messages: Vec<MessageData> = vec![];
	for (i, message_state) in states.into_iter().enumerate() {
		let states: Vec<ShaState> = message_state
			.into_iter()
			.map(|(_, v)| v.to_immutable().unwrap())
			.collect();

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
	let mut args_with_file = arguments.clone();
	args_with_file.push(format!("data/{hash_function}_{collision_type}_{rounds}.smt2"));

	let child = Command::new(solver.command())
		.args(args_with_file)
		.stdout(Stdio::piped())
		.stderr(Stdio::piped())
		.spawn()?;

	let start_time = Instant::now();
	let pid = child.id();
	let child_arc = Arc::new(Mutex::new(child));

	// TODO: Investigate why this is throwing an error after the 1st iteration
	if interrupt_kill_child(Arc::clone(&child_arc)).is_err() {
		// println!("Failed to set interrupt to kill child. Continuing...")
	}

	println!("{rounds} rounds; {hash_function} {collision_type} collision\nSMT solver PID: {pid}");

	// TODO: Memory profiling!

	let mut child_guard = child_arc.lock().unwrap();
	let status = child_guard.wait()?; // Await process exit
	let execution_time = start_time.elapsed();

	// Read output
	if let Some(stdout) = child_guard.stdout.take() {
		let mut console_output = String::new();
		BufReader::new(stdout).read_to_string(&mut console_output)?;

		let status_code = status.code().unwrap_or(-1);
		let solver_status = console_output
			.lines()
			.next()
			.unwrap_or("unknown");

		let result = match (status_code, solver_status) {
			(0, "sat") => BenchmarkResult::Sat,
			(0, "unsat") => BenchmarkResult::Unsat,
			(1, _) => BenchmarkResult::SMTError,
			(2, _) => BenchmarkResult::Aborted,
			_ => BenchmarkResult::Unknown,
			// TODO: Handle MEMOUT and CPUOUT states
		};

		return Ok(Benchark {
			solver,
			arguments,
			hash_function,
			rounds,
			collision_type,
			execution_time,
			memory_bytes: 0,
			result,
			console_output,
		})
	}

	Err(Box::from("Generic benchmark failure!"))
}

fn interrupt_kill_child(child_arc: Arc<Mutex<Child>>) -> Result<(), ctrlc::Error> {
	ctrlc::set_handler(move || {
		println!("\nReceived interrupt, killing child process...");
		kill_process(&child_arc);
		std::process::exit(0);
	})
}

fn kill_process(child_arc: &Arc<Mutex<Child>>) {
	match child_arc.lock().unwrap().kill() {
		Ok(_) => println!("Child process killed successfully"),
		Err(e) => eprintln!("Failed to kill child process: {}", e),
	}
}
