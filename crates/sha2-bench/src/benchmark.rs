use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Duration;

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use regex::Regex;
use serde::{Deserialize, Serialize};
use sha2_core::sha::{MessageBlock, OutputHash, StartVector, Word};
use sha2_core::structs::collision_type::CollisionType;
use sha2_core::structs::hash_function::HashFunction;
use sha2_core::structs::sha_state::ShaState;
use sha2_smt::smt_lib::smt_retriever::EncodingType;
use sha2_verify::colliding_pair::{CollidingPair, MessageData};

#[derive(
	Copy,
	Clone,
	Debug,
	Serialize,
	Deserialize,
	Eq,
	PartialEq,
	Hash,
	Ord,
	PartialOrd
)]
pub enum SmtSolver {
	Z3,
	CVC5,
	Yices2,
	Bitwuzla,
	Boolector,
	Colibri2,
	MathSAT
}

impl FromStr for SmtSolver {
	type Err = ParseSmtSolverError;

	fn from_str(s : &str) -> Result<Self, Self::Err> {
		match s {
			"z3" => Ok(SmtSolver::Z3),
			"cvc5" => Ok(SmtSolver::CVC5),
			"yices2" => Ok(SmtSolver::Yices2),
			"bitwuzla" => Ok(SmtSolver::Bitwuzla),
			"boolector" => Ok(SmtSolver::Boolector),
			"colibri2" => Ok(SmtSolver::Colibri2),
			"math-sat" => Ok(SmtSolver::MathSAT),
			_ => Err(ParseSmtSolverError(s.to_string()))
		}
	}
}

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
#[error(
	"unknown solver '{0}', expected one of: z3, cvc5, yices2, bitwuzla, boolector, colibri2, math-sat"
)]
pub struct ParseSmtSolverError(String);

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn parses_all_variants() {
		assert_eq!(SmtSolver::from_str("z3"), Ok(SmtSolver::Z3));
		assert_eq!(SmtSolver::from_str("cvc5"), Ok(SmtSolver::CVC5));
		assert_eq!(SmtSolver::from_str("yices2"), Ok(SmtSolver::Yices2));
		assert_eq!(SmtSolver::from_str("bitwuzla"), Ok(SmtSolver::Bitwuzla));
		assert_eq!(SmtSolver::from_str("boolector"), Ok(SmtSolver::Boolector));
		assert_eq!(SmtSolver::from_str("colibri2"), Ok(SmtSolver::Colibri2));
		assert_eq!(SmtSolver::from_str("math-sat"), Ok(SmtSolver::MathSAT));
	}

	#[test]
	fn rejects_unknown() {
		assert!(SmtSolver::from_str("Z3").is_err());
		assert!(SmtSolver::from_str("stp").is_err());
		assert!(SmtSolver::from_str("").is_err());
	}

	#[test]
	fn unknown_solver_lists_expected_variants() {
		let err = SmtSolver::from_str("stp").unwrap_err().to_string();

		for variant in [
			"z3",
			"cvc5",
			"yices2",
			"bitwuzla",
			"boolector",
			"colibri2",
			"math-sat"
		] {
			assert!(
				err.contains(variant),
				"error text {err:?} missing variant {variant}"
			);
		}
	}

	#[test]
	fn load_missing_file_reports_path() {
		let missing = Path::new("/nonexistent-dir/missing-benchmark.json");
		let err = Benchmark::load(missing).unwrap_err();

		assert!(
			format!("{err:#}").contains(&missing.display().to_string()),
			"error {err:#?} missing path {}",
			missing.display()
		);
	}

	#[test]
	fn parse_output_rejects_malformed_sat_output() {
		let mut benchmark = sat_benchmark_with_output("(hash0 #x)");
		let err = benchmark.parse_output().unwrap_err();
		let message = format!("{err:#}");

		assert!(
			message.contains("failed to decode solver output value"),
			"error {message:?} missing decode context"
		);
		assert!(
			message.contains("Z3"),
			"error {message:?} missing solver name"
		);
	}

	fn sat_benchmark_with_output(output : &str) -> Benchmark {
		Benchmark {
			date_time : Utc::now(),
			solver : SmtSolver::Z3,
			arguments : None,
			hash_function : HashFunction::SHA256,
			rounds : 1,
			collision_type : CollisionType::Standard,
			execution_time : Duration::from_secs(1),
			memory_bytes : 0,
			result : BenchmarkResult::Sat,
			console_output : (output.to_string(), String::new()),
			is_valid : None,
			is_baseline : false,
			is_rerun : false,
			encoding : EncodingType::BruteForce {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			},
			stop_tolerance : 0,
			timeout : Duration::from_secs(60)
		}
	}
}

impl Display for SmtSolver {
	fn fmt(&self, f : &mut Formatter<'_>) -> std::fmt::Result {
		use SmtSolver::*;

		write!(
			f,
			"{}",
			match self {
				Z3 => "Z3",
				CVC5 => "cvc5",
				Yices2 => "Yices2",
				Bitwuzla => "Bitwuzla",
				Boolector => "Boolector",
				Colibri2 => "Colibri2",
				MathSAT => "MathSAT"
			}
		)
	}
}

impl SmtSolver {
	pub fn command(&self) -> String {
		use SmtSolver::*;

		match self {
			Z3 => "z3",
			CVC5 => "cvc5",
			Yices2 => "yices-smt2",
			Bitwuzla => "bitwuzla",
			Boolector => "boolector",
			Colibri2 => "./solvers/colibri2",
			MathSAT => "./solvers/mathsat"
		}
		.into()
	}
}

pub type SolverArg = String;

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq, Clone)]
pub enum BenchmarkResult {
	Sat,
	Unsat,
	MemOut,
	CPUOut,
	Aborted,
	SMTError,
	Unknown
}

impl Display for BenchmarkResult {
	fn fmt(&self, f : &mut Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				BenchmarkResult::Sat => "SAT",
				BenchmarkResult::Unsat => "UNSAT",
				BenchmarkResult::MemOut => "OUT OF MEMORY",
				BenchmarkResult::CPUOut => "OUT OF CPU TIME",
				BenchmarkResult::Aborted => "ABORTED",
				BenchmarkResult::SMTError => "SMT ERROR",
				BenchmarkResult::Unknown => "UNKNOWN"
			}
		)
	}
}

#[derive(Clone, Copy)]
enum SmtOutputFormat {
	Boolean,
	Hex,
	Decimal
}

impl SmtOutputFormat {
	fn output_string(self) -> String {
		match self {
			SmtOutputFormat::Boolean => "#b([01]*)",
			SmtOutputFormat::Hex => "#x([0-9a-fA-F]*)",
			SmtOutputFormat::Decimal => "([0-9]*)"
		}
		.to_string()
	}

	fn get_base_size(self, capture : &str, hash_function : HashFunction) -> Result<Word> {
		let radix_size = match self {
			SmtOutputFormat::Boolean => 2,
			SmtOutputFormat::Hex => 16,
			SmtOutputFormat::Decimal => 10
		};

		Word::from_str_radix(capture, radix_size, hash_function).with_context(|| {
			format!(
				"failed to parse solver output value {capture:?} with radix {radix_size} for {hash_function}"
			)
		})
	}
}

#[derive(Debug, PartialEq, Clone, Default)]
pub struct MutableShaState {
	pub i : u8,
	pub w : Option<Word>,
	pub a : Option<Word>,
	pub e : Option<Word>
}

impl MutableShaState {
	fn to_immutable(&self) -> Option<ShaState> {
		Some(ShaState {
			i : self.i,
			w : self.w?,
			a : self.a?,
			e : self.e?
		})
	}

	fn update_state_variable(&mut self, variable : char, value : Word) {
		match variable {
			'a' => self.a = Some(value),
			'e' => self.e = Some(value),
			'w' => self.w = Some(value),
			_ => {}
		}
	}
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub struct Benchmark {
	pub date_time : DateTime<Utc>,
	pub solver : SmtSolver,
	pub arguments : Option<SolverArg>,
	pub hash_function : HashFunction,
	pub rounds : u8,
	pub collision_type : CollisionType,
	pub execution_time : Duration,
	pub memory_bytes : u64,
	pub result : BenchmarkResult,
	pub console_output : (String, String),
	pub is_valid : Option<bool>,
	pub is_baseline : bool,
	pub is_rerun : bool,
	pub encoding : EncodingType,
	pub stop_tolerance : u8,
	pub timeout : Duration
}

impl Benchmark {
	pub fn save(&self, path : &Path) -> Result<PathBuf> {
		if !path.exists() {
			fs::create_dir_all(path).with_context(|| {
				format!(
					"failed to create benchmark save directory {}",
					path.display()
				)
			})?;
		}

		let path = path.join(format!(
			"{}_{}_{}_{}_{}.json",
			self.hash_function, self.collision_type, self.solver, self.rounds, self.date_time,
		));

		let mut file = File::options()
			.create_new(true)
			.write(true)
			.open(path.clone())
			.with_context(|| format!("failed to create benchmark file {}", path.display()))?;

		let json = serde_json::to_string(&self).with_context(|| {
			format!(
				"failed to serialize benchmark (solver {}, encoding {})",
				self.solver,
				String::from(self.encoding)
			)
		})?;
		file.write_all(json.as_bytes())
			.with_context(|| format!("failed to write benchmark file {}", path.display()))?;

		Ok(path)
	}

	pub fn load(file : &Path) -> Result<Self> {
		let contents = fs::read(file)
			.with_context(|| format!("failed to read benchmark file {}", file.display()))?;
		let benchmark : Self = serde_json::from_slice(&contents)
			.with_context(|| format!("failed to parse benchmark file {}", file.display()))?;
		Ok(benchmark)
	}

	pub fn load_all(dir_location : &Path, recursively : bool) -> Result<Vec<Self>> {
		let mut benchmarks = vec![];

		if dir_location.is_file() {
			benchmarks.push(Self::load(dir_location)?);
			return Ok(benchmarks);
		}

		for dir_entry in fs::read_dir(dir_location)
			.with_context(|| {
				format!(
					"failed to read benchmark directory {}",
					dir_location.display()
				)
			})?
			.flatten()
		{
			let metadata = dir_entry.metadata().with_context(|| {
				format!("failed to read metadata for {}", dir_entry.path().display())
			})?;
			if recursively && metadata.is_dir() {
				benchmarks.extend(Self::load_all(&dir_entry.path(), recursively)?)
			} else if metadata.is_file() {
				benchmarks.push(Self::load(&dir_entry.path())?);
			}
		}

		Ok(benchmarks)
	}

	pub fn parse_output(&mut self) -> Result<Option<CollidingPair>> {
		if self.result != BenchmarkResult::Sat {
			return Ok(None);
		}

		let output_format = self.get_output_format();
		let number_format = output_format.output_string();
		let re = Regex::new(&format!(
			r"\((?:m([01])_|)(delta_[aew]|[a-hw]|hash)([0-9]+) (?:\(_ bv{number_format} (?:32|64)\)|{number_format})\)",
		))
		.with_context(|| {
			format!(
				"failed to compile solver output pattern for {} encoding (solver {})",
				String::from(self.encoding),
				self.solver
			)
		})?;

		let (smt_output, _) = self.console_output.clone();
		let default_word = self.hash_function.default_word();

		let mut hash = Box::new([None; 8]);
		let mut start_blocks = [[default_word; 16]; 2];
		let mut start_vectors = [[default_word; 8]; 2];
		let mut states = [BTreeMap::new(), BTreeMap::new()];

		for capture in re.captures_iter(&smt_output) {
			let msg = capture.get(1);
			let var = &capture[2];
			let round : usize = capture[3].parse().with_context(|| {
				format!(
					"failed to parse solver output round {:?} (solver {})",
					&capture[3], self.solver
				)
			})?;

			let val = match (capture.get(4), capture.get(5)) {
				(Some(val), _) => val,
				(_, Some(val)) => val,
				(None, None) => {
					return Err(anyhow::anyhow!(
						"failed to retrieve solver output value (solver {})",
						self.solver
					));
				}
			};
			let val = output_format
				.get_base_size(val.into(), self.hash_function)
				.with_context(|| {
					format!(
						"failed to decode solver output value for {var}{round} (solver {})",
						self.solver
					)
				})?;

			let is_differential = var.contains("delta");

			match msg {
				Some(msg) => {
					let msg_index : usize = msg.as_str().parse().with_context(|| {
						format!(
							"failed to parse solver output message {:?} (solver {})",
							msg.as_str(),
							self.solver
						)
					})?;
					self.parse_update_for_msg(
						msg_index,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
						is_differential
					)?;
				}
				None => {
					self.parse_update_for_msg(
						0,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
						is_differential
					)?;
					self.parse_update_for_msg(
						1,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
						is_differential
					)?;
				}
			}
		}

		// Trim hash
		let output_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut trimmed_hash = Vec::with_capacity(output_size);
		for (i, word) in hash.into_iter().enumerate() {
			if let Some(word) = word {
				trimmed_hash.push(word);
			} else if i == output_size {
				break;
			}
		}

		// Process messages
		let mut messages = vec![];
		for (i, message_states) in states.into_iter().enumerate() {
			let mut states = vec![];
			for (_, mut state) in message_states {
				if self.rounds == 0 {
					state.w = Some(self.hash_function.default_word());
				}

				states.push(state.to_immutable().ok_or_else(|| {
					anyhow::anyhow!(
						"failed to retrieve all message states (solver {}, {} rounds)",
						self.solver,
						self.rounds
					)
				})?);
			}

			messages.push(MessageData {
				m : MessageBlock(start_blocks[i]),
				cv : StartVector::CV(start_vectors[i]),
				states,
				expected_hash : OutputHash(Box::from(trimmed_hash.clone()))
			});
		}

		let [m0, m1] = messages.try_into().map_err(|messages : Vec<MessageData>| {
			anyhow::anyhow!(
				"expected 2 colliding messages, parsed {} (solver {})",
				messages.len(),
				self.solver
			)
		})?;
		let colliding_pair = CollidingPair {
			m0,
			m1,
			hash_function : self.hash_function,
			rounds : self.rounds
		};

		// Verify benchmark
		self.is_valid = Some(colliding_pair.verify().with_context(|| {
			format!("failed to verify colliding pair (solver {})", self.solver)
		})?);

		Ok(Some(colliding_pair))
	}

	#[allow(clippy::too_many_arguments)]
	fn parse_update_for_msg(
		&self,
		msg : usize,
		var : &str,
		round : usize,
		val : Word,
		hash : &mut Box<[Option<Word>; 8]>,
		start_blocks : &mut [[Word; 16]; 2],
		start_vectors : &mut [[Word; 8]; 2],
		states : &mut [BTreeMap<usize, MutableShaState>; 2],
		differential : bool
	) -> Result<()> {
		// Special handling if differential
		let (var, val) = if differential {
			let var = var.split("_").nth(1).ok_or_else(|| {
				anyhow::anyhow!(
					"failed to parse differential variable {var:?} (solver {})",
					self.solver
				)
			})?;
			let val = if msg == 0 {
				val
			} else {
				self.hash_function.default_word()
			};

			(var, val)
		} else {
			(var, val)
		};

		// Parse
		if var == "hash" {
			let slot = hash.get_mut(round).ok_or_else(|| {
				anyhow::anyhow!(
					"solver output round {round} out of range for hash (solver {})",
					self.solver
				)
			})?;
			*slot = Some(val);
		} else {
			let var_char : char = var.parse().with_context(|| {
				format!(
					"failed to parse state variable {var:?} (solver {})",
					self.solver
				)
			})?;

			// Parse H constants (CV/IV)
			if !differential && round == 0 && var_char != 'w' {
				let i = (var_char as u32 - u32::from(b'a')) as u8;
				start_vectors[msg][i as usize] = val;
			}

			// Parse start blocks
			if !differential && var_char == 'w' && round < 16 {
				start_blocks[msg][round] = val;
			}

			// Upsert updated state
			states[msg]
				.entry(round)
				.and_modify(|state| {
					state.update_state_variable(var_char, val);
				})
				.or_insert_with(|| {
					let mut state = MutableShaState {
						i : round as u8,
						..Default::default()
					};
					state.update_state_variable(var_char, val);
					state
				});
		}
		Ok(())
	}

	fn get_output_format(&self) -> SmtOutputFormat {
		let (smt_output, _) = &self.console_output;
		if smt_output.contains("#b") {
			SmtOutputFormat::Boolean
		} else if smt_output.contains("#x") {
			SmtOutputFormat::Hex
		} else {
			SmtOutputFormat::Decimal
		}
	}
}
