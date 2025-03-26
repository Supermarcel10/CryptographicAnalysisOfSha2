use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;
use chrono::{DateTime, Utc};
use regex::Regex;
use serde::{Deserialize, Serialize};
use crate::sha::{MessageBlock, OutputHash, StartVector, Word};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;
use crate::{update_state_variable, MutableShaState};
use crate::verification::colliding_pair::{CollidingPair, MessageData};

#[derive(Copy, Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum SmtSolver {
	Z3,
	CVC5,
	Yices2,
	Bitwuzla,
	Boolector,
	STP,
	// Colibri, // TODO: Figure out how to install this thing
}

// TODO: TO TEST:
// Z3:
// core.minimize (bool) minimize computed core (default: false)
//    bce (bool) eliminate blocked clauses (default: false)
//    ate (bool) asymmetric tautology elimination (default: true)
//    abce (bool) eliminate blocked clauses using asymmetric literals (default: false)
//     acce (bool) eliminate covered clauses using asymmetric added literals (default: false)
//     anf (bool) enable ANF based simplification in-processing (default: false)
//    binspr (bool) enable SPR inferences of binary propagation redundant clauses. This inprocessing step eliminates models (default: false)
//    cce (bool) eliminate covered clauses (default: false)
//		cut (bool) enable AIG based simplification in-processing (default: false)
//    threads (unsigned int) number of parallel threads to use (default: 1)
//    cancel_backup_file (symbol) file to save partial search state if search is canceled (default: )
//		enable_sls (bool) enable SLS tuning during weighted maxsat (default: false)
//    enable (bool) enable parallel solver by default on selected tactics (for QF_BV) (default: false)
//    check_lemmas (bool) check lemmas on the fly using an independent nlsat solver (default: false)
//    blast_distinct (bool) expand a distinct predicate into a quadratic number of disequalities (default: false)
//    blast_eq_value (bool) blast (some) Bit-vector equalities into bits (default: false)
//    bv_extract_prop (bool) attempt to partially propagate extraction inwards (default: false)
//    bv_not_simpl (bool) apply simplifications for bvnot (default: false)
//		bv_sort_ac (bool) sort the arguments of all AC operators (default: false)
//    elim_and (bool) conjunctions are rewritten using negation and disjunctions (default: false)
//[module] sls, description: Experimental Stochastic Local Search Solver (for QFBV only).
//

// CVC5:
//  --arith-rewrite-equalities
//                          turns on the preprocessing rewrite turning equalities
//                          into a conjunction of inequalities [*]
//   --arith-static-learning
//                          do arithmetic static learning for ite terms based on
//                          bounds when static learning is enabled [*]
//   --dio-solver           turns on Linear Diophantine Equation solver (Griggio,
//                          JSAT 2012) (EXPERTS only) [*]
//  --dio-decomps          let skolem variables for integer divisibility
//                          constraints leak from the dio solver (EXPERTS only) [*]
//  --new-prop             use the new row propagation system (EXPERTS only) [*]
//  --nl-cov               whether to use the cylindrical algebraic coverings
//                          solver for non-linear arithmetic [*]
//  --use-approx           attempt to use an approximate solver (EXPERTS only) [*]
//  --use-fcsimplex        use focusing and converging simplex (FMCAD 2013
//                          submission) (EXPERTS only) [*]
//   --use-soi              use sum of infeasibility simplex (FMCAD 2013
//                          submission) (EXPERTS only) [*]
//  --plugin-share-skolems true if we permit sharing theory lemmas and SAT clauses
//                          with skolems (EXPERTS only) [*]
//  --bitblast=MODE        choose bitblasting mode, see --bitblast=help
//  --bool-to-bv=MODE      convert booleans to bit-vectors of size 1 at various
//                          levels of aggressiveness, see --bool-to-bv=help
//  --bv-assert-input      assert input assertions on user-level 0 instead of
//                          assuming them in the bit-vector SAT solver (EXPERTS
//                          only) [*]
//  --bv-eager-eval        perform eager context-dependent evaluation for
//                          applications of bv kinds in the equality engine [*]
//  --bv-eq-engine         enable equality engine when possible in bitvector
//                          theory (EXPERTS only) [*]
//   --bv-gauss-elim        simplify formula via Gaussian Elimination if applicable
//                          (EXPERTS only) [*]
//   --bv-propagate         use bit-vector propagation in the bit-blaster (EXPERTS
//                          only) [*]
//   --bv-rw-extend-eq      enable additional rewrites over zero/sign extend over
//                          equalities with constants (useful on
//                          BV/2017-Preiner-scholl-smt08) (EXPERTS only) [*]
//   --bv-sat-solver=MODE   choose which sat solver to use, see
//                          --bv-sat-solver=help
//   --bv-solver=MODE       choose bit-vector solver, see --bv-solver=help
//  --minisat-simplification=MODE
//                          Simplifications to be performed by Minisat. (EXPERTS
//                          only)

// TODO: Yices2

// Bitwuzla:
//  --bv-solver preprop
// --pp-elim-extracts                [false]      eliminate extract on BV constants
// --pp-elim-bvudiv                  [false]      eliminate bvudiv and bvurem
// --pp-contr-ands                   [false]      enable contradicting ands preprocessing pass
//   --abstraction-bvadd               [false]      term abstraction for bvadd
//  --abstraction-initial-lemmas      [false]      use initial lemma refinements only
//   --abstraction-inc-bitblast        [false]      incrementally bit-blast bvmul and bvadd
//  --abstraction                     [false]      enable abstraction module
// --prop-normalize                  [false]      enable normalization for local search
//   -S <M>, --sat-solver <M>          [cadical]    backend SAT solver {kissat, cms, cadical}

// TODO: Boolector

// TODO: STP

impl Display for SmtSolver {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		use SmtSolver::*;

		write!(f, "{}", match self {
			Z3 => "z3",
			CVC5 => "cvc5",
			Yices2 => "yices",
			Bitwuzla => "bitwuzla",
			Boolector => "boolector",
			STP => "stp",
		})
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
			STP => "stp",
		}.into()
	}
}

pub enum SatSolver {
	CryptoMiniSat,
	Glucose,
	GlucoseSyrup,
	CreuSAT,
	Varisat,
}

pub type SolverArg = String;

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum BenchmarkResult {
	Sat,
	Unsat,
	MemOut,
	CPUOut,
	Aborted,
	SMTError,
	Unknown,
}

impl Display for BenchmarkResult {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", match self {
			BenchmarkResult::Sat => "SAT",
			BenchmarkResult::Unsat => "UNSAT",
			BenchmarkResult::MemOut => "OUT OF MEMORY",
			BenchmarkResult::CPUOut => "OUT OF CPU TIME",
			BenchmarkResult::Aborted => "ABORTED",
			BenchmarkResult::SMTError => "SMT ERROR",
			BenchmarkResult::Unknown => "UNKNOWN",
		})
	}
}

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct Benchark {
	pub date_time: DateTime<Utc>,
	pub solver: SmtSolver,
	pub arguments: Vec<SolverArg>,
	pub hash_function: HashFunction,
	pub rounds: u8,
	pub collision_type: CollisionType,
	pub execution_time: Duration,
	pub memory_bytes: u64,
	pub result: BenchmarkResult,
	pub console_output: (String, String),
}

impl Benchark {
	pub fn save(&self) -> Result<PathBuf, Box<dyn Error>> {
		let path = PathBuf::from(
			format!("results/{}_{}_{}_{}_{}.json",
					self.solver,
					self.collision_type,
					self.hash_function,
					self.rounds,
					self.date_time.format("%Y%m%d_%H:%M"),
			));

		let mut file = File::create(path.clone())?;
		let json = serde_json::to_string(&self)?;
		file.write_all(json.as_bytes())?;

		Ok(path)
	}

	pub fn parse_output(self) -> Result<Option<CollidingPair>, Box<dyn Error>> {
		if self.result != BenchmarkResult::Sat {
			return Ok(None);
		}

		let (smt_output, _) = self.console_output;
		let re = Regex::new(r"\((?:m([01])_|)([a-hw]|hash)([0-9]+) #b([01]*)\)")?;
		let default_word = self.hash_function.default_word();

		let mut hash = Box::new([default_word; 8]);
		let mut start_blocks = [[default_word; 16]; 2];
		let mut start_vectors = [[default_word; 8]; 2];
		let mut states = [BTreeMap::new(), BTreeMap::new()];

		for capture in re.captures_iter(&smt_output) {
			let msg= capture.get(1);
			let var = &capture[2];
			let round: usize = capture[3].parse()?;
			let val = Word::from_str_radix(&capture[4], 2, self.hash_function)?;

			match msg {
				Some(msg) => {
					Self::parse_update_for_msg(
						msg.as_str().parse()?,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
					)?;
				}
				None => {
					Self::parse_update_for_msg(
						0,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
					)?;
					Self::parse_update_for_msg(
						1,
						var,
						round,
						val,
						&mut hash,
						&mut start_blocks,
						&mut start_vectors,
						&mut states,
					)?;
				}
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
		Ok(Some(CollidingPair {
			m0,
			m1,
			verified_hash: None,
		}))
	}

	fn parse_update_for_msg(
		msg: usize,
		var: &str,
		round: usize,
		val: Word,
		mut hash: &mut Box<[Word; 8]>,
		mut start_blocks: &mut [[Word; 16]; 2],
		mut start_vectors: &mut [[Word; 8]; 2],
		mut states: &mut [BTreeMap<usize, MutableShaState>; 2],
	) -> Result<(), Box<dyn Error>> {
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
		Ok(())
	}
}
