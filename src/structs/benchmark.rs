use std::time::Duration;
use serde::{Deserialize, Serialize};
use crate::sha::StartVector;
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum Solver {
	Z3,
	CVC5,
	Yices2,
	Bitwuzla,
	Boolector,
}

impl Solver {
	pub fn command(&self) -> String {
		// TODO: Figure out how to make this reproducible on all systems.
		match self {
			Solver::Z3 => "z3",
			Solver::CVC5 => "cvc5",
			Solver::Yices2 => "yices",
			Solver::Bitwuzla => "bitwuzla",
			Solver::Boolector => "boolector",
		}.into()
	}
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

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct Benchark {
	pub solver: Solver,
	pub arguments: Vec<SolverArg>,
	pub hash_function: HashFunction,
	pub rounds: u8,
	pub collision_type: CollisionType,
	pub execution_time: Duration,
	pub memory_bytes: u64,
	pub result: BenchmarkResult,
	pub console_output: String,
}
