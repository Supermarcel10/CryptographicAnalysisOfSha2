use std::time::Duration;
use serde::{Deserialize, Serialize};
use crate::sha::StartVector;
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
	Pass,
	Fail,
	MemOut,
	CPUOut,
}

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct Benchark {
	pub solver: Solver,
	pub parameters: Vec<SolverArg>,
	pub hash_function: HashFunction,
	pub compression_rounds: u8,
	pub start_vector: StartVector,
	pub time: Duration,
	pub memory_bytes: u64,
	pub result: BenchmarkResult,
}
