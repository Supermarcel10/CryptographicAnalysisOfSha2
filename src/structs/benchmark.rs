use std::time::Duration;
use serde::{Deserialize, Serialize};
use crate::sha::{StartVector, Word};
use crate::structs::hash_function::HashFunction;

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum Solver {
	Z3,
	CVC5,
	Yices2,
	Bitwuzla,
	Boolector,
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
pub struct Benchark<W: Word> {
	pub solver: Solver,
	pub parameters: Vec<SolverArg>,
	pub hash_function: HashFunction,
	pub compression_rounds: u8,
	pub start_vector: StartVector<W>,
	pub time: Duration,
	pub memory_bytes: u64,
	pub result: BenchmarkResult,
}
