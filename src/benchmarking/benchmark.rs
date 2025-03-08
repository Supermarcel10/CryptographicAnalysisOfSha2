use crate::sha::{HashFunction, StartVector, Word};
use std::time::Duration;
use serde::{Deserialize, Serialize};

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

#[cfg(test)]
mod tests {
	use std::time::Duration;
	use super::Benchark;
	use super::BenchmarkResult::*;
	use super::Solver::*;
	use crate::sha::HashFunction::*;
	use crate::sha::StartVector::IV;

	const BENCHMARK_OBJ: Benchark<u32> = Benchark {
		solver: Z3,
		parameters: vec![],
		hash_function: SHA256,
		compression_rounds: 64,
		start_vector: IV,
		time: Duration::from_millis(1000),
		memory_bytes: 100,
		result: Pass,
	};

	const BENCHMARK_JSON: &str = r#"{"solver":"Z3","parameters":[],"hash_function":"SHA256","compression_rounds":64,"start_vector":"IV","time":{"secs":1,"nanos":0},"memory_bytes":100,"result":"Pass"}"#;

	#[test]
	fn test_serialization() {
		let result = serde_json::to_string(&BENCHMARK_OBJ).unwrap();
		assert_eq!(result, BENCHMARK_JSON);
	}

	#[test]
	fn test_deserialization() {
		let result: Benchark<u32> = serde_json::from_str(BENCHMARK_JSON).unwrap();
		assert_eq!(result, BENCHMARK_OBJ);
	}
}
