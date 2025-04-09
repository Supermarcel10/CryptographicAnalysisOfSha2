use std::collections::BTreeMap;
use std::error::Error;
use std::path::PathBuf;
use crate::BENCHMARK_SAVE_PATH_DEFAULT;
use crate::structs::benchmark::{Benchmark, SmtSolver, SolverArg};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


pub struct DataRetriever {
	data_location: PathBuf,
}

impl DataRetriever {
	pub fn new(data_location: PathBuf) -> Self {
		DataRetriever {
			data_location,
		}
	}

	pub fn default() -> Self {
		DataRetriever {
			data_location: PathBuf::from(*BENCHMARK_SAVE_PATH_DEFAULT),
		}
	}

	fn retrieve_all(&self) -> Result<Vec<Benchmark>, Box<dyn Error>> {
		Benchmark::load_all(&self.data_location, true)
	}

	pub fn retrieve_all_baselines(
		&self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		prefer_test_reruns: bool, // TODO: Implement!
	) -> Result<Vec<Benchmark>, Box<dyn Error>> {
		let benchmarks = Benchmark::load_all(
			&self.data_location.join("brute-force"),
			false
		)?;

		Ok(
			benchmarks
				.into_iter()
				.filter(|b| b.hash_function == hash_function)
				.filter(|b| b.collision_type == collision_type)
				.filter(|b| b.arguments.is_empty())
				.collect()
		)
	}

	pub fn retrieve_baseline(
		&self,
		solver: SmtSolver,
		hash_function: HashFunction,
		collision_type: CollisionType,
		prefer_anomalnies: bool,
	) -> Result<Vec<Benchmark>, Box<dyn Error>> {
		let all_baselines = self.retrieve_all_baselines(
			hash_function,
			collision_type,
			prefer_anomalnies
		)?;

		Ok(
			all_baselines
				.into_iter()
				.filter(|b| b.solver == solver)
				.collect()
		)
	}

	pub fn retrieve_with_args(
		&self,
		solver: SmtSolver,
		hash_function: HashFunction,
		collision_type: CollisionType,
		prefer_test_reruns: bool, // TODO: Implement!
		arg_identifier: &str,
	) -> Result<BTreeMap<Vec<SolverArg>, Vec<Benchmark>>, Box<dyn Error>> {
		let benchmarks = self.retrieve_all()?;

		fn has_similar_arg(benchmark: &Benchmark, identifier: &str) -> bool {
			benchmark.arguments.iter().any(|arg| arg.contains(identifier))
		}

		let filtered: Vec<_> = benchmarks
			.into_iter()
			.filter(|b| b.solver == solver)
			.filter(|b| b.hash_function == hash_function)
			.filter(|b| b.collision_type == collision_type)
			.filter(|b| has_similar_arg(b, arg_identifier))
			.collect();

		let mut map = BTreeMap::new();
		for benchmark in filtered {
			let key = benchmark.arguments.clone();
			map.entry(key)
				.or_insert_with(Vec::new)
				.push(benchmark);
		}

		Ok(map)
	}
}
