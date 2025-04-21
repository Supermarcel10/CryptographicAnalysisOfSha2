use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::path::PathBuf;
use crate::structs::benchmark::{Benchmark, SmtSolver, SolverArg};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


pub struct DataRetriever {
	data_dir: PathBuf,
	all_results: Option<Vec<Benchmark>>,
}

impl DataRetriever {
	pub fn new(data_dir: PathBuf) -> Result<Self, Box<dyn Error>> {
		if !data_dir.exists() {
			fs::create_dir_all(data_dir.clone())?;
		}

		Ok(DataRetriever {
			data_dir,
			all_results: None,
		})
	}

	#[allow(dead_code)]
	pub fn default() -> Result<Self, Box<dyn Error>> {
		DataRetriever::new(PathBuf::from("results/"))
	}

	fn cache_all(&mut self) -> Result<(), Box<dyn Error>> {
		let benchmarks: Vec<_> = Benchmark::load_all(&self.data_dir, true)?
			.into_iter()
			.filter(|b| b.is_valid != Some(false))
			.collect();

		if !benchmarks.is_empty() {
			self.all_results = Some(benchmarks);
		}

		Ok(())
	}

	pub fn retrieve_all_baselines(
		&mut self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		prefer_test_reruns: bool,
	) -> Result<Vec<Benchmark>, Box<dyn Error>> {
		if self.all_results.is_none() {
			self.cache_all()?;
		}

		let mut baselines = Vec::new();
		let mut reruns = Vec::new();
		for b in self.all_results.clone().unwrap() {
			if b.is_baseline
				&& b.hash_function == hash_function
				&& b.collision_type == collision_type
				&& b.arguments.is_empty()
			{
				if b.is_rerun {
					reruns.push(b);
				} else {
					baselines.push(b);
				}
			}
		}

		if prefer_test_reruns {
			substitute_reruns(&mut baselines, reruns);
		}

		Ok(baselines)
	}

	pub fn retrieve_baseline(
		&mut self,
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
		&mut self,
		solver: SmtSolver,
		hash_function: HashFunction,
		collision_type: CollisionType,
		prefer_test_reruns: bool,
		arg_identifier: &str,
	) -> Result<BTreeMap<Vec<SolverArg>, Vec<Benchmark>>, Box<dyn Error>> {
		if self.all_results.is_none() {
			self.cache_all()?;
		}

		fn has_similar_arg(benchmark: &Benchmark, identifier: &str) -> bool {
			benchmark.arguments.iter().any(|arg| arg.contains(identifier))
		}

		let mut baselines = Vec::new();
		let mut reruns = Vec::new();
		for b in self.all_results.clone().unwrap() {
			if b.solver == solver
				&& b.hash_function == hash_function
				&& b.collision_type == collision_type
				&& has_similar_arg(&b, arg_identifier)
			{
				if b.is_rerun {
					reruns.push(b);
				} else {
					baselines.push(b);
				}
			}
		}

		if prefer_test_reruns {
			substitute_reruns(&mut baselines, reruns);
		}

		let mut map = BTreeMap::new();
		for benchmark in baselines {
			let key = benchmark.arguments.clone();
			map.entry(key)
				.or_insert_with(Vec::new)
				.push(benchmark);
		}

		Ok(map)
	}
}

fn substitute_reruns(
	baselines: &mut Vec<Benchmark>,
	reruns: Vec<Benchmark>,
) {
	for rerun in reruns.into_iter() {
		for baseline in baselines.iter_mut() {
			if baseline.rounds == rerun.rounds
				&& baseline.collision_type == rerun.collision_type
				&& baseline.hash_function == rerun.hash_function
				&& baseline.solver == rerun.solver
			{
				*baseline = rerun;
				break;
			}
		}
	}
}
