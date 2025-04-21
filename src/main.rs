use std::error::Error;
use std::fs;
use std::ops::Range;
use std::path::{PathBuf};
use std::time::{Duration};
use clap::{Parser, Subcommand};
use plotters::prelude::RGBColor;
use crate::benchmark::runner::BenchmarkRunner;
use crate::data::data_retriever::DataRetriever;
use crate::graphing::graph_renderer::GraphRenderer;
use crate::sha::{MessageBlock, Sha, StartVector, Word};
use crate::smt_lib::smt_lib::generate_smtlib_files;
use crate::smt_lib::smt_retriever::{EncodingType, SmtRetriever};
use crate::structs::benchmark::{Benchmark, SmtSolver};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;

#[cfg(not(unix))]
compile_error!("This crate supports only Unix-like operating systems");

mod smt_lib;
mod sha;
mod verification;
mod structs;
mod graphing;
mod data;
mod benchmark;


#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
	#[command(subcommand)]
	command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
	/// Generate SMTLIB 2.6 standard files
	Generate {
		/// Directory where smt2 files will be saved. Default `smt/`
		#[arg(short = 'S', long)]
		smt_dir: Option<PathBuf>,
	},

	/// Run an exhaustive benchmark over all solvers, hash functions, collision types and arguments
	Benchmark {
		/// Argument to select solver. Use multiple `--solver <SOLVER>` statements for multiple solvers
		#[arg(required = true, long)]
		solver: Vec<SmtSolver>,

		/// Argument to select hash function. Use separate `--hash-function <HASH_FUNCTION>` statements for multiple hash functions
		#[arg(required = true, long)]
		hash_function: Vec<HashFunction>,

		/// Argument to select collision type. Use separate `--collision-type <COLLISION_TYPE>` statements for multiple collision types
		#[arg(required = true, long)]
		collision_type: Vec<CollisionType>,

		/// Argument to set (non-inclusive) range of compression rounds. Input with `--round-range <MIN>..<MAX>`. Default 1..hash function max
		#[arg(long, value_parser = parse_range)]
		round_range: Option<Range<u8>>,

		/// Argument to set the solver argument sets (combinations of solver arguments).
		/// An arugment set can contain multiple arguments which will all be executed on the solver.
		/// To test each argument separately, set each solver argument as a separate --arg-set.
		/// Use separate `--arg-set "<ARG_SET>"` statements for multiple argument sets.
		/// Default <No Args>
		#[arg(long, allow_hyphen_values = true)]
		arg_set: Option<Vec<String>>,

		/// The number of required sequential failures to stop. Default 3
		#[arg(short, long)]
		stop_tolerance:  Option<u8>,

		/// Duration after which run is marked as timed out. Default 15 mins
		#[arg(short, long)]
		timeout_sec: Option<u64>,

		/// Path to directory containing SMT files. Default `smt/`
		#[arg(short = 'S', long)]
		smt_dir: Option<PathBuf>,

		/// Path to directory where result files will be saved to. `None` to disable output. Default `results/`
		#[arg(short, long)]
		result_dir: Option<PathBuf>,

		/// Should remaining benchmark runs continue despite error on one. Default false
		#[arg(short = 'C', visible_alias = "cof", long)]
		continue_on_fail: Option<bool>,

		/// Type of encoding to benchmark. Default bruteforce
		#[arg(short = 'E', long)]
		encoding_type: Option<EncodingType>,

		/// Should the benchmark be marked as a rerun. Useful for flagging up anomalies. Default false
		#[arg(short = 'R', long)]
		is_rerun: Option<bool>,
	},

	/// Run the underlying sha2 function
	Sha2 {
		/// Message to hash
		#[arg(short, long)]
		msg: Option<String>,

		/// Message digest block to hash (pre-padded and pre-processed digest), separated word-by-word with spaces
		#[arg(short = 'M', visible_alias = "mb", long)]
		msg_block: Option<String>,

		/// Hash function
		hash_function: HashFunction,

		/// Number of compression rounds. Default hash function max
		#[arg(short, long)]
		rounds: Option<u8>,

		/// Starting vector for hash function, separated word-by-word with spaces. Default Initial Vector (IV)
		#[arg(long, visible_alias = "sv")]
		start_vector: Option<String>,
	},

	/// Load, verify and display result files
	Load {
		/// Path to a result file, or a directory. Default `results/`
		#[arg(short = 'R', long)]
		result_path: Option<PathBuf>,

		/// Should directory scan be recursive. Default true
		#[arg(short, long)]
		recursive: Option<bool>,
	},

	/// Render result graphs
	Graph {
		/// Directory where graphs will be saved. Default `graphs/`
		#[arg(long)]
		graph_dir: Option<PathBuf>,

		/// Directory where all benchmark results are stored. Default `results/`
		#[arg(long)]
		result_dir: Option<PathBuf>,
	}
}

fn main() -> Result<(), Box<dyn Error>> {
	let cli = Cli::parse();

	match &cli.command {
		Commands::Generate { smt_dir } => {
			let smt_dir = smt_dir.clone().unwrap_or(PathBuf::from("smt/"));
			generate_smtlib_files(
				SmtRetriever::new(smt_dir)?
			)?;
		},

		Commands::Benchmark {
			solver: solvers,
			hash_function: hash_functions,
			collision_type: collision_types,
			round_range,
			arg_set,
			stop_tolerance,
			timeout_sec,
			smt_dir,
			result_dir,
			continue_on_fail,
			encoding_type,
			is_rerun,
		} => {
			let round_range = round_range.clone().unwrap_or(1..80);
			let arg_set = arg_set.clone().unwrap_or(Vec::with_capacity(0));
			let stop_tolerance = (*stop_tolerance).unwrap_or(3);
			let timeout = Duration::from_secs((*timeout_sec).unwrap_or(15 * 60));
			let continue_on_fail = (*continue_on_fail).unwrap_or(false);
			let encoding_type = encoding_type.unwrap_or(EncodingType::BruteForce);
			let smt_dir = smt_dir.clone().unwrap_or(PathBuf::from("smt/"));
			let is_rerun = is_rerun.unwrap_or(false);

			let save_dir = if result_dir
				.clone()
				.is_some_and(|path| path.to_str().unwrap().to_lowercase() == "none")
			{
				None
			} else if let Some(path) = result_dir.clone() {
				Some(path)
			} else {
				Some(PathBuf::from("results/"))
			};

			let runner = BenchmarkRunner::new(
				stop_tolerance,
				timeout,
				SmtRetriever::new(smt_dir)?,
				save_dir,
				continue_on_fail,
				encoding_type,
				is_rerun,
			);

			runner.run_benchmarks(
				solvers.clone(),
				hash_functions.clone(),
				collision_types.clone(),
				round_range,
				arg_set,
			)?;
		}

		Commands::Sha2 {
			msg,
			msg_block,
			hash_function,
			rounds,
			start_vector,
		} => {
			let rounds = rounds.unwrap_or(hash_function.max_rounds());

			let start_vector = match start_vector {
				None => StartVector::IV,
				Some(start_vector) => {
					let mut words= Vec::with_capacity(8);
					for word in start_vector.split_whitespace() {
						 words.push(Word::from_str_radix(word, 16, *hash_function)?);
					}

					StartVector::CV(<[Word; 8]>::try_from(words).unwrap())
				}
			};

			let result = if let Some(msg) = msg {
				Sha::from_string(
					msg,
					*hash_function,
					rounds,
					start_vector,
				)?.execute()?
			} else if let Some(msg_block) = msg_block {
				Sha::from_message_block(
					MessageBlock::from_str_radix(msg_block, 16, *hash_function)?,
					*hash_function,
					rounds,
					start_vector,
				)?.execute()?
			} else {
				return Err(Box::from("Either msg or msg_block must be provided"));
			};

			println!("{}", result.hash);
		},

		Commands::Load {
			result_path,
			recursive,
		} => {
			let result_path = result_path.clone().unwrap_or(PathBuf::from("results/"));
			let recursive = recursive.unwrap_or(true);

			let benchmarks_with_files = load_mapped(&result_path, recursive)?;
			let show_file_names = benchmarks_with_files.len() > 1;
			for (mut benchmark, file_path) in benchmarks_with_files {
				let file_name = file_path
					.file_name()
					.unwrap()
					.to_str()
					.ok_or("Failed to read file")?;

				if show_file_names {
					println!("{file_name}");
				}

				match benchmark.parse_output() {
					Ok(output) => match output {
						None => println!("UNSAT\n"),
						Some(colliding_pair) => println!("{}\n", colliding_pair),
					}
					Err(err) => println!("{err}"),
				}

				println!("---\n")
			}
		}

		Commands::Graph {
			graph_dir,
			result_dir,
		} => {
			let graph_dir = graph_dir.clone().unwrap_or(PathBuf::from("graphs/"));
			let result_dir = result_dir.clone().unwrap_or(PathBuf::from("results/"));

			let mut graph_renderer = GraphRenderer::new(
				graph_dir.clone(),
				(1024, 768),
				("noto sans", 36),
				("noto sans", 14),
				Box::from([
					RGBColor(166, 30, 77), // Maroon
					RGBColor(24, 100, 171), // Dark Blue
					RGBColor(8, 127, 91), // Green
					RGBColor(250, 176, 5), // Yellow
					RGBColor(156, 54, 181), // Purple
					RGBColor(12, 133, 153), // Cyan
					RGBColor(95, 61, 196), // Light Purple
					RGBColor(70, 210, 94), // Light Green
					RGBColor(116, 143, 252), // Light Blue
					RGBColor(0, 0, 0),
				]),
				2,
				DataRetriever::new(result_dir.clone())?,
			)?;

			graph_renderer.generate_all_graphs()?;
		},
	}

	Ok(())
}

fn load_mapped(
	dir_location: &PathBuf,
	recursive: bool,
) -> Result<Vec<(Benchmark, PathBuf)>, Box<dyn Error>> {
	let mut map = Vec::new();

	if dir_location.is_file() {
		map.push((Benchmark::load(dir_location)?, dir_location.clone()));
		return Ok(map);
	}

	for dir_entry in fs::read_dir(dir_location)? {
		if let Ok(entry) = dir_entry {
			let metadata = entry.metadata()?;
			if recursive && metadata.is_dir() {
				map.extend(load_mapped(&entry.path(), true)?);
			} else if metadata.is_file() {
				map.push((Benchmark::load(&entry.path())?, entry.path()));
			}
		}
	}

	Ok(map)
}

fn parse_range(s: &str) -> Result<Range<u8>, String> {
	let (start, end) = s.split_once("..")
		.ok_or_else(|| format!("Invalid range format: '{}'", s))?;

	Ok(Range {
		start: start.parse().map_err(|e| format!("Start: {}", e))?,
		end: end.parse().map_err(|e| format!("End: {}", e))?
	})
}

// TODO: Finish DB migration stuff using rusqlite
//
// let db_path = PathBuf::from("results.sqlite");
// let mut result_store = ResultStore::new(db_path);

// let benchmarks = result_store.load_results()?;
// println!("{:?}", benchmarks);


// result_store.create_table()?;

// let benchmarks = Benchmark::load_all(&PathBuf::from("results"), true)?;

// for benchmark in benchmarks {
// 	result_store.save_result(&benchmark)?;
// }
