use std::error::Error;
use std::path::{PathBuf};
use std::time::{Duration};
use clap::{Parser, Subcommand};
use plotters::prelude::RGBColor;
use crate::benchmark::runner::BenchmarkRunner;
use crate::data::data_retriever::DataRetriever;
use crate::graphing::graph_renderer::GraphRenderer;
use crate::sha::{MessageBlock, Sha, StartVector};
use crate::smt_lib::smt_lib::generate_smtlib_files;
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
		/// Directory where smt2 files will be saved
		smt_dir: PathBuf,
	},

	/// Run all benchmarks
	Benchmark {
		/// The number of required sequential failures to stop. Default 3
		#[arg(short, long)]
		stop_tolerance:  Option<u8>,

		/// Duration after which run is marked as timed out. Default 15 mins
		#[arg(short, long)]
		timeout_sec: Option<u64>,

		/// Path to directory containing SMT files. Default `smt/`
		#[arg(long)]
		smt_dir: Option<PathBuf>,

		/// Path to directory where result files will be saved to. `None` to disable output. Default `results/`
		#[arg(long)]
		result_dir: Option<PathBuf>,

		/// Should remaining benchmark runs continue despite error on one. Default false
		#[arg(long)]
		continue_on_fail: Option<bool>,
	},

	/// Run the underlying sha2 function
	Sha2 {
		/// Message to hash
		#[arg(short, long)]
		msg: Option<String>,

		/// Message digest block to hash (pre-padded and pre-processed digest)
		#[arg(alias = "mb", long)]
		msg_block: Option<String>,

		/// Hash function
		hash_function: HashFunction,

		/// Number of compression rounds. Default hash function max
		#[arg(short, long, default_value = None)]
		rounds: Option<u8>,

		// start_vector: Option<StartVector>,
	},

	// TODO: Add verify
	//
	// Verify {
	//
	// },

	/// Render result graphs
	Graph {
		/// Directory where graphs will be saved
		graph_dir: PathBuf,

		/// Directory where all benchmark results are stored
		result_dir: PathBuf,
	}
}

fn main() -> Result<(), Box<dyn Error>> {
	let cli = Cli::parse();

	match &cli.command {
		Commands::Generate { smt_dir } => {
			generate_smtlib_files(smt_dir.clone())?;
		},

		Commands::Benchmark {
			stop_tolerance,
			timeout_sec,
			smt_dir,
			result_dir,
			continue_on_fail,
		} => {
			let stop_tolerance = (*stop_tolerance).unwrap_or(3);
			let timeout = Duration::from_secs((*timeout_sec).unwrap_or(15 * 60));
			let continue_on_fail = (*continue_on_fail).unwrap_or(false);

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
				save_dir,
				continue_on_fail,
			);

			runner.run_benchmarks()?;
		},

		Commands::Sha2 {
			msg,
			msg_block,
			hash_function,
			rounds
		} => {
			let rounds = rounds.unwrap_or(hash_function.max_rounds());
			// TODO: Use provided start vector or IV by default
			let start_vector = StartVector::IV;

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

		Commands::Graph {
			graph_dir,
			result_dir,
		} => {
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
