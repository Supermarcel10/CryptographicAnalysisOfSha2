use std::collections::BTreeMap;
use std::error::Error;
use std::ops::Range;
use std::path::PathBuf;
use num_traits::Float;
use plotters::prelude::*;
use crate::graphing::custom_point_styles::PointStyles;
use crate::graphing::graph_renderer::{GraphRenderer, GraphRendererError};
use crate::graphing::graph_renderer::GraphRendererError::{FailedToGenerate, MissingData};
use crate::graphing::line_styles::LineStyle::Normal;
use crate::graphing::utils::{classify_benchmark_results_to_point_styles, get_range};
use crate::smt_lib::smt_retriever::EncodingType;
use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver};


/// Implementation of graph types
impl GraphRenderer {
	/// Create graph describing the relation of time and memory for a given run.
	///
	/// # Arguments
	///
	/// * `data`: Single run benchmark data.
	///
	/// # Returns
	/// `Result<PathBuf, Box<dyn Error>>`
	///
	/// Returns path of saved graph file, or error.
	fn create_time_and_memory_chart(
		&self,
		data: Vec<Benchmark>,
	) -> Result<PathBuf, Box<dyn Error>> {
		if data.len() == 0 {
			println!("{}", MissingData { graph_name: "Time & Memory", dataset_name: "data" });
		}

		let solver_name = data[0].solver.to_string().to_lowercase();
		let file_name = format!(
			"detailed_{}_{}_{}.svg",
			solver_name,
			data[0].hash_function,
			data[0].collision_type,
		);
		let path = self.output_dir.join(file_name);

		let data: Vec<_> = data
			.into_iter()
			.filter(|b| b.result == BenchmarkResult::Sat || b.result == BenchmarkResult::Unsat)
			.collect();

		let mut sorted_data = data;
		sorted_data.sort_by_key(|b| b.rounds);

		// Define ranges
		let x_range = get_range(&sorted_data.clone(), &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range"})?;
		let y_range_mem = get_range(&sorted_data.clone(), &|b| b.memory_bytes as f64 / 1048576.0)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range_mem"})?;
		let y_range_time = get_range(&sorted_data.clone(), &|b| b.execution_time.as_secs_f64())
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range_time"})?;

		let path_clone_bind = path.clone();
		let root = SVGBackend::new(&path_clone_bind, self.output_size)
			.into_drawing_area();
		root.fill(&WHITE)?;

		let title = format!("{solver_name}; Memory & Time vs Rounds");
		let mut chart = ChartBuilder::on(&root)
			.x_label_area_size(45)
			.y_label_area_size(60)
			.right_y_label_area_size(60)
			.margin(5)
			.caption(title, self.title_style)
			.build_cartesian_2d(x_range.clone(), y_range_time.log_scale().base(2.0))? // Time
			.set_secondary_coord(x_range, y_range_mem); // Memory

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (s)",
			Some(*self.line_styles[0].get_color()),
			Some(&|y: &f64| format!("2^{}", y.log2())),
		)?;
		self.set_secondary_y_axis(
			&mut chart,
			"Memory (MiB)",
			Some(*self.line_styles[1].get_color()),
			None,
		)?;

		// Draw primary data
		let time_data: Vec<_> = sorted_data
			.clone()
			.into_iter()
			.map(|b| (b.rounds as u32, b.execution_time.as_secs_f64()))
			.collect();

		self.draw_series(
			&mut chart,
			time_data,
			PointStyles::Basic,
			true,
			"Time",
			Some(self.line_styles[0])
		)?;

		// Draw secondary data
		let memory_data: Vec<_> = sorted_data
			.clone()
			.into_iter()
			.map(|b| (b.rounds as u32, b.memory_bytes as f64 / 1048576.0))
			.collect();

		self.draw_secondary_series(
			&mut chart,
			memory_data,
			true,
			true,
			"Memory",
			Some(*self.line_styles[1].get_color())
		)?;

		self.draw_legend(&mut chart)?;

		// Write to PathBuf
		root.present()?;
		Ok(path)
	}

	/// Create graph where one solver run is a baseline, and the remaining data is compared against it.
	///
	/// # Arguments
	///
	/// * `baseline`: Single run benchmark data, used as a baseline.
	/// * `data`: Vector of benchmark runs, used as deviation.
	/// * `argument_name`: String outputted to the title.
	/// * `buffer`: Should the graph be buffered on each end?
	/// * `enforce`: Should minimums and a max range be respected?
	///
	/// # Returns
	/// `Result<PathBuf, Box<dyn Error>>`
	///
	/// Returns path of saved graph file, or error.
	fn create_baseline_graph<L>(
		&self,
		baseline_data: Vec<Benchmark>,
		data: BTreeMap<L, Vec<Benchmark>>,
		title_str: &str,
		buffer: bool,
		enforce: bool,
		draw_background: bool,
	) -> Result<PathBuf, Box<dyn Error>>
	where
		L: Clone + Ord + Into<String>,
	{
		if baseline_data.len() == 0 {
			return Err(MissingData { graph_name: "baseline", dataset_name: "baseline" }.into());
		}

		if data.len() == 0 {
			println!("{}", MissingData { graph_name: "baseline", dataset_name: "data" });
		}

		// Define x range
		let x_range = get_range(&baseline_data, &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range" })?;

		// Trim data
		let mut trimmed_data: BTreeMap<L, Vec<Benchmark>> = BTreeMap::new();
		for (encoding, mut benchmarks) in data.clone().into_iter() {
			if benchmarks.len() > x_range.end as usize {
				benchmarks.retain(|b| b.rounds <= x_range.end as u8);
			}

			trimmed_data.insert(encoding, benchmarks);
		}

		let title = format!(
			"{} {} {}: {}",
			baseline_data[0].solver,
			baseline_data[0].hash_function,
			baseline_data[0].collision_type,
			title_str,
		);

		let file_name = format!(
			"{}_{}.svg",
			baseline_data[0].solver.to_string().to_lowercase(),
			title_str.to_lowercase().replace(" ", "_"),
		);

		let path = self.output_dir.join(file_name);

		let mut baseline_data = baseline_data;
		baseline_data.sort_by_key(|b| b.rounds);

		let mut baseline = BTreeMap::new();
		for b in &baseline_data {
			baseline.insert(b.rounds as u32, b.execution_time.as_secs_f64());
		}

		// Get range & calculate deviation from baseline
		let mut deviation_range: Range<f64> = f64::MAX..f64::MIN;
		let mut deviation_data: BTreeMap<String, Vec<(u32, f64, BenchmarkResult)>> = BTreeMap::new();
		for (label, run) in trimmed_data.clone() {
			let mut data = vec![];
			for b in run {
				let dev_percent = if let Some(&base_time) = baseline.get(&(b.rounds as u32)) {
					let dev_time = b.execution_time.as_secs_f64();
					let dev_percent = ((dev_time / base_time) - 1.0) * 100.0;

					if deviation_range.start > dev_percent {
						deviation_range.start = dev_percent;
					}

					if deviation_range.end < dev_percent {
						deviation_range.end = dev_percent;
					}

					dev_percent
				} else {
					f64::neg_infinity()
				};

				data.push((b.rounds as u32, dev_percent, b.result))
			}

			data.sort_by_key(|b| b.0);
			deviation_data.insert(label.into(), data);
		}

		if buffer {
			deviation_range.start = deviation_range.start - 5.0;
			deviation_range.end = deviation_range.end + 5.0;
		}

		// Truncate max range & enforce a minimum
		if enforce {
			deviation_range.end = deviation_range.end.min(100.0);
			deviation_range.start = deviation_range.start.min(-5.0);
		}

		// Define y range
		let y_range = deviation_range;

		let path_clone_bind = path.clone();
		let root = SVGBackend::new(&path_clone_bind, self.output_size)
			.into_drawing_area();
		root.fill(&WHITE)?;

		let mut chart = ChartBuilder::on(&root)
			.x_label_area_size(45)
			.y_label_area_size(60)
			.margin(5)
			.caption(title, self.title_style)
			.build_cartesian_2d(x_range.clone(), y_range.clone())?;

		// Draw background
		if draw_background {
			chart
				.draw_series(std::iter::once(
					Rectangle::new(
						[(x_range.start, -2.0), (x_range.end, y_range.start)],
						RGBAColor(182, 255, 182, 0.4).filled(),
					)
				))?;

			chart
				.draw_series(std::iter::once(
					Rectangle::new(
						[(x_range.start, 2.0), (x_range.end, -2.0)],
						RGBAColor(182, 182, 182, 0.2).filled(),
					)
				))?;

			chart
				.draw_series(std::iter::once(
					Rectangle::new(
						[(x_range.start, 2.0), (x_range.end, y_range.end)],
						RGBAColor(255, 182, 182, 0.4).filled(),
					)
				))?;
		}

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (%dev)",
			None,
			Some(&|v| format!("{:+.0}%", v)),
		)?;

		// Draw deviation data
		for (i, (label, run)) in deviation_data.into_iter().enumerate() {
			if run.len() <= 0 {
				continue;
			}

			let (cartesian_run, _): (Vec<_>, Vec<_>) = run
				.into_iter()
				.map(|(x, y, result)| ((x, y), result))
				.unzip();

			self.draw_series(
				&mut chart,
				cartesian_run,
				PointStyles::Basic,
				true,
				&label,
				Some(self.line_styles[i]),
			)?
		}

		// Draw baseline data
		self.draw_series(
			&mut chart,
			baseline.keys().map(|&x| (x, 0.0)).collect(),
			PointStyles::None,
			true,
			"Baseline",
			Some(Normal {
				color: RGBAColor(0, 0, 0, 0.3),
			}),
		)?;

		self.draw_legend(&mut chart)?;

		// Write to PathBuf
		root.present()?;
		Ok(path)
	}

	/// Create graph comparing solvers.
	///
	/// # Arguments
	///
	/// * `data`: All runs combined.
	///
	/// # Returns
	/// `Result<PathBuf, Box<dyn Error>>`
	///
	/// Returns path of saved graph file, or error.
	fn solver_comparison(
		&self,
		data: Vec<Benchmark>,
	) -> Result<PathBuf, Box<dyn Error>> {
		if data.is_empty() {
			return Err(MissingData { graph_name: "comparison", dataset_name: "data" }.into());
		}

		let title = format!(
			"{} {} Solver Comparison",
			data[0].hash_function,
			data[0].collision_type,
		);

		let file_name = format!(
			"solver_comparison_{}_{}.svg",
			data[0].hash_function,
			data[0].collision_type,
		);

		let path = self.output_dir.join(file_name);

		let mut sorted_data = data.clone();
		sorted_data.sort_by_key(|b| b.rounds);

		// Define ranges
		let x_range = get_range(&data, &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range"})?;
		let y_range = get_range(&data, &|b| b.execution_time.as_secs_f64())
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range"})?;

		let path_clone_bind = path.clone();
		let root = SVGBackend::new(&path_clone_bind, self.output_size)
			.into_drawing_area();
		root.fill(&WHITE)?;

		let mut chart = ChartBuilder::on(&root)
			.x_label_area_size(45)
			.y_label_area_size(60)
			.margin(5)
			.caption(title, self.title_style)
			.build_cartesian_2d(x_range, y_range.log_scale().base(2.0))?;

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (s)",
			None,
			Some(&|y: &f64| format!("2^{}", y.log2())),
		)?;

		// Draw data
		let mut split_data = BTreeMap::new();
		for b in sorted_data {
			split_data
				.entry(b.solver)
				.or_insert_with(Vec::new)
				.push((b.rounds as u32, b.execution_time.as_secs_f64(), b.result));
		}

		for (i, (solver, data)) in split_data.into_iter().enumerate() {
			let (cartesian_run, benchmark_results): (Vec<_>, Vec<_>) = data
				.into_iter()
				.map(|(x, y, result)| ((x, y), result))
				.unzip();

			self.draw_series(
				&mut chart,
				cartesian_run,
				PointStyles::Custom{
					shapes: classify_benchmark_results_to_point_styles(benchmark_results.clone())
				},
				true,
				&solver.to_string(),
				Some(self.line_styles[i])
			)?;
		}

		// TODO: Do secondary legend with the result types
		self.draw_legend(&mut chart)?;

		Ok(path)
	}

	/// Collection function to generate all graphs.
	pub fn generate_all_graphs(&mut self) -> Result<(), Box<dyn Error>> {
		use crate::structs::hash_function::HashFunction::*;
		use crate::structs::collision_type::CollisionType::*;
		use crate::smt_lib::smt_retriever::EncodingType::*;


		// Generate all solver comparisons for each HashFunction and CollisionType
		for hash_function in [SHA224, SHA256, SHA512] {
			for collision_type in [Standard, SemiFreeStart, FreeStart] {
				let baselines = self.data_retriever.retrieve_all_baselines_with_encoding(
					hash_function,
					collision_type,
					BruteForce {
						simplified_maj_and_ch_functions: false,
						alternative_add: false,
					},
					false,
				)?;

				if baselines.is_empty() {
					println!(
						"WARNING: {}",
						FailedToGenerate {
							hash_function,
							collision_type,
							err: &MissingData {
								graph_name: "Time & Memory",
								dataset_name: "Bitwuzla",
							}.to_string(),
						},
					);
					continue;
				}
				self.solver_comparison(baselines)?;
			}
		}


		// Generate Bitwuzla detail chart
		let bitwuzla_baseline_with_anomalies = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			BruteForce {
				simplified_maj_and_ch_functions: false,
				alternative_add: false
			},
			true,
		)?;
		self.create_time_and_memory_chart(bitwuzla_baseline_with_anomalies.clone())?;


		// Generate Bitwuzla argument Graphs
		let arg_categories = BTreeMap::from([
			("Abstraction", "-abstraction"),
			("Preprocessing", "-pp-"),
			("Propagation", "-prop"),
			("Rewrite Level", "-rwl"),
			("SAT Solver", "--sat-solver"),
			("Solver Engine", "--bv-solver"),
		]);

		let bitwuzla_baseline: Vec<_> = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			BruteForce {
				simplified_maj_and_ch_functions: false,
				alternative_add: false
			},
			false,
		)?
			.into_iter()
			.filter(|b| b.result != BenchmarkResult::CPUOut)
			.collect();

		for (category, identifier) in arg_categories {
			let deviation_data = self.data_retriever.retrieve_with_args(
				SmtSolver::Bitwuzla,
				SHA256,
				Standard,
				false,
				identifier,
			)?;

			let deviation_data = deviation_data
				.into_iter()
				.map(|(a, runs)|{
					let runs = runs.into_iter()
						.filter(|b| b.result != BenchmarkResult::CPUOut)
						.collect();
					(a, runs)
				})
				.collect();

			self.create_baseline_graph(
				bitwuzla_baseline.clone(),
				deviation_data,
				&format!("{category} Args"),
				true,
				true,
				true,
			)?;
		}


		// Generate Bitwuzla encoding graphs
		let encoding_data = self.data_retriever.retrieve_non_bruteforce_encodings(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			false,
		)?;

		// DXOR
		let dxor_encoding_data: BTreeMap<_, _> = encoding_data
			.clone()
			.into_iter()
			.filter(|(e, _)| matches!(e, DeltaXOR { .. }))
			.collect();

		self.create_baseline_graph(
			bitwuzla_baseline.clone(),
			dxor_encoding_data,
			"Delta XOR Encoding Comparison",
			true,
			true,
			true,
		)?;

		// DSUB
		let dsub_encoding_data: BTreeMap<_, _> = encoding_data
			.clone()
			.into_iter()
			.filter(|(e, _)| matches!(e, DeltaSub { .. }))
			.collect();

		self.create_baseline_graph(
			bitwuzla_baseline.clone(),
			dsub_encoding_data,
			"Delta Sub Encoding Comparison",
			true,
			true,
			true,
		)?;

		// Pure encoding comparison graph
		let mut all_encodings: BTreeMap<EncodingType, Vec<Benchmark>> = BTreeMap::new();

		// Retrieve remaining results
		let bruteforce_simpl = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			BruteForce {
				simplified_maj_and_ch_functions: true,
				alternative_add: false,
			},
			false
		).expect("Failed to retrieve bruteforce simplified baseline");

		let bruteforce_alt_add = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			BruteForce {
				simplified_maj_and_ch_functions: false,
				alternative_add: true,
			},
			false
		).expect("Failed to retrieve bruteforce alt add baseline");

		let bruteforce_alt_add_simpl = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			BruteForce {
				simplified_maj_and_ch_functions: true,
				alternative_add: true,
			},
			false
		).expect("Failed to retrieve bruteforce alt add simplified baseline");

		// Insert baselines
		all_encodings.insert(BruteForce {
			simplified_maj_and_ch_functions: true,
			alternative_add: false,
		}, bruteforce_simpl);
		all_encodings.insert(BruteForce {
			simplified_maj_and_ch_functions: false,
			alternative_add: true,
		}, bruteforce_alt_add);
		all_encodings.insert(BruteForce {
			simplified_maj_and_ch_functions: true,
			alternative_add: true,
		}, bruteforce_alt_add_simpl);

		self.create_baseline_graph(
			bitwuzla_baseline.clone(),
			all_encodings,
			"Bruteforce Encoding Comparison",
			true,
			true,
			true,
		)?;

		Ok(())
	}
}
