use std::collections::BTreeMap;
use std::error::Error;
use std::ops::Range;
use std::path::PathBuf;
use plotters::prelude::*;
use crate::graphing::graph_renderer::{GraphRenderer, GraphRendererError};
use crate::graphing::graph_renderer::GraphRendererError::{FailedToGenerate, MissingData};
use crate::graphing::utils::get_range;
use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver, SolverArg};


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
			Some(self.color_palette[0].to_rgba()),
			Some(&|y: &f64| format!("2^{}", y.log2())),
		)?;
		self.set_secondary_y_axis(
			&mut chart,
			"Memory (MiB)",
			Some(self.color_palette[1].to_rgba()),
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
			true,
			true,
			"Time",
			Some(self.color_palette[0].to_rgba())
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
			Some(self.color_palette[1].to_rgba())
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
	///
	/// # Returns
	/// `Result<PathBuf, Box<dyn Error>>`
	///
	/// Returns path of saved graph file, or error.
	fn create_baseline_graph(
		&self,
		baseline_data: Vec<Benchmark>,
		data: BTreeMap<Vec<SolverArg>, Vec<Benchmark>>,
		argument_name: &str,
	) -> Result<PathBuf, Box<dyn Error>> {
		if baseline_data.len() == 0 {
			return Err(MissingData { graph_name: "baseline", dataset_name: "baseline" }.into());
		}

		if data.len() == 0 {
			println!("{}", MissingData { graph_name: "baseline", dataset_name: "data" });
		}

		let title = format!(
			"{} {} {}: {} Args",
			baseline_data[0].solver,
			baseline_data[0].hash_function,
			baseline_data[0].collision_type,
			argument_name,
		);

		let file_name = format!(
			"{}_{}.svg",
			baseline_data[0].solver.to_string().to_lowercase(),
			argument_name.to_lowercase().replace(" ", "_"),
		);

		let path = self.output_dir.join(file_name);

		let mut baseline_data = baseline_data;
		baseline_data.sort_by_key(|b| b.rounds);

		// Get range for baseline
		let baseline_range = get_range(&baseline_data, &|b| b.execution_time.as_nanos())
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range baseline" })?;

		// Get range for all plots
		let mut deviation_range: Range<u128> = u128::MAX..u128::MIN;
		for (_, benchmarks) in data.clone() {
			for benchmark in benchmarks {
				let time = benchmark.execution_time.as_nanos();
				if time < deviation_range.start {
					deviation_range.start = time;
				}

				if time > deviation_range.end {
					deviation_range.end = time;
				}
			}
		}

		// Define ranges
		let x_range = get_range(&baseline_data, &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range" })?;
		let y_range = self.calculate_percent_dev(baseline_range, deviation_range, 10.0);

		let mut baseline = BTreeMap::new();
		for b in baseline_data {
			baseline.insert(b.rounds as u32, b.execution_time.as_secs_f64());
		}

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
		chart
			.draw_series(std::iter::once(
				Rectangle::new(
					[(x_range.start, 0.0), (x_range.end, y_range.start)],
					RGBAColor(182, 255, 182, 0.4).filled(),
				)
			))?;

		chart
			.draw_series(std::iter::once(
				Rectangle::new(
					[(x_range.start, 0.0), (x_range.end, y_range.end)],
					RGBAColor(255, 182, 182, 0.4).filled(),
				)
			))?;

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (%dev)",
			None,
			Some(&|v| format!("{:+.0}%", v)),
		)?;

		// Draw deviation data
		for (i, (args, run)) in data.iter().enumerate() {
			if run.len() <= 0 {
				continue;
			}

			// Calculate deviation from baseline
			let mut data = vec![];
			for b in run {
				if let Some(&base_time) = baseline.get(&(b.rounds as u32)) {
					let dev_time = b.execution_time.as_secs_f64();
					data.push((b.rounds as u32, ((dev_time / base_time) - 1.0) * 100.0))
				}
			}

			data.sort_by_key(|b| b.0);

			self.draw_series(
				&mut chart,
				data,
				true,
				true,
				&args.join(" "),
				Some(self.color_palette[i].to_rgba()),
			)?
		}

		// Draw baseline data
		self.draw_series(
			&mut chart,
			baseline.keys().map(|&x| (x, 0.0)).collect(),
			true,
			true,
			"Baseline (No Args)",
			Some(RGBAColor(0, 0, 0, 0.3)),
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

		// // Draw background
		// let col = RGBAColor(60, 60, 60, 0.25).filled();
		// chart
		// 	.draw_series(std::iter::once(
		// 		Rectangle::new(
		// 			[(x_range.start, y_range.end), (x_range.end, y_range.end - 125.0)],
		// 			col,
		// 		)
		// 	))?
		// 	.label("TIMEOUT")
		// 	.legend(move |(x, y)| Rectangle::new([(x + 5, y - 5), (x + 15, y + 5)], col));
		//
		// let col = RGBAColor(255, 0, 0, 0.125).filled();
		// chart
		// 	.draw_series(std::iter::once(
		// 		Rectangle::new(
		// 			[(0, y_range.start), (8, y_range.end - 125.0)],
		// 			col,
		// 		)
		// 	))?
		// 	.label("UNSAT")
		// 	.legend(move |(x, y)| Rectangle::new([(x + 5, y - 5), (x + 15, y + 5)], col));
		//
		// let col = RGBAColor(0, 255, 0, 0.125).filled();
		// chart
		// 	.draw_series(std::iter::once(
		// 		Rectangle::new(
		// 			[(8, y_range.start), (x_range.end, y_range.end - 125.0)],
		// 			col,
		// 		)
		// 	))?
		// 	.label("SAT")
		// 	.legend(move |(x, y)| Rectangle::new([(x + 5, y - 5), (x + 15, y + 5)], col));

		// Draw data
		let mut split_data = BTreeMap::new();
		for b in sorted_data {
			split_data
				.entry(b.solver)
				.or_insert_with(Vec::new)
				.push((b.rounds as u32, b.execution_time.as_secs_f64()));
		}

		for (i, (solver, data)) in split_data.into_iter().enumerate() {
			self.draw_series(
				&mut chart,
				data,
				true,
				false,
				&solver.to_string(),
				Some(self.color_palette[i].to_rgba())
			)?;
		}

		// TODO: Add shapes for result types!
		// TODO: Do secondary legend with the result types
		self.draw_legend(&mut chart)?;

		Ok(path)
	}

	/// Collection function to generate all graphs.
	pub fn generate_all_graphs(&mut self) -> Result<(), Box<dyn Error>> {
		use crate::structs::hash_function::HashFunction::*;
		use crate::structs::collision_type::CollisionType::*;


		// Generate all solver comparisons for each HashFunction and CollisionType
		for hash_function in [SHA224, SHA256, SHA512] {
			for collision_type in [Standard, SemiFreeStart, FreeStart] {
				let baselines = self.data_retriever.retrieve_all_baselines(
					hash_function,
					collision_type,
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

		let bitwuzla_baseline = self.data_retriever.retrieve_baseline(
			SmtSolver::Bitwuzla,
			SHA256,
			Standard,
			false,
		)?;

		for (category, identifier) in arg_categories {
			let deviation_data = self.data_retriever.retrieve_with_args(
				SmtSolver::Bitwuzla,
				SHA256,
				Standard,
				false,
				identifier,
			)?;

			self.create_baseline_graph(
				bitwuzla_baseline.clone(),
				deviation_data,
				category,
			)?;
		}

		Ok(())
	}
}
