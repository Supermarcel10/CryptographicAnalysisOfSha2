use std::collections::BTreeMap;
use std::error::Error;
use std::path::PathBuf;
use plotters::prelude::*;
use crate::graphing::graph_renderer::{GraphRenderer, GraphRendererError};
use crate::graphing::utils::get_range;
use crate::structs::benchmark::Benchmark;


impl GraphRenderer {
	pub fn create_time_and_memory_chart(
		&self,
		data: Vec<Benchmark>,
	) -> Result<PathBuf, Box<dyn Error>> {
		let file_name = format!("{}.svg", "test2");
		let path = self.output_directory.join(file_name);

		let mut sorted_data = data.clone();
		sorted_data.sort_by_key(|b| b.rounds);

		// Define ranges
		let x_range = get_range(&data, &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range"})?;
		let y_range_mem = get_range(&data, &|b| b.memory_bytes as f64 / 1048576.0)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range_mem"})?;
		let y_range_time = get_range(&data, &|b| b.execution_time.as_secs_f64())
			.ok_or(GraphRendererError::GetRangeFailed { variable: "y_range_time"})?;

		// Define Cartesian mapped data
		let sorted_data = sorted_data
			.into_iter()
			.map(|b| (b.rounds as u32, b.memory_bytes as f64 / 1048576.0, b.execution_time.as_secs_f64()));

		let path_clone_bind = path.clone();
		let root = SVGBackend::new(&path_clone_bind, self.output_size)
			.into_drawing_area();
		root.fill(&WHITE)?;

		let mut chart = ChartBuilder::on(&root)
			.x_label_area_size(45)
			.y_label_area_size(60)
			.right_y_label_area_size(60)
			.margin(5)
			.caption("Memory & Time vs Rounds", self.title_style)
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
		let time_data: Vec<_> = sorted_data.clone().map(|(r, _, t)| (r, t)).collect();
		self.draw_series(
			&mut chart,
			time_data,
			true,
			false,
			"Time",
			Some(self.color_palette[0].to_rgba())
		)?;

		// Draw secondary data
		let memory_data: Vec<_> = sorted_data.clone().map(|(r, m, _)| (r, m)).collect();
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

	pub fn create_baseline_graph(
		self,
		baseline_data: Vec<Benchmark>,
		data: Vec<Vec<Benchmark>>,
	) -> Result<PathBuf, Box<dyn Error>> {
		let file_name = format!("{}.svg", "test3");
		let path = self.output_directory.join(file_name);

		let mut baseline_data = baseline_data.clone();
		baseline_data.sort_by_key(|b| b.rounds);

		// Define ranges
		let x_range = get_range(&baseline_data, &|b| b.rounds as u32)
			.ok_or(GraphRendererError::GetRangeFailed { variable: "x_range"})?;
		let y_range = -25.0..25.0; // TODO: Derive this some other way?

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
			.caption("Bitwuzla Abstraction Deviation Graph", self.title_style)
			.build_cartesian_2d(x_range, y_range)?;

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (%dev)",
			None,
			Some(&|v| format!("{:+}%", v)),
		)?;

		// Draw deviation data
		for (i, run) in data.iter().enumerate() {
			if run.len() <= 0 {
				continue;
			}

			// Calculate deviation from baseline
			let mut data = vec![];
			for b in run {
				if let Some(&base_time) = baseline.get(&(b.rounds as u32)) {
					let dev_time = b.execution_time.as_secs_f64();
					data.push((b.rounds as u32, 1.0 - (dev_time / base_time)))
				}
			}

			data.sort_by_key(|b| b.0);

			self.draw_series(
				&mut chart,
				data,
				true,
				true,
				&run[0].arguments.join(" "),
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

	pub fn solver_comparison(
		&self,
		data: Vec<Benchmark>,
		// TODO: Add a way to differenciate between different hash functions and different collision types
	) -> Result<PathBuf, Box<dyn Error>> {
		let file_name = format!("{}.svg", "test");
		let path = self.output_directory.join(file_name);

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
			.caption("SHA256 STD", self.title_style)
			.build_cartesian_2d(x_range, y_range.log_scale().base(2.0))?;

		// Draw axis
		self.set_x_axis_as_rounds(&mut chart)?;
		self.set_y_axis(
			&mut chart,
			"Time (s)",
			None,
			Some(&|y: &f64| format!("2^{}", y.log2())),
		)?;

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
}
