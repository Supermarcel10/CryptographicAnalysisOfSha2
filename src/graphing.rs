use std::error::Error;
use std::ops::Range;
use std::path::PathBuf;
use plotters::prelude::*;
use crate::structs::benchmark::{Benchark, BenchmarkResult};
use crate::structs::hash_function::HashFunction;

type Data = Vec<Benchark>;

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum ChartingError<'a> {
	#[error("failed to get range for {variable}")]
	GetRangeFailed {
		variable: &'a str,
	},
}

fn filter_data(data: Data, hash_function: HashFunction) -> Data {
	data.into_iter()
		.filter(|b| b.hash_function == hash_function && b.result == BenchmarkResult::Sat)
		.collect()
}

fn get_range<T: Copy + Ord>(
	data: &Data,
	retr: fn(&Benchark) -> T,
) -> Option<Range<T>> {
	let mut it = data.into_iter();
	let first = retr(it.next()?);
	let (min, max) = it.fold((first, first), |(min_agg, max_agg), b| {
		let v = retr(b);
		(v.min(min_agg), v.max(max_agg))
	});

	Some(min..max)
}

fn create_time_and_memory_chart(
	data: Data,
	color_palette: Vec<RGBColor>,
	file_name: &str,
) -> Result<PathBuf, Box<dyn Error>> {
	let path = PathBuf::from(format!("graphs/{file_name}.svg"));
	let output_size = (1024, 768);

	let font = "noto sans";

	// TODO: Look into why Range<u8> does not work?
	//? Potential issue in plotters.rs?
	//? Range<u8> and Range<u16> don't implement plotters::prelude::Ranged as expected?

	// Define ranges
	let x_range: Range<u32> = get_range(&data, |b| b.rounds as u32)
		.ok_or(ChartingError::GetRangeFailed { variable: "x_range"})?;
	let y_range_mem = get_range(&data, |b| b.memory_bytes / 1024^2)
		.ok_or(ChartingError::GetRangeFailed { variable: "y_range_mem"})?;
	let y_range_time = get_range(&data, |b| b.execution_time.as_secs())
		.ok_or(ChartingError::GetRangeFailed { variable: "y_range_time"})?;

	// Define Cartesian mapped data
	let memory_data = data
		.iter()
		.map(|b| (b.rounds as u32, b.memory_bytes / 1024^2));

	let time_data = data
		.iter()
		.map(|b| (b.rounds as u32, b.execution_time.as_secs()));

	let path_clone_bind = path.clone();
	let root = SVGBackend::new(&path_clone_bind, output_size)
		.into_drawing_area();
	root.fill(&WHITE)?;

	let mut chart = ChartBuilder::on(&root)
		.x_label_area_size(45)
		.y_label_area_size(60)
		.right_y_label_area_size(60)
		.margin(5)
		.caption("Memory & Time vs Rounds", (font, 36))
		.build_cartesian_2d(x_range.clone(), y_range_mem)? // Memory
		.set_secondary_coord(x_range, y_range_time.log_scale().base(2.0)); // Time

	// Draw X axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_y_axis()
		.x_desc("Compression Rounds")
		.label_style((font, 14).with_color(&BLACK))
		.draw()?;

	// Draw primary Y axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_x_axis()
		.y_desc("Memory (MB)")
		.label_style((font, 14).with_color(&color_palette[0]))
		.draw()?;

	// Draw secondary Y axis
	chart
		.configure_secondary_axes()
		.y_desc("Time (s)")
		.y_label_formatter(&|&x| format!("2^{}", x.ilog2()))
		.label_style((font, 14).with_color(&color_palette[1]))
		.draw()?;

	// Draw primary data
	chart
		.draw_series(LineSeries::new(memory_data.clone(), color_palette[0]))?
		.label("Memory")
		.legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_palette[0]));

	chart.draw_series(PointSeries::of_element(
		memory_data,
		3,
		color_palette[0],
		&|c, s, st| Circle::new(c, s, st.filled()),
	))?;

	// Draw secondary data
	chart
		.draw_secondary_series(LineSeries::new(time_data.clone(), color_palette[1]))?
		.label("Time")
		.legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_palette[1]));

	chart.draw_secondary_series(PointSeries::of_element(
		time_data,
		3,
		color_palette[1],
		&|c, s, st| Circle::new(c, s, st.filled()),
	))?;

	// Draw legend
	chart
		.configure_series_labels()
		.background_style(RGBColor(220, 220, 220))
		.position(SeriesLabelPosition::LowerRight)
		.draw()?;

	// Write to PathBuf
	root.present()?;
	Ok(path)
}

#[cfg(test)]
mod tests {
	use std::error::Error;
	use std::path::PathBuf;
	use std::time::Duration;
	use plotters::style::RGBColor;
	use crate::structs::benchmark::{Benchark, BenchmarkResult, Solver};
	use crate::structs::collision_type::CollisionType;
	use crate::structs::hash_function::HashFunction::*;
	use super::{create_time_and_memory_chart, filter_data};

	fn cleanup_test(chart_result: Result<PathBuf, Box<dyn Error>>) {
		if let Ok(path) = chart_result {
			std::fs::remove_file(path).expect("Test cleanup failed!");
		}
	}

	#[test]
	fn test_filter_data() {
		// Mock Data
		let benchmarks = vec![
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 16,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1000),
				memory_bytes: 1000,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 17,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1400),
				memory_bytes: 12503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 18,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(5000),
				memory_bytes: 525503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA224,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA224,
				rounds: 20,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(800000),
				memory_bytes: 82550300,
				result: BenchmarkResult::MemOut,
				console_output: String::new(),
			},
		];

		let data = filter_data(benchmarks, SHA224);
		assert_eq!(data.len(), 1);
	}

	#[test]
	fn test_create_time_and_memory_chart() {
		// Mock Data
		let benchmarks = vec![
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 16,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1000),
				memory_bytes: 1000,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 17,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1400),
				memory_bytes: 12503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 18,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(5000),
				memory_bytes: 525503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
			Benchark {
				solver: Solver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: String::new(),
			},
		];

		let color_palette = vec![
			RGBColor(37, 95, 133),
			RGBColor(140, 33, 85),
			RGBColor(221, 164, 72),
			RGBColor(50, 150, 93),
			RGBColor(0, 0, 0),
		];

		let chart = create_time_and_memory_chart(
			benchmarks,
			color_palette,
			"test_create_time_and_memory_chart"
		);

		assert!(matches!(chart, Ok(..)));

		cleanup_test(chart);
	}
}
