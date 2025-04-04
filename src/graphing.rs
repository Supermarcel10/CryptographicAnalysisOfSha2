use std::collections::HashSet;
use std::error::Error;
use std::ops::Range;
use std::path::PathBuf;
use plotters::prelude::*;
use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver};
use crate::structs::hash_function::HashFunction;

const OUTPUT_SIZE: (u32, u32) = (1024, 768);

const FONT: &str = "noto sans";
const TITLE_STYLE: (&str, u32) = (FONT, 36);
const TEXT_STYLE: (&str, u32) = (FONT, 14);

type Data = Vec<Benchmark>;

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum ChartingError<'a> {
	#[error("failed to get range for {variable}")]
	GetRangeFailed {
		variable: &'a str,
	},
}

// TODO: Move utilities to another file dealing with preparing data
fn filter_data(data: Data, hash_function: HashFunction) -> Data {
	data.into_iter()
		.filter(|b| b.hash_function == hash_function && b.result == BenchmarkResult::Sat)
		.collect()
}

// TODO: Look into why Range<u8> does not work?
//? Potential issue in plotters.rs?
//? Range<u8> and Range<u16> don't implement plotters::prelude::Ranged as expected?

fn get_range<T: Copy + PartialOrd>(
    data: &Data,
    retr: fn(&Benchmark) -> T,
) -> Option<Range<T>> {
    let mut it = data.into_iter();
    let first = retr(it.next()?);
    let (min, max) = it.fold((first, first), |(min_agg, max_agg), b| {
        let v = retr(b);
        (
            if v < min_agg { v } else { min_agg },
            if v > max_agg { v } else { max_agg }
        )
    });

	Some(min..max)
}

fn order_data_by_rounds(data: &mut Data) {
	data.sort_by_key(|b| b.rounds);
}

fn create_time_and_memory_chart(
	data: Data,
	color_palette: Vec<RGBColor>,
	file_name: &str,
) -> Result<PathBuf, Box<dyn Error>> {
	let path = PathBuf::from(format!("graphs/{file_name}.svg"));

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
	let root = SVGBackend::new(&path_clone_bind, OUTPUT_SIZE)
		.into_drawing_area();
	root.fill(&WHITE)?;

	let mut chart = ChartBuilder::on(&root)
		.x_label_area_size(45)
		.y_label_area_size(60)
		.right_y_label_area_size(60)
		.margin(5)
		.caption("Memory & Time vs Rounds", TITLE_STYLE)
		.build_cartesian_2d(x_range.clone(), y_range_mem)? // Memory
		.set_secondary_coord(x_range, y_range_time.log_scale().base(2.0)); // Time

	// Draw X axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_y_axis()
		.x_desc("Compression Rounds")
		.label_style(TEXT_STYLE.with_color(&BLACK))
		.draw()?;

	// Draw primary Y axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_x_axis()
		.y_desc("Memory (MB)")
		.label_style(TEXT_STYLE.with_color(&color_palette[0]))
		.draw()?;

	// Draw secondary Y axis
	chart
		.configure_secondary_axes()
		.y_desc("Time (s)")
		.y_label_formatter(&|&x| format!("2^{}", x.ilog2()))
		.label_style(TEXT_STYLE.with_color(&color_palette[1]))
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

pub fn create_baseline_graph(
	baseline: Data,
	data: Data,
	color_palette: Vec<RGBColor>,
	file_name: &str,
) -> Result<PathBuf, Box<dyn Error>> {
	let path = PathBuf::from(format!("graphs/{file_name}.svg"));

	let mut baseline = baseline.clone();
	order_data_by_rounds(&mut baseline);

	// Define ranges
	let x_range: Range<u32> = get_range(&baseline, |b| b.rounds as u32)
		.ok_or(ChartingError::GetRangeFailed { variable: "x_range"})?;
	let y_range = -100.0..100.0; // -100% to +100% // TODO: Derive this some other way?

	// Define Cartesian mapped data
	let time_data = data
		.iter()
		.map(|b| (b.rounds as u32, 0.0)); // TODO: Make deviation calculation

	let path_clone_bind = path.clone();
	let root = SVGBackend::new(&path_clone_bind, OUTPUT_SIZE)
		.into_drawing_area();
	root.fill(&WHITE)?;

	let mut chart = ChartBuilder::on(&root)
		.x_label_area_size(45)
		.y_label_area_size(60)
		.margin(5)
		.caption("(Deviation from Baseline) %dev", TITLE_STYLE)
		.build_cartesian_2d(x_range, y_range)?;

	// Draw X axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_y_axis()
		.x_desc("Compression Rounds")
		.x_label_formatter(&|v| format!("{:.0}", v))
		.label_style(TEXT_STYLE.with_color(&BLACK))
		.draw()?;

	// Draw primary Y axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_x_axis()
		.y_desc("Time (% deviation)")
		.y_label_formatter(&|v| format!("{:+}%", v)) // y-axis +/-%
		.label_style(TEXT_STYLE.with_color(&color_palette[0]))
		.draw()?;

	// Draw data
	chart
		.draw_series(LineSeries::new(time_data.clone(), color_palette[0]))?
		.label("Time")
		.legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_palette[0]));

	chart.draw_series(PointSeries::of_element(
		time_data,
		3,
		color_palette[0],
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

pub fn create_smt_comparison(
	data: Data,
	color_palette: Vec<RGBColor>,
	file_name: &str,
) -> Result<PathBuf, Box<dyn Error>> {
	let path = PathBuf::from(format!("graphs/{file_name}.svg"));

	// Define ranges
	let x_range: Range<u32> = get_range(&data, |b| b.rounds as u32)
		.ok_or(ChartingError::GetRangeFailed { variable: "x_range"})?;
	let y_range = get_range(&data, |b| b.execution_time.as_secs_f64())
		.ok_or(ChartingError::GetRangeFailed { variable: "y_range"})?;

	let path_clone_bind = path.clone();
	let root = SVGBackend::new(&path_clone_bind, OUTPUT_SIZE)
		.into_drawing_area();
	root.fill(&WHITE)?;

	let mut chart = ChartBuilder::on(&root)
		.x_label_area_size(45)
		.y_label_area_size(60)
		.margin(5)
		.caption("SHA256 STD: SMT Solver Benchmark", (FONT, 36))
		.build_cartesian_2d(x_range, y_range.log_scale().base(2.0))?;

	// Draw X axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_y_axis()
		.x_desc("Compression Rounds")
		.label_style((FONT, 14).with_color(&BLACK))
		.draw()?;

	// Draw Y axis
	chart
		.configure_mesh()
		.disable_mesh()
		.disable_x_axis()
		.y_desc("Time (s)")
		.y_label_formatter(&|&x| format!("2^{}", x.log2()))
		.label_style((FONT, 14).with_color(&BLACK))
		.draw()?;

	let solvers: HashSet<SmtSolver> = data
		.iter()
		.map(|b| b.solver)
		.collect();

	#[derive(Debug, Copy, Clone)]
	struct CartesianWithShape<X, Y> {
		cartesian: (X, Y),
		color: RGBAColor,
	}

	for (i, solver) in solvers.into_iter().enumerate() {
		// Define Cartesian mapped data
		let mut time_data: Vec<_> = data
			.iter()
			.filter(|b| b.solver == solver)
			// .filter(|b| b.result != CPUOut)
			.map(|b| CartesianWithShape {
				cartesian: (b.rounds as u32, b.execution_time.as_secs_f64()),
				color: map_benchmark_to_color(&b.result),
			})
			.collect();

		// Sort by x-axis
		time_data.sort_by_key(|b| b.cartesian.0);

		let color = color_palette[i];
		// TODO: Fix color for legend

		// Draw primary data
		chart
			.draw_series(
				LineSeries::new(
					time_data.clone().iter().map(|c| c.cartesian),
					ShapeStyle {
						color: color.into(),
						filled: false,
						stroke_width: 2,
					}
				).point_size(4))?
			.label(solver.to_string())
			.legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_palette[0]));

		chart.draw_series(
			time_data.iter().map(|c| {
				Circle::new(
					c.cartesian,
					3,
					c.color,
				)
			})
		)?;
	}

	// TODO: Do secondary legend with the result
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

fn map_benchmark_to_color(benchmark_result: &BenchmarkResult) -> RGBAColor {
	use BenchmarkResult::*;

	match benchmark_result {
		Sat => RGBAColor(0, 168, 14, 1.0),
		Unsat => RGBAColor(153, 11, 37, 1.0),
		MemOut | CPUOut => RGBAColor(56, 51, 52, 1.0),
		Aborted | SMTError => RGBAColor(0, 128, 128, 1.0),
		Unknown => RGBAColor(0, 0, 255, 1.0),
	}
}

#[cfg(test)]
mod tests {
	use std::error::Error;
	use std::path::PathBuf;
	use std::time::Duration;
	use plotters::style::RGBColor;
	use crate::structs::benchmark::{Benchmark, BenchmarkResult, SmtSolver};
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
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 16,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1000),
				memory_bytes: 1000,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 17,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1400),
				memory_bytes: 12503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 18,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(5000),
				memory_bytes: 525503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA224,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA224,
				rounds: 20,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(800000),
				memory_bytes: 82550300,
				result: BenchmarkResult::MemOut,
				console_output: (String::new(), String::new()),
			},
		];

		let data = filter_data(benchmarks, SHA224);
		assert_eq!(data.len(), 1);
	}

	#[test]
	fn test_create_time_and_memory_chart() {
		// Mock Data
		let benchmarks = vec![
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 16,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1000),
				memory_bytes: 1000,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 17,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(1400),
				memory_bytes: 12503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 18,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(5000),
				memory_bytes: 525503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
			},
            Benchmark {
				date_time: Default::default(),
				solver: SmtSolver::Z3,
				arguments: vec![],
				hash_function: SHA256,
				rounds: 19,
				collision_type: CollisionType::Standard,
				execution_time: Duration::from_millis(50000),
				memory_bytes: 825503,
				result: BenchmarkResult::Sat,
				console_output: (String::new(), String::new()),
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

		println!("{chart:?}");
		assert!(matches!(chart, Ok(..)));

		cleanup_test(chart);
	}
}
