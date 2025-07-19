use crate::graphing::custom_point_styles::CustomShape;
use crate::structs::benchmark::{Benchmark, BenchmarkResult};
use num_traits::One;
use plotters::backend::DrawingBackend;
use plotters::chart::SeriesAnno;
use plotters::element::PathElement;
use plotters::prelude::RGBAColor;
use std::ops::{Add, Range};

/// Utility method to retrieve the range of a given data set for any numerical data.
///
/// # Arguments
///
/// * `data`: Data to retrieve range for.
/// * `retr`: Retriever lambda to define which field and how to map it.
///
/// # Returns
/// `Option<Range<T>>`
///
/// Returns `None` if length 0 data provided, otherwise provides a range of the retrieved data type.
// Potential bug/oversight with plotters.rs?
// Range<u8> and Range<u16> don't implement plotters::prelude::Ranged as expected?
pub(super) fn get_range<T: Copy + PartialOrd>(
	data: &Vec<Benchmark>,
	retr: &dyn Fn(&Benchmark) -> T,
) -> Option<Range<T>> {
	let mut it = data.into_iter();
	let first = retr(it.next()?);
	let (min, max) = it.fold((first, first), |(min_agg, max_agg), b| {
		let v = retr(b);
		(
			if v < min_agg { v } else { min_agg },
			if v > max_agg { v } else { max_agg },
		)
	});

	Some(min..max)
}

/// Splits a data set to multiple segments.
/// This is useful when there is a gap in the data which is meant to be rendered as disjoint.
///
/// # Arguments
///
/// * `data`: Data to split.
///
/// # Returns
/// Vec<Vec<(XT, YT), Global>, Global>
///
/// A set of continious cartesian data.
pub(super) fn split_data<XT, YT>(data: Vec<(XT, YT)>) -> Vec<Vec<(XT, YT)>>
where
	XT: Clone + Copy + Add<Output = XT> + PartialOrd + One + 'static,
	YT: Clone + 'static,
{
	if data.is_empty() {
		return vec![];
	}

	let mut segments = Vec::new();
	let mut current_segment = Vec::new();
	current_segment.push(data[0].clone());

	for window in data.windows(2) {
		let (x1, _) = window[0];
		let (x2, _) = window[1];

		if x2 > x1 + XT::one() {
			segments.push(current_segment);
			current_segment = Vec::new();
		}

		current_segment.push(window[1].clone());
	}

	if !current_segment.is_empty() {
		segments.push(current_segment);
	}

	segments
}

pub(super) fn ensure_defined_only_once<'a, DB>(
	label: &str,
	color: RGBAColor,
	was_legend_defined: &mut bool,
	series: &mut SeriesAnno<DB>,
) where
	DB: DrawingBackend + 'a,
	DB::ErrorType: 'static,
{
	if !*was_legend_defined {
		*was_legend_defined = true;
		series
			.label(label)
			.legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));
	}
}

pub(super) fn classify_benchmark_result_to_point_style(result: BenchmarkResult) -> CustomShape {
	use CustomShape::*;
	use BenchmarkResult::*;

	match result {
		Sat => Circle,
		Unsat => Cross,
		MemOut => Triangle,
		CPUOut => Triangle,
		_ => None,
	}
}

pub(super) fn classify_benchmark_results_to_point_styles(
	result: Vec<BenchmarkResult>,
) -> Vec<CustomShape> {
	result
		.into_iter()
		.map(classify_benchmark_result_to_point_style)
		.collect()
}
