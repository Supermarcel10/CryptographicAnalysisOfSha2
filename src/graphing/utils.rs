use std::ops::{Add, Range};
use num_traits::One;
use crate::structs::benchmark::Benchmark;


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
			if v > max_agg { v } else { max_agg }
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
pub(super) fn split_data<XT, YT>(
	data: Vec<(XT, YT)>
) -> Vec<Vec<(XT, YT)>>
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
