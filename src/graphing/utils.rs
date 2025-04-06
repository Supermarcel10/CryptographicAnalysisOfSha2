use std::ops::Range;
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
// TODO: Look into why Range<u8> does not work?
//? Potential issue in plotters.rs?
//? Range<u8> and Range<u16> don't implement plotters::prelude::Ranged as expected?
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
