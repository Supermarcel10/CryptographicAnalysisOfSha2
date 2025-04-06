use std::ops::Range;
use crate::structs::benchmark::Benchmark;


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
