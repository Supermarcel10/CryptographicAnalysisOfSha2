use std::fmt::{Display, Formatter};
use crate::sha::Word;
use crate::structs::sha_state::ShaState;

#[derive(Debug, PartialEq, Clone)]
pub struct HashResult<W: Word> {
	pub hash: Box<[W]>,
	pub states: Vec<ShaState<W>>,
}

impl<W: Word> Display for HashResult<W> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let word_size_bytes = size_of::<W>();
		let width = word_size_bytes * 2;

		for word in self.hash.iter() {
			write!(f, "{word:0width$x} ")?;
		}
		Ok(())
	}
}
