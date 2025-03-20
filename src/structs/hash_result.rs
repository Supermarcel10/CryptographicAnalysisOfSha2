use crate::sha::Word;
use crate::structs::sha_state::ShaState;

#[derive(Debug, PartialEq, Clone)]
pub struct HashResult {
	pub hash: Box<[Word]>,
	pub states: Vec<ShaState>,
}
