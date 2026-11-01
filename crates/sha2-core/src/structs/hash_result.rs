use crate::sha::OutputHash;
use crate::structs::sha_state::ShaState;

#[derive(Debug, PartialEq, Clone)]
pub struct HashResult {
	pub hash: OutputHash,
	pub states: Vec<ShaState>,
}
