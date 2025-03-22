use crate::sha::HashError;
use crate::structs::hash_function::HashFunction;

pub trait VerifyHash {
	fn verify(&self, hash_function: HashFunction, rounds: u8) -> Result<bool, HashError>;
}
