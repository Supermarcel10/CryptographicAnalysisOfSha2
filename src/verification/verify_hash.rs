use sha2_core::sha::HashError;
use sha2_core::structs::hash_function::HashFunction;

pub trait VerifyHash {
	fn verify(&self, hash_function: HashFunction, rounds: u8) -> Result<bool, HashError>;
}
