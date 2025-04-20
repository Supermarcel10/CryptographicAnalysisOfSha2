use std::fmt::{Display, Formatter};
use crate::sha::{HashError, MessageBlock, OutputHash, Sha, StartVector};
use crate::structs::hash_function::HashFunction;
use crate::structs::hash_result::HashResult;
use crate::structs::sha_state::ShaState;
use crate::verification::bit_differential::BitDifferential;
use crate::verification::verify_hash::VerifyHash;

#[derive(Debug)]
pub struct MessageData {
	pub m: MessageBlock,
	pub cv: StartVector,
	pub states: Vec<ShaState>,
	pub expected_hash: OutputHash,
}

impl MessageData {
	fn run_sha(
		&self,
		hash_function: HashFunction,
		rounds: u8
	) -> Result<HashResult, HashError> {
		Sha::from_message_block(
			self.m,
			hash_function,
			rounds,
			self.cv,
		)?.execute()
	}
}

impl VerifyHash for MessageData {
	fn verify(
		&self,
		hash_function: HashFunction,
		rounds: u8,
	) -> Result<bool, HashError> {
		let hash_result = self.run_sha(hash_function, rounds)?;
		Ok(hash_result.hash == self.expected_hash)
	}
}

#[derive(Debug)]
pub struct CollidingPair {
	pub m0: MessageData,
	pub m1: MessageData,
	pub hash_function: HashFunction,
	pub rounds: u8,
}

impl CollidingPair {
	pub fn verify(&self) -> Result<bool, HashError> {
		let is_m0_hash_same = self.m0.verify(self.hash_function, self.rounds)?;
		let is_m1_hash_same = self.m0.verify(self.hash_function, self.rounds)?;

		Ok(is_m0_hash_same && is_m1_hash_same)
	}
}

impl Display for CollidingPair {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let is_m0_hash_same = self.m0.verify(self.hash_function, self.rounds).unwrap_or(false);
		let is_m1_hash_same = self.m1.verify(self.hash_function, self.rounds).unwrap_or(false);

		let mut mismatch_info = String::new();
		if !is_m0_hash_same {
			match self.m0.run_sha(self.hash_function, self.rounds) {
				Ok(result) => mismatch_info += &format!("\nActual Hash: {}", result.hash),
				Err(_) => mismatch_info += "\nUnable to retrieve actual hash for M!",
			}
		}

		if !is_m1_hash_same {
			match self.m1.run_sha(self.hash_function, self.rounds) {
				Ok(result) => mismatch_info += &format!("\nActual Hash': {}", result.hash),
				Err(_) => mismatch_info += "\nUnable to retrieve actual hash for M'!",
			}
		}

		if mismatch_info.len() > 0 {
			mismatch_info += "\n";
		}

		let hash_message = format!(
			"Hash : {} (Valid? {})\nHash': {} (Valid? {})\n{}",
			self.m0.expected_hash,
			is_m0_hash_same,
			self.m1.expected_hash,
			is_m1_hash_same,
			mismatch_info,
		);

		write!(f, "CV   : {}\n", self.m0.cv)?;
		write!(f, "CV'  : {}\n", self.m1.cv)?;
		write!(f, "M    : {}\n", self.m0.m)?;
		write!(f, "M'   : {}\n", self.m1.m)?;
		write!(f, "{hash_message}\n\n")?;
		write!(f, "{}", self.m0.states.clone().bit_diff(self.m1.states.clone()))?;
		Ok(())
	}
}
