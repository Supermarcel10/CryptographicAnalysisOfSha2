use std::fmt::{Display, Formatter};

use anyhow::Result;
use sha2_core::bit_differential::BitDifferential;
use sha2_core::sha::{MessageBlock, OutputHash, Sha, StartVector};
use sha2_core::structs::hash_function::HashFunction;
use sha2_core::structs::hash_result::HashResult;
use sha2_core::structs::sha_state::ShaState;

use crate::verify_hash::VerifyHash;

#[derive(Debug)]
pub struct MessageData {
	pub m : MessageBlock,
	pub cv : StartVector,
	pub states : Vec<ShaState>,
	pub expected_hash : OutputHash
}

impl MessageData {
	fn run_sha(&self, hash_function : HashFunction, rounds : u8) -> Result<HashResult> {
		Sha::from_message_block(self.m, hash_function, rounds, self.cv)?.execute()
	}
}

impl VerifyHash for MessageData {
	fn verify(&self, hash_function : HashFunction, rounds : u8) -> Result<bool> {
		let hash_result = self.run_sha(hash_function, rounds)?;
		Ok(hash_result.hash == self.expected_hash)
	}
}

#[derive(Debug)]
pub struct CollidingPair {
	pub m0 : MessageData,
	pub m1 : MessageData,
	pub hash_function : HashFunction,
	pub rounds : u8
}

impl CollidingPair {
	pub fn verify(&self) -> Result<bool> {
		let is_m0_hash_same = self.m0.verify(self.hash_function, self.rounds)?;
		let is_m1_hash_same = self.m0.verify(self.hash_function, self.rounds)?;

		Ok(is_m0_hash_same && is_m1_hash_same)
	}
}

impl Display for CollidingPair {
	fn fmt(&self, f : &mut Formatter<'_>) -> std::fmt::Result {
		let is_m0_hash_same = self
			.m0
			.verify(self.hash_function, self.rounds)
			.unwrap_or(false);
		let is_m1_hash_same = self
			.m1
			.verify(self.hash_function, self.rounds)
			.unwrap_or(false);

		let mut mismatch_info = String::new();
		if !is_m0_hash_same {
			match self.m0.run_sha(self.hash_function, self.rounds) {
				Ok(result) => mismatch_info += &format!("\nActual Hash: {}", result.hash),
				Err(_) => mismatch_info += "\nUnable to retrieve actual hash for M!"
			}
		}

		if !is_m1_hash_same {
			match self.m1.run_sha(self.hash_function, self.rounds) {
				Ok(result) => mismatch_info += &format!("\nActual Hash': {}", result.hash),
				Err(_) => mismatch_info += "\nUnable to retrieve actual hash for M'!"
			}
		}

		if !mismatch_info.is_empty() {
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

		writeln!(f, "CV   : {}", self.m0.cv)?;
		writeln!(f, "CV'  : {}", self.m1.cv)?;
		writeln!(f, "M    : {}", self.m0.m)?;
		writeln!(f, "M'   : {}", self.m1.m)?;
		write!(f, "{hash_message}\n\n")?;
		write!(
			f,
			"{}",
			self.m0.states.clone().bit_diff(self.m1.states.clone())
		)?;
		Ok(())
	}
}
