use std::fmt::{Display, Formatter};
use crate::sha::{HashError, MessageBlock, OutputHash, Sha, StartVector};
use crate::structs::hash_function::HashFunction;
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

impl VerifyHash for MessageData {
	fn verify(
		&self,
		hash_function: HashFunction,
		rounds: u8
	) -> Result<bool, HashError> {
		let hash_result = Sha::from_message_block(
			self.m,
			hash_function,
			rounds,
			self.cv,
		)?.execute()?;

		Ok(hash_result.hash == self.expected_hash)
	}
}

#[derive(Debug)]
pub struct CollidingPair {
	pub m0: MessageData,
	pub m1: MessageData,
	pub verified_hash: Option<OutputHash>,
}

impl VerifyHash for CollidingPair {
	fn verify(&self, hash_function: HashFunction, rounds: u8) -> Result<bool, HashError> {
		let m0_valid_hash = self.m0.verify(hash_function, rounds)?;
		let m1_valid_hash = self.m1.verify(hash_function, rounds)?;
		println!("{}", m0_valid_hash);
		println!("{}", m1_valid_hash);

		Ok(m0_valid_hash && m1_valid_hash)
	}
}

impl Display for CollidingPair {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let is_m0_hash_same = self.verified_hash.is_some() && self.m0.expected_hash == self.verified_hash.clone().unwrap();
		let is_m1_hash_same = self.verified_hash.is_some() && self.m1.expected_hash == self.verified_hash.clone().unwrap();

		let mut hash_message = format!(
			"Hash : {} (Valid? {})\nHash': {} (Valid? {})",
			self.m0.expected_hash,
			is_m0_hash_same,
			self.m1.expected_hash,
			is_m1_hash_same,
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
