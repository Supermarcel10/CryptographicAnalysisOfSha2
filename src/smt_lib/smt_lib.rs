use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use crate::sha::{HashError};
use crate::smt_lib::smt_retriever::{EncodingType, SmtRetriever};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;

pub struct SmtBuilder {
	/// Sha defined in SMTLIB2 format
	pub(super) smt: String,
	/// Hash function to use
	pub(super) hash_function: HashFunction,
	/// Number of compression rounds
	pub(super) rounds: u8,
	/// The target collision type
	pub(super) collision_type: CollisionType,
}

impl SmtBuilder {
	fn new(
		hash_function: HashFunction,
		rounds: u8,
		collision_type: CollisionType,
	) -> Result<Self, HashError> {
		hash_function.validate_rounds(rounds)?;

		Ok(SmtBuilder {
			smt: String::new(),
			hash_function,
			rounds,
			collision_type,
		})
	}

	fn to_file(self, file_path: PathBuf) -> Result<File, std::io::Error> {
		let mut file = File::create(file_path)?;

		file.write(self.smt.as_bytes())?;

		Ok(file)
	}

	fn encoding(
		&mut self,
		encoding_type: EncodingType,
	)  -> Result<(), Box<dyn Error>> {
		match encoding_type {
			EncodingType::BruteForce => self.brute_force_encoding(false),
			EncodingType::BruteForceWithSimpifiedFuns => self.brute_force_encoding(true),
			EncodingType::DeltaXOR => self.dxor_encoding(false)?,
			EncodingType::DeltaXORWithSimplifiedFuns => self.dxor_encoding(true)?,
			EncodingType::DeltaSub => self.dsub_encoding(false)?,
			EncodingType::DeltaSubWithSimplifiedFuns => self.dxor_encoding(true)?,
			// EncodingType::Base4 => self.base4_encoding(false)?,
			// EncodingType::Base4WithSimplifiedFuns => self.base4_encoding(true)?,
			_ => {}, // TODO: Implement
		};

		Ok(())
	}
}

pub fn generate_smtlib_files(
	smt_retriever: SmtRetriever,
) -> Result<(), Box<dyn Error>> {
	use HashFunction::*;
	use CollisionType::*;
	use EncodingType::*;

	for hash_function in [SHA224, SHA256, SHA512] {
		for collision_type in [Standard, SemiFreeStart, FreeStart] {
			for encoding in [
				BruteForce,
				BruteForceWithSimpifiedFuns,
				DeltaXOR,
				DeltaXORWithSimplifiedFuns,
				DeltaSub,
				DeltaSubWithSimplifiedFuns,
				// Base4,
				// Base4WithSimplifiedFuns,
			] {
				for rounds in 1..=hash_function.max_rounds() {
					let mut builder = SmtBuilder::new(hash_function, rounds, collision_type)?;
					builder.encoding(encoding)?;

					let file_path = smt_retriever.get_file(
						hash_function,
						collision_type,
						rounds,
						encoding,
					);

					builder.to_file(file_path)?;
				}
			}
		}
	}

	Ok(())
}
