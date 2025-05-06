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
	/// The target encoding type
	pub(super) encoding: EncodingType,
}

impl SmtBuilder {
	fn new(
		hash_function: HashFunction,
		rounds: u8,
		collision_type: CollisionType,
		encoding: EncodingType
	) -> Result<Self, HashError> {
		hash_function.validate_rounds(rounds)?;

		Ok(SmtBuilder {
			smt: String::new(),
			hash_function,
			rounds,
			collision_type,
			encoding,
		})
	}

	fn to_file(self, file_path: PathBuf) -> Result<File, std::io::Error> {
		let mut file = File::create(file_path)?;

		file.write(self.smt.as_bytes())?;

		Ok(file)
	}

	fn write_encoding(&mut self)  -> Result<(), Box<dyn Error>> {
		use EncodingType::*;

		match self.encoding {
			BruteForce { .. } => self.brute_force_encoding()?,
			DeltaXOR { .. } => self.dxor_encoding()?,
			DeltaSub { .. } => self.dsub_encoding()?,
			Base4 { .. } => self.base4_encoding()?,
		};

		Ok(())
	}
}

pub fn generate_smtlib_files(
	smt_retriever: SmtRetriever,
) -> Result<(), Box<dyn Error>> {
	use HashFunction::*;
	use CollisionType::*;

	for hash_function in [SHA224, SHA256, SHA512] {
		for collision_type in [Standard, SemiFreeStart, FreeStart] {
			for encoding in EncodingType::get_all_permutations() {
				for rounds in 1..=hash_function.max_rounds() {
					let mut builder = SmtBuilder::new(
						hash_function,
						rounds,
						collision_type,
						encoding,
					)?;

					builder.write_encoding()?;

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
