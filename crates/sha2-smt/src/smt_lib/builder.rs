use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::{Context, Result};
use sha2_core::structs::collision_type::CollisionType;
use sha2_core::structs::hash_function::HashFunction;

use crate::smt_lib::encodings::base4::Base4Encoding;
use crate::smt_lib::encodings::brute_force::BruteForceEncoding;
use crate::smt_lib::encodings::dsub::DsubEncoding;
use crate::smt_lib::encodings::dxor::DxorEncoding;
use crate::smt_lib::encodings::encoding::SmtEncoding;
use crate::smt_lib::smt_retriever::{EncodingType, SmtRetriever};

pub struct SmtBuilder {
	/// Sha defined in SMTLIB2 format
	pub(super) smt : String,
	/// Hash function to use
	pub(super) hash_function : HashFunction,
	/// Number of compression rounds
	pub(super) rounds : u8,
	/// The target collision type
	pub(super) collision_type : CollisionType,
	/// The target encoding type
	pub(super) encoding : EncodingType
}

impl SmtBuilder {
	fn new(
		hash_function : HashFunction,
		rounds : u8,
		collision_type : CollisionType,
		encoding : EncodingType
	) -> Result<Self> {
		hash_function.validate_rounds(rounds)?;

		Ok(SmtBuilder {
			smt : String::new(),
			hash_function,
			rounds,
			collision_type,
			encoding
		})
	}

	fn to_file(&self, file_path : PathBuf) -> Result<File> {
		let mut file = File::create(&file_path)
			.with_context(|| format!("failed to create SMT file {}", file_path.display()))?;

		file.write_all(self.smt.as_bytes())
			.with_context(|| format!("failed to write SMT file {}", file_path.display()))?;

		Ok(file)
	}

	fn write_encoding(&mut self) -> Result<()> {
		use EncodingType::*;

		match self.encoding {
			BruteForce {
				..
			} => BruteForceEncoding.generate(self),
			DeltaXOR {
				..
			} => DxorEncoding.generate(self),
			DeltaSub {
				..
			} => DsubEncoding.generate(self),
			Base4 {
				..
			} => Base4Encoding.generate(self)
		}
	}
}

pub fn generate_smtlib_files(smt_retriever : SmtRetriever) -> Result<()> {
	use CollisionType::*;
	use HashFunction::*;

	for hash_function in [SHA224, SHA256, SHA512] {
		for collision_type in [Standard, SemiFreeStart, FreeStart] {
			for encoding in EncodingType::get_all_permutations() {
				for rounds in 1..=hash_function.max_rounds() {
					let mut builder =
						SmtBuilder::new(hash_function, rounds, collision_type, encoding)?;

					builder.write_encoding()?;

					let file_path =
						smt_retriever.get_file(hash_function, collision_type, rounds, encoding);

					builder.to_file(file_path)?;
				}
			}
		}
	}

	Ok(())
}
