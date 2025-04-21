use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub enum EncodingType {
	BruteForce,
	DeltaXOR,
	Base4,
	Base4WithMajOr,
}

impl Display for EncodingType {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let et = match self {
			EncodingType::BruteForce => "",
			EncodingType::DeltaXOR => "DXOR",
			EncodingType::Base4 => "BASE4",
			EncodingType::Base4WithMajOr => "BASE4+OR",
		};
		write!(f, "{et}")
	}
}

impl EncodingType {

}

pub struct SmtRetriever {
	smt_dir: PathBuf,
}

impl SmtRetriever {
	pub fn new(smt_dir: PathBuf) -> Result<Self, Box<dyn Error>> {
		if !smt_dir.exists() {
			fs::create_dir_all(smt_dir.clone())?;
		}

		Ok(SmtRetriever {
			smt_dir,
		})
	}

	#[allow(dead_code)]
	pub fn default() -> Result<Self, Box<dyn Error>> {
		SmtRetriever::new(PathBuf::from("smt/"))
	}

	pub fn retrieve_file(
		&self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		rounds: u8,
		encoding_type: EncodingType,
	) -> Result<PathBuf, Box<dyn Error>> {
		let file_name = self.get_file_name(
			hash_function,
			collision_type,
			rounds,
			encoding_type
		);

		Ok(self.smt_dir.join(file_name))
	}

	fn get_file_name(
		&self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		rounds: u8,
		encoding_type: EncodingType,
	) -> String {
		let mut base = format!("{hash_function}_{collision_type}_{rounds}");
		if encoding_type.to_string().len() > 0 {
			base += &format!("_{encoding_type}");
		}

		base + ".smt2"
	}
}
