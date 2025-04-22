use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


#[derive(Debug, Copy, Clone, Serialize, Deserialize, Eq, PartialEq, clap::ValueEnum)]
pub enum EncodingType {
	BruteForce,
	DeltaXOR,
	DeltaSub,
	Base4,
	Base4WithMajOr,
}

impl EncodingType {
	pub fn get_diff(&self) -> Result<&str, Box<dyn Error>> {
		use EncodingType::*;
		match self {
			DeltaXOR => Ok("bvxor"),
			DeltaSub => Ok("bvsub"),
			_ => Err(Box::from("get_diff not supported for encoding type")),
		}
	}
}

impl Display for EncodingType {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let et = match self {
			EncodingType::BruteForce => "",
			EncodingType::DeltaXOR => "DXOR",
			EncodingType::DeltaSub => "DSUB",
			EncodingType::Base4 => "BASE4",
			EncodingType::Base4WithMajOr => "BASE4+OR",
		};
		write!(f, "{et}")
	}
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

	pub fn get_file(
		&self,
		hash_function: HashFunction,
		collision_type: CollisionType,
		rounds: u8,
		encoding_type: EncodingType,
	) -> PathBuf {
		let mut base = format!("{hash_function}_{collision_type}_{rounds}");
		if encoding_type.to_string().len() > 0 {
			base += &format!("_{encoding_type}");
		}

		self.smt_dir.join(base + ".smt2")
	}
}
