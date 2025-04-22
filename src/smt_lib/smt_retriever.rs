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
	BruteForceWithSimpifiedFuns,
	DeltaXOR,
	DeltaXORWithSimplifiedFuns,
	DeltaSub,
	DeltaSubWithSimplifiedFuns,
	Base4,
	Base4WithSimplifiedFuns,
}

impl EncodingType {
	pub fn get_diff(&self) -> Result<&str, Box<dyn Error>> {
		use EncodingType::*;
		match self {
			DeltaXOR | DeltaXORWithSimplifiedFuns => Ok("bvxor"),
			DeltaSub | DeltaSubWithSimplifiedFuns => Ok("bvsub"),
			_ => Err(Box::from("get_diff not supported for encoding type")),
		}
	}
}

impl Display for EncodingType {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		use EncodingType::*;

		let et = match self {
			BruteForce => "",
			BruteForceWithSimpifiedFuns => "BRUTE_SIMP",
			DeltaXOR => "DXOR",
			DeltaXORWithSimplifiedFuns => "DXOR_SIMP",
			DeltaSub => "DSUB",
			DeltaSubWithSimplifiedFuns => "DSUB_SIMP",
			Base4 => "BASE4",
			Base4WithSimplifiedFuns => "BASE4_SIMP",
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
