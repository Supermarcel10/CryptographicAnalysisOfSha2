use std::error::Error;
use std::fmt::{Display, Formatter};
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;
use serde::{Deserialize, Serialize};
use crate::smt_lib::smt_retriever::EncodingType::{Base4, BruteForce, DeltaSub, DeltaXOR};
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;


#[derive(Debug, Copy, Clone, Serialize, Deserialize, Eq, PartialEq, )]
pub enum EncodingType {
	BruteForce {
		simplified_maj_and_ch_functions: bool,
		alternative_add: bool,
	},
	DeltaXOR {
		simplified_maj_and_ch_functions: bool,
		alternative_add: bool,
	},
	DeltaSub {
		simplified_maj_and_ch_functions: bool,
		alternative_add: bool,
	},
	Base4 {
		simplified_maj_and_ch_functions: bool,
		alternative_add: bool,
	},
}

impl EncodingType {
	pub fn get_diff(&self) -> Result<&str, Box<dyn Error>> {
		use EncodingType::*;
		match self {
			DeltaXOR { .. } => Ok("bvxor"),
			DeltaSub { .. } => Ok("bvsub"),
			_ => Err(Box::from("get_diff not supported for encoding type")),
		}
	}

	pub fn simplified_maj_and_ch_functions(&self) -> bool {
		use EncodingType::*;
		*match self {
			BruteForce { simplified_maj_and_ch_functions, .. } => simplified_maj_and_ch_functions,
			DeltaXOR { simplified_maj_and_ch_functions, .. } => simplified_maj_and_ch_functions,
			DeltaSub { simplified_maj_and_ch_functions, .. } => simplified_maj_and_ch_functions,
			Base4 { simplified_maj_and_ch_functions, .. } => simplified_maj_and_ch_functions,
		}
	}

	pub fn alternative_add(&self) -> bool {
		use EncodingType::*;
		*match self {
			BruteForce { alternative_add, .. } => alternative_add,
			DeltaXOR { alternative_add, .. } => alternative_add,
			DeltaSub { alternative_add, .. } => alternative_add,
			Base4 { alternative_add, .. } => alternative_add,
		}
	}

	pub fn get_all_permutations() -> Vec<Self> {
		let mut vec = Vec::with_capacity(4 * 3);

		for simplified_maj_and_ch_functions in [false, true] {
			for alternative_add in [false, true] {
				vec.push(BruteForce {
					simplified_maj_and_ch_functions,
					alternative_add,
				});
				vec.push(DeltaXOR {
					simplified_maj_and_ch_functions,
					alternative_add,
				});
				vec.push(DeltaSub {
					simplified_maj_and_ch_functions,
					alternative_add,
				});
				// TODO: Uncomment once implemented
				// vec.push(Base4 {
				// 	simplified_maj_and_ch_functions,
				// 	alternative_add,
				// });
			}
		}

		vec
	}
}

fn parse_bool(s: &str) -> bool {
	match s.to_lowercase().as_str() {
		"true" | "1" | "yes" | "y" => true,
		_ => false,
	}
}

impl FromStr for EncodingType {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		use EncodingType::*;

		let parts: Vec<_> = s.splitn(3, ":").collect();
		let encoding_type_str = parts[0].trim();

		let simplified_maj_and_ch_functions = parts
			.get(1)
			.map_or(false, |&s| parse_bool(s));

		let alternative_add = parts
			.get(2)
			.map_or(false, |&s| parse_bool(s));

		match encoding_type_str {
			"bruteforce" => {
				Ok(BruteForce {
					simplified_maj_and_ch_functions,
					alternative_add,
				})
			},
			"dxor" => {
				Ok(DeltaXOR {
					simplified_maj_and_ch_functions,
					alternative_add,
				})
			},
			"dsub" => {
				Ok(DeltaSub {
					simplified_maj_and_ch_functions,
					alternative_add,
				})
			},
			"base4" => {
				Ok(Base4 {
					simplified_maj_and_ch_functions,
					alternative_add,
				})
			},
			_ => Err(format!("Unknown encoding type: {}", encoding_type_str)),
		}
	}
}

impl Display for EncodingType {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		use EncodingType::*;

		let (et_name, simplified_maj_and_ch_functions, alternative_add) = match self {
			BruteForce { simplified_maj_and_ch_functions, alternative_add } =>
				("", *simplified_maj_and_ch_functions, *alternative_add),
			DeltaXOR { simplified_maj_and_ch_functions, alternative_add } =>
				("DXOR", *simplified_maj_and_ch_functions, *alternative_add),
			DeltaSub { simplified_maj_and_ch_functions, alternative_add } =>
				("DSUB", *simplified_maj_and_ch_functions, *alternative_add),
			Base4 { simplified_maj_and_ch_functions, alternative_add } =>
				("BASE4", *simplified_maj_and_ch_functions, *alternative_add),
		};

		let mut s = String::from(et_name);

		if simplified_maj_and_ch_functions {
			if !s.is_empty() {
				s.push('_');
			}

			s += "SIMP";
		}

		if alternative_add {
			if !s.is_empty() {
				s.push('_');
			}

			s += "ALTADD";
		}

		write!(f, "{s}")
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
