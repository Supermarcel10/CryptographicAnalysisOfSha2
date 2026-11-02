use std::fmt::{Display, Formatter};
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use sha2_core::structs::collision_type::CollisionType;
use sha2_core::structs::hash_function::HashFunction;

use crate::smt_lib::smt_retriever::EncodingType::{Base4, BruteForce, DeltaSub, DeltaXOR};

#[derive(
	Debug,
	Copy,
	Clone,
	Serialize,
	Deserialize,
	Eq,
	PartialEq,
	PartialOrd,
	Ord
)]
pub enum EncodingType {
	BruteForce {
		simplified_maj_and_ch_functions : bool,
		alternative_add : bool
	},
	DeltaXOR {
		simplified_maj_and_ch_functions : bool,
		alternative_add : bool
	},
	DeltaSub {
		simplified_maj_and_ch_functions : bool,
		alternative_add : bool
	},
	Base4 {
		simplified_maj_and_ch_functions : bool,
		alternative_add : bool
	}
}

impl From<EncodingType> for String {
	fn from(encoding : EncodingType) -> Self {
		let mut encoding_str = match encoding {
			BruteForce {
				..
			} => "bruteforce",
			DeltaXOR {
				..
			} => "delta-xor",
			DeltaSub {
				..
			} => "delta-sub",
			Base4 {
				..
			} => "base-4"
		}
		.to_string();

		if encoding.alternative_add() {
			encoding_str.push_str(" bitwise add");
		}

		if encoding.simplified_maj_and_ch_functions() {
			encoding_str.push_str(" simplified MAJ & CH fn");
		}

		encoding_str
	}
}

impl EncodingType {
	pub fn get_diff(&self) -> Result<&str> {
		use EncodingType::*;
		match self {
			DeltaXOR {
				..
			} => Ok("bvxor"),
			DeltaSub {
				..
			} => Ok("bvsub"),
			_ => Err(anyhow::anyhow!("get_diff not supported for encoding type"))
		}
	}

	pub fn simplified_maj_and_ch_functions(&self) -> bool {
		use EncodingType::*;
		*match self {
			BruteForce {
				simplified_maj_and_ch_functions,
				..
			} => simplified_maj_and_ch_functions,
			DeltaXOR {
				simplified_maj_and_ch_functions,
				..
			} => simplified_maj_and_ch_functions,
			DeltaSub {
				simplified_maj_and_ch_functions,
				..
			} => simplified_maj_and_ch_functions,
			Base4 {
				simplified_maj_and_ch_functions,
				..
			} => simplified_maj_and_ch_functions
		}
	}

	pub fn alternative_add(&self) -> bool {
		use EncodingType::*;
		*match self {
			BruteForce {
				alternative_add, ..
			} => alternative_add,
			DeltaXOR {
				alternative_add, ..
			} => alternative_add,
			DeltaSub {
				alternative_add, ..
			} => alternative_add,
			Base4 {
				alternative_add, ..
			} => alternative_add
		}
	}

	pub fn get_all_permutations() -> Vec<Self> {
		let mut vec = Vec::with_capacity(4 * 3);

		for simplified_maj_and_ch_functions in [false, true] {
			for alternative_add in [false, true] {
				vec.push(BruteForce {
					simplified_maj_and_ch_functions,
					alternative_add
				});
				vec.push(DeltaXOR {
					simplified_maj_and_ch_functions,
					alternative_add
				});
				vec.push(DeltaSub {
					simplified_maj_and_ch_functions,
					alternative_add
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

fn parse_bool(s : &str) -> bool {
	matches!(s.to_lowercase().as_str(), "true" | "1" | "yes" | "y")
}

impl FromStr for EncodingType {
	type Err = String;

	fn from_str(s : &str) -> Result<Self, Self::Err> {
		use EncodingType::*;

		let parts : Vec<_> = s.splitn(3, ":").collect();
		let encoding_type_str = parts[0].trim();

		let simplified_maj_and_ch_functions = parts.get(1).is_some_and(|&s| parse_bool(s));

		let alternative_add = parts.get(2).is_some_and(|&s| parse_bool(s));

		match encoding_type_str {
			"bruteforce" => Ok(BruteForce {
				simplified_maj_and_ch_functions,
				alternative_add
			}),
			"dxor" => Ok(DeltaXOR {
				simplified_maj_and_ch_functions,
				alternative_add
			}),
			"dsub" => Ok(DeltaSub {
				simplified_maj_and_ch_functions,
				alternative_add
			}),
			"base4" => Ok(Base4 {
				simplified_maj_and_ch_functions,
				alternative_add
			}),
			_ => Err(format!("Unknown encoding type: {}", encoding_type_str))
		}
	}
}

impl Display for EncodingType {
	fn fmt(&self, f : &mut Formatter<'_>) -> std::fmt::Result {
		use EncodingType::*;

		let (et_name, simplified_maj_and_ch_functions, alternative_add) = match self {
			BruteForce {
				simplified_maj_and_ch_functions,
				alternative_add
			} => ("", *simplified_maj_and_ch_functions, *alternative_add),
			DeltaXOR {
				simplified_maj_and_ch_functions,
				alternative_add
			} => ("DXOR", *simplified_maj_and_ch_functions, *alternative_add),
			DeltaSub {
				simplified_maj_and_ch_functions,
				alternative_add
			} => ("DSUB", *simplified_maj_and_ch_functions, *alternative_add),
			Base4 {
				simplified_maj_and_ch_functions,
				alternative_add
			} => ("BASE4", *simplified_maj_and_ch_functions, *alternative_add)
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
	smt_dir : PathBuf
}

impl SmtRetriever {
	pub fn new(smt_dir : PathBuf) -> Result<Self> {
		if !smt_dir.exists() {
			fs::create_dir_all(&smt_dir)
				.with_context(|| format!("failed to create SMT directory {}", smt_dir.display()))?;
		}

		Ok(SmtRetriever {
			smt_dir
		})
	}

	#[allow(dead_code)]
	pub fn with_default_dir() -> Result<Self> {
		SmtRetriever::new(PathBuf::from("smt/"))
	}

	pub fn get_file(
		&self,
		hash_function : HashFunction,
		collision_type : CollisionType,
		rounds : u8,
		encoding_type : EncodingType
	) -> PathBuf {
		let mut base = format!("{hash_function}_{collision_type}_{rounds}");
		if !encoding_type.to_string().is_empty() {
			base += &format!("_{encoding_type}");
		}

		self.smt_dir.join(base + ".smt2")
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn unique_temp_path(name : &str) -> PathBuf {
		std::env::temp_dir().join(format!("sha2-smt-retriever-{name}-{}", std::process::id()))
	}

	#[test]
	fn from_str_parses_base4_spelling() {
		assert_eq!(
			"base4".parse::<EncodingType>(),
			Ok(Base4 {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			})
		);
		assert_eq!(
			"base4:true:1".parse::<EncodingType>(),
			Ok(Base4 {
				simplified_maj_and_ch_functions : true,
				alternative_add : true
			})
		);
	}

	#[test]
	fn new_creates_missing_dir() {
		let dir = unique_temp_path("missing");
		let _ = std::fs::remove_dir_all(&dir);

		let retriever = SmtRetriever::new(dir.clone()).unwrap();

		assert!(
			dir.exists(),
			"SmtRetriever::new should create {}",
			dir.display()
		);
		assert_eq!(retriever.smt_dir, dir);

		let _ = std::fs::remove_dir_all(&dir);
	}

	#[test]
	fn new_unwritable_dir_reports_path() {
		let blocker = unique_temp_path("blocker");
		std::fs::write(&blocker, "blocker").unwrap();
		let unwritable = blocker.join("subdir");

		let err = SmtRetriever::new(unwritable.clone())
			.err()
			.expect("expected error for unwritable SMT dir");

		assert!(
			format!("{err:#}").contains(&unwritable.display().to_string()),
			"error {err:#} missing path {}",
			unwritable.display()
		);

		let _ = std::fs::remove_file(&blocker);
	}
}
