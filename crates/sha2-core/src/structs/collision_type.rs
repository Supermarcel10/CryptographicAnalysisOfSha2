use std::fmt::{Display, Formatter};
use std::str::FromStr;

#[derive(
	Debug,
	Eq,
	PartialEq,
	Copy,
	Clone,
	serde::Serialize,
	serde::Deserialize
)]
pub enum CollisionType {
	/// Use the fixed iv for both m0 and m1, where m0 != m1
	Standard,
	/// Use a shared cv for both m0 and m1, where m0 != m1
	SemiFreeStart,
	/// Use cv0 for m0, cv1 for m1, where cv0 != cv1 and m0 ?= m1
	FreeStart
}

impl Display for CollisionType {
	fn fmt(&self, f : &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			CollisionType::Standard => f.write_str("STD"),
			CollisionType::SemiFreeStart => f.write_str("SFS"),
			CollisionType::FreeStart => f.write_str("FS")
		}
	}
}

impl FromStr for CollisionType {
	type Err = ParseCollisionTypeError;

	fn from_str(s : &str) -> Result<Self, Self::Err> {
		match s {
			"std" => Ok(CollisionType::Standard),
			"sfs" => Ok(CollisionType::SemiFreeStart),
			"fs" => Ok(CollisionType::FreeStart),
			_ => Err(ParseCollisionTypeError(s.to_string()))
		}
	}
}

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
#[error("unknown collision type '{0}', expected one of: std, sfs, fs")]
pub struct ParseCollisionTypeError(String);

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn parses_all_variants() {
		assert_eq!(CollisionType::from_str("std"), Ok(CollisionType::Standard));
		assert_eq!(
			CollisionType::from_str("sfs"),
			Ok(CollisionType::SemiFreeStart)
		);
		assert_eq!(CollisionType::from_str("fs"), Ok(CollisionType::FreeStart));
	}

	#[test]
	fn rejects_unknown() {
		assert!(CollisionType::from_str("STD").is_err());
		assert!(CollisionType::from_str("free").is_err());
		assert!(CollisionType::from_str("").is_err());
	}
}
