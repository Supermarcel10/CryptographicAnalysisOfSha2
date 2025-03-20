use std::fmt::{Display, Formatter};

#[cfg_attr(feature = "benchmarking", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum CollisionType {
	/// Use the fixed iv for both m0 and m1, where m0 != m1
	Standard,
	/// Use a shared cv for both m0 and m1, where m0 != m1
	SemiFreeStart,
	/// Use cv0 for m0, cv1 for m1, where cv0 != cv1 and m0 ?= m1
	FreeStart,
}

impl Display for CollisionType {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			CollisionType::Standard => f.write_str("STD"),
			CollisionType::SemiFreeStart => f.write_str("SFS"),
			CollisionType::FreeStart => f.write_str("FS"),
		}
	}
}
