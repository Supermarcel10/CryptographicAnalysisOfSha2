use std::fmt::{Display, Formatter};

#[derive(Debug, Eq, PartialEq, Copy, Clone, serde::Serialize, serde::Deserialize)]
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
