use serde::{Deserialize, Serialize};


#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub enum EncodingType {
	BruteForce,
	DeltaXOR,
	Base4,
}
