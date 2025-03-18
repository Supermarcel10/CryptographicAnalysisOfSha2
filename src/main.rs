use crate::structs::collision_type::CollisionType::*;
use crate::structs::hash_function::HashFunction::*;

#[cfg(feature = "benchmarking")] mod benchmarking;
#[cfg(feature = "graphing")] mod graphing;
#[cfg(feature = "smt-gen")] mod smt_lib;
mod sha;
mod verification;
mod structs;

fn main() {}
