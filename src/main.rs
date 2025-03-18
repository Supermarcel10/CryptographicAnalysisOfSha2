use crate::sha::HashFunction::*;
use crate::structs::collision_type::CollisionType::*;
use crate::smt_lib::smt_lib::SmtBuilder;

#[cfg(feature = "benchmarking")] mod benchmarking;
#[cfg(feature = "graphing")] mod graphing;
mod heuristics;
mod sha;
mod verification;
mod smt_lib;
mod structs;

fn main() {
	for sha_function in [SHA256, SHA512] {
		for collision_type in [Standard, SemiFreeStart, FreeStart] {
			for rounds in 0..sha_function.max_rounds() {
				let mut builder = SmtBuilder::new(sha_function, rounds, collision_type)
					.expect("Failed to create builder!");

				builder.default();

				builder.to_file(format!("data/{sha_function}_{collision_type}_{rounds}.smt2").into())
					.expect("Failed to save file");
			}
		}
	}
}
