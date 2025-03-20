#[cfg(feature = "graphing")] mod graphing;
#[cfg(feature = "smt-gen")] mod smt_lib;
mod sha;
mod verification;
mod structs;

fn main() {
	#[cfg(feature = "smt-gen")]
	{
		use crate::smt_lib::smt_lib::generate_all_smt_files;

		generate_all_smt_files().expect("Failed to generate all SMT files!");
		println!("Generated all files!")
	}
}
