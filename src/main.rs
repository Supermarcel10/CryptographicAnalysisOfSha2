use std::cmp::PartialEq;
use bitvec::prelude::*;
use crate::structs::Word;

mod structs;
mod solver;


fn main() {
	// Rotate
	// {
	// 	let word = Word::new(3u64);
	// 	println!("Word is {word:?}");
	//
	// 	let mut clone = word.clone();
	// 	clone.rotate_right(2);
	// 	println!("Clone the same after ROTR(2)? {}", word == clone);
	//
	// 	clone.rotate_left(2);
	// 	println!("Clone the same after ROTL(2)? {}", word == clone);
	//
	// 	println!("Size is {} bytes", size_of_val(&word));
	// }

	// Add
	// {
	// 	let mut word1 = Word::new(3u32);
	// 	let word2 = Word::new(5u32);
	// 	print!("{word1} + {word2} = ");
	// 	word1.add(word2);
	// 	println!("{word1}");
	// }

	// Add with overflow
	// {
	// 	let mut word1 = Word::new(255u8);
	// 	let word2 = Word::new(5u8);
	// 	println!("{}", word1);
	// 	println!("{}", word2);
	//
	// 	word1.add(word2);
	// 	println!("{word1}");
	// }

	// And
	// {
	// 	let mut word1 = Word::new(3u8); // 0011
	// 	let word2 = Word::new(1u8); // 0001
	//
	// 	word1.and(word2);
	// 	println!("{word1:?}"); // 0001
	// }

	// Or
	// {
	// 	let mut word1 = Word::new(2u8); // 0010
	// 	let word2 = Word::new(1u8); // 0001
	//
	// 	word1.or(word2);
	// 	println!("{word1}") // 0011
	// }

	// Xor
	// {
	// 	let mut word1 = Word::new(3u8); // 0011
	// 	let word2 = Word::new(1u8); // 0001
	//
	// 	word1.xor(word2);
	// 	println!("{word1}") // 0010
	// }

	// Not
	// {
	// 	let mut word = Word::new(2u8);
	// 	word.not();
	// 	println!("{word}");
	// }
}
