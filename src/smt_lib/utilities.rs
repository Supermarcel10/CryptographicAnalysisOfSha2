use crate::sha::Word;
use crate::structs::collision_type::CollisionType;
use crate::structs::hash_function::HashFunction;

pub(super) fn smt_hex(val: Word, hash_function: &HashFunction) -> String {
	let size = hash_function.word_size().bytes() * 2;
	format!("#x{:0size$x}", val)
}

pub(super) fn get_previous_var(var: char) -> char {
	if var == 'a' {
		'h'
	} else {
		char::from_u32(var as u32 - 1).unwrap()
	}
}

pub(super) fn msg_prefix(
	message: u8,
	i: u64,
	collision_type: CollisionType,
) -> String {
	// SemiFreeStart has separate parameters for the 0th iteration
	if i == 0 && collision_type != CollisionType::FreeStart {
		"".to_string()
	} else {
		format!("m{message}_")
	}
}
