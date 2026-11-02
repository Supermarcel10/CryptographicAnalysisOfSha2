use anyhow::Result;
use sha2_core::sha::Word;
use sha2_core::structs::collision_type::CollisionType;
use sha2_core::structs::hash_function::HashFunction;

pub(super) fn smt_hex(val : Word, hash_function : &HashFunction) -> String {
	let size = hash_function.word_size().bytes() * 2;
	format!("#x{:0size$x}", val)
}

pub(super) fn get_previous_var(var : char) -> Result<char> {
	if var == 'a' {
		Ok('h')
	} else if ('b'..='h').contains(&var) {
		char::from_u32(var as u32 - 1).ok_or_else(|| {
			anyhow::anyhow!(
				"invalid SMT working variable '{var}': failed to compute previous variable"
			)
		})
	} else {
		Err(anyhow::anyhow!(
			"invalid SMT working variable '{var}': expected 'a'..='h'"
		))
	}
}

pub(super) fn msg_prefix(message : u8, i : u64, collision_type : CollisionType) -> String {
	// SemiFreeStart has separate parameters for the 0th iteration
	if i == 0 && collision_type != CollisionType::FreeStart {
		"".to_string()
	} else {
		format!("m{message}_")
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn previous_var_valid_range() {
		assert_eq!(get_previous_var('a').unwrap(), 'h');
		assert_eq!(get_previous_var('b').unwrap(), 'a');
		assert_eq!(get_previous_var('h').unwrap(), 'g');
	}

	#[test]
	fn previous_var_out_of_range_errors() {
		for var in ['z', 'A', '0', '\0'] {
			let err = get_previous_var(var).unwrap_err();
			assert!(
				format!("{err:#}").contains(&format!("'{var}'")),
				"error should name the offending input, got: {err:#}"
			);
		}
	}
}
