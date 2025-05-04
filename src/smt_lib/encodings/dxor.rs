use std::error::Error;
use crate::smt_lib::smt_lib::SmtBuilder;
use crate::structs::collision_type::CollisionType;


impl SmtBuilder {
	pub fn dxor_encoding(&mut self) -> Result<(), Box<dyn Error>> {
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions();

		self.title("CONSTANTS");
		self.define_constants();
		self.break_line();
		self.define_initial_vector();
		self.define_calculated_differential_initial_vector()?;

		self.title("MESSAGE EXPANSION");
		self.define_differential_words()?;

		self.title("MESSAGE COMPRESSION");
		self.define_compression_for_message(0);
		self.break_line();
		self.define_compression_for_message(1);
		self.break_line();
		self.define_differential_for_working_variables()?;

		self.break_line();
		self.final_state_update();
		self.break_line();
		self.define_differential_final_state()?;

		self.title("ASSERTIONS");
		if self.collision_type == CollisionType::FreeStart {
			self.assert_initial_vector_different();
		} else {
			self.assert_message_difference();
		}
		self.break_line();

		self.assert_hash_difference_equal();

		self.check_sat();
		self.get_full_model();

		Ok(())
	}
}
