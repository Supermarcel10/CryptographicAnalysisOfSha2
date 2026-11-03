use anyhow::Result;
use sha2_core::structs::collision_type::CollisionType;

use crate::smt_lib::builder::SmtBuilder;

pub trait SmtEncoding {
	/// Differential operator spliced into `delta_*` definitions.
	///
	/// Only the differential section defaults below splice this; absolute
	/// encodings inherit the inert default and never emit it.
	fn diff_op(&self) -> &'static str {
		""
	}

	fn generate(&self, builder : &mut SmtBuilder) -> Result<()> {
		builder.title("SETUP");
		builder.set_logic();

		builder.title("TYPE");
		builder.define_word_type();

		builder.title("FUNCTIONS");
		self.emit_functions(builder)?;

		builder.title("CONSTANTS");
		self.emit_constants(builder)?;

		builder.title("MESSAGE EXPANSION");
		self.emit_expansion(builder)?;

		builder.title("MESSAGE COMPRESSION");
		self.emit_compression(builder)?;

		builder.title("ASSERTIONS");
		self.emit_assertions(builder)?;

		builder.check_sat();
		builder.get_full_model();

		Ok(())
	}

	fn emit_functions(&self, builder : &mut SmtBuilder) -> Result<()> {
		builder.define_functions()
	}

	fn emit_constants(&self, builder : &mut SmtBuilder) -> Result<()> {
		builder.define_constants();
		builder.break_line();
		builder.define_initial_vector();
		builder.define_calculated_differential_initial_vector(self.diff_op())?;

		Ok(())
	}

	fn emit_expansion(&self, builder : &mut SmtBuilder) -> Result<()> {
		builder.define_differential_words(self.diff_op())
	}

	fn emit_compression(&self, builder : &mut SmtBuilder) -> Result<()> {
		builder.define_compression_for_message(0)?;
		builder.break_line();
		builder.define_compression_for_message(1)?;
		builder.break_line();
		builder.define_differential_for_working_variables(self.diff_op())?;
		builder.break_line();
		builder.final_state_update()?;
		builder.break_line();
		builder.define_differential_final_state(self.diff_op())?;

		Ok(())
	}

	fn emit_assertions(&self, builder : &mut SmtBuilder) -> Result<()> {
		if builder.collision_type == CollisionType::FreeStart {
			builder.assert_initial_vector_different();
		} else {
			builder.assert_message_difference();
		}
		builder.break_line();

		builder.assert_hash_difference_equal();

		Ok(())
	}
}
