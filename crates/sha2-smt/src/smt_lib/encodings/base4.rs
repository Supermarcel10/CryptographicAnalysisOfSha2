use anyhow::Result;
use sha2_core::structs::collision_type::CollisionType;

use crate::smt_lib::builder::SmtBuilder;
use crate::smt_lib::encodings::encoding::SmtEncoding;
use crate::smt_lib::utilities::msg_prefix;

pub struct Base4Encoding;

impl SmtEncoding for Base4Encoding {
	fn generate(&self, builder : &mut SmtBuilder) -> Result<()> {
		// Full-section override: base-4's 4-way structure inserts CONDITIONS
		// and PROPAGATION sections with no default-hook equivalent.
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

		builder.title("BASE-4 CONDITIONS");
		builder.define_base4_conditions();

		builder.title("BASE-4 PROPAGATION LEMMAS");
		builder.assert_base4_propagation_lemmas();

		builder.title("ASSERTIONS");
		self.emit_assertions(builder)?;

		builder.check_sat();
		builder.get_full_model();

		Ok(())
	}

	fn emit_functions(&self, builder : &mut SmtBuilder) -> Result<()> {
		// Base-4 prepends its proven b4band/b4bor/b4bxor definitions.
		builder.define_base4_functions();
		builder.break_line();
		builder.define_functions()
	}

	fn emit_constants(&self, builder : &mut SmtBuilder) -> Result<()> {
		// No differential IV: base-4 tracks message pairs, not delta words.
		builder.define_constants();
		builder.break_line();
		builder.define_initial_vector();

		Ok(())
	}

	fn emit_expansion(&self, builder : &mut SmtBuilder) -> Result<()> {
		// Absolute schedule only: base-4 conditions derive from word pairs.
		builder.define_expansion_for_message(0);
		builder.break_line();
		builder.define_expansion_for_message(1);

		Ok(())
	}

	fn emit_compression(&self, builder : &mut SmtBuilder) -> Result<()> {
		// No differential working variables or final state in base-4.
		builder.define_compression_for_message(0)?;
		builder.break_line();
		builder.define_compression_for_message(1)?;
		builder.break_line();
		builder.final_state_update()?;

		Ok(())
	}

	fn emit_assertions(&self, builder : &mut SmtBuilder) -> Result<()> {
		// 4-way asserts pair absolute and mask conditions per word.
		if builder.collision_type == CollisionType::FreeStart {
			builder.assert_initial_vector_not_same_base4();
		} else {
			builder.assert_messages_not_same_base4();
		}
		builder.break_line();

		builder.assert_hash_same_base4();

		Ok(())
	}
}

impl SmtBuilder {
	fn b4_ones(&self) -> String {
		format!("#b{}", "1".repeat(self.hash_function.word_size().bits()))
	}

	/// Absolute SMT expression of working variable `var` of `message` at `round`.
	fn b4_abs(&self, message : u8, var : char, round : u64) -> String {
		format!(
			"{}{var}{round}",
			msg_prefix(message, round, self.collision_type)
		)
	}

	fn define_base4_functions(&mut self) {
		self.comment(
			"Base-4 AND/OR/XOR condition propagation (proven in proofs/encoding_{and,or,xor}.smt2)"
		);

		// AND: d = Xd&Yd; b = (Xf&Yf)&~d; c = (Xg&Yg)&~d; a = ~(d|b|c).
		self.smt += "(define-fun b4band_b ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvand (bvor Xb Xd) (bvor Yb Yd) (bvnot (bvand Xd Yd))))\n";
		self.smt += "(define-fun b4band_c ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvand (bvor Xc Xd) (bvor Yc Yd) (bvnot (bvand Xd Yd))))\n";
		self.smt += "(define-fun b4band_d ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvand Xd Yd))\n";
		self.smt += "(define-fun b4band_a ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvnot (bvor (b4band_d Xa Xb Xc Xd Ya Yb Yc Yd) (b4band_b Xa Xb Xc Xd Ya Yb Yc Yd) (b4band_c Xa Xb Xc Xd Ya Yb Yc Yd))))\n";

		// OR: a = Xa&Ya; b = ~(Xg|Yg|a); c = ~(Xf|Yf|a); d = ~(a|b|c)
		self.smt += "(define-fun b4bor_a ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvand Xa Ya))\n";
		self.smt += "(define-fun b4bor_b ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvnot (bvor (bvor Xc Xd) (bvor Yc Yd) (bvand Xa Ya))))\n";
		self.smt += "(define-fun b4bor_c ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvnot (bvor (bvor Xb Xd) (bvor Yb Yd) (bvand Xa Ya))))\n";
		self.smt += "(define-fun b4bor_d ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvnot (bvor (b4bor_a Xa Xb Xc Xd Ya Yb Yc Yd) (b4bor_b Xa Xb Xc Xd Ya Yb Yc Yd) (b4bor_c Xa Xb Xc Xd Ya Yb Yc Yd))))\n";

		// XOR: pairwise matching of (a, b, c, d) membership
		self.smt += "(define-fun b4bxor_a ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvor (bvand Xa Ya) (bvand Xb Yb) (bvand Xc Yc) (bvand Xd Yd)))\n";
		self.smt += "(define-fun b4bxor_b ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvor (bvand Xa Yb) (bvand Xb Ya) (bvand Xc Yd) (bvand Xd Yc)))\n";
		self.smt += "(define-fun b4bxor_c ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvor (bvand Xa Yc) (bvand Xc Ya) (bvand Xb Yd) (bvand Xd Yb)))\n";
		self.smt += "(define-fun b4bxor_d ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word
	(bvor (bvand Xa Yd) (bvand Xd Ya) (bvand Xb Yc) (bvand Xc Yb)))\n";
	}

	fn define_base4_pair(&mut self, tag : &str, left : &str, right : &str) {
		self.smt += &format!(
			"(define-fun B4_{tag}_A () Word (bvand (bvnot {left}) (bvnot {right})))\n\
			(define-fun B4_{tag}_B () Word (bvand (bvnot {left}) {right}))\n\
			(define-fun B4_{tag}_C () Word (bvand {left} (bvnot {right})))\n\
			(define-fun B4_{tag}_D () Word (bvand {left} {right}))\n"
		);
	}

	fn define_base4_conditions(&mut self) {
		self.comment("Base-4 condition masks for the chaining value");
		for var in 'a'..='h' {
			let (left, right) = match self.collision_type {
				CollisionType::FreeStart => (format!("m0_{var}0"), format!("m1_{var}0")),
				_ => {
					let shared = format!("{var}0");
					(shared.clone(), shared)
				}
			};
			self.define_base4_pair(&format!("cv_{var}"), &left, &right);
		}

		self.break_line();
		self.comment("Base-4 condition masks for the message schedule");
		for i in 0..self.rounds {
			self.define_base4_pair(&format!("w{i}"), &format!("m0_w{i}"), &format!("m1_w{i}"));
		}

		if self.rounds > 0 {
			self.break_line();
			self.comment("Base-4 condition masks for the working variables");
			for i in 1..=self.rounds {
				for var in 'a'..='h' {
					let left = self.b4_abs(0, var, i.into());
					let right = self.b4_abs(1, var, i.into());
					self.define_base4_pair(&format!("s{var}{i}"), &left, &right);
				}
			}
		}

		self.break_line();
		self.comment("Base-4 condition masks for the final hash");
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for i in 0..final_size {
			self.define_base4_pair(
				&format!("hash{i}"),
				&format!("m0_hash{i}"),
				&format!("m1_hash{i}")
			);
		}
	}

	fn assert_base4_propagation_lemmas(&mut self) {
		let comb = if self.encoding.simplified_maj_and_ch_functions() {
			"b4bor"
		} else {
			"b4bxor"
		};

		for i in 1..=self.rounds {
			let p : u64 = (i - 1).into();
			let ct = self.collision_type;

			// Absolute inputs of both messages.
			let inputs = |var : char| {
				(
					format!("{}{var}{p}", msg_prefix(0, p, ct)),
					format!("{}{var}{p}", msg_prefix(1, p, ct))
				)
			};

			// Condition masks of the input pair.
			let masks = |var : char| {
				let tag = if var == 'w' {
					format!("w{p}")
				} else if p == 0 {
					format!("cv_{var}")
				} else {
					format!("s{var}{p}")
				};
				[
					format!("B4_{tag}_A"),
					format!("B4_{tag}_B"),
					format!("B4_{tag}_C"),
					format!("B4_{tag}_D")
				]
			};

			// Combined two mask quadruples with the given operator family.
			let combine = |op : &str, x : &[String; 4], y : &[String; 4]| {
				['a', 'b', 'c', 'd'].map(|o| {
					format!(
						"({op}_{o} {} {} {} {} {} {} {} {})",
						x[0], x[1], x[2], x[3], y[0], y[1], y[2], y[3]
					)
				})
			};

			// Actual masks of the absolute output pair (out0, out1).
			let actual = |out0 : &str, out1 : &str| {
				[
					format!("(bvand (bvnot {out0}) (bvnot {out1}))"),
					format!("(bvand (bvnot {out0}) {out1})"),
					format!("(bvand {out0} (bvnot {out1}))"),
					format!("(bvand {out0} {out1})")
				]
			};

			// Ch(e, f, g)
			{
				let (e0, e1) = inputs('e');
				let (f0, f1) = inputs('f');
				let (g0, g1) = inputs('g');
				let (e, f, g) = (masks('e'), masks('f'), masks('g'));
				// ~e swaps a<->d and b<->c.
				let not_e : [String; 4] = [e[3].clone(), e[2].clone(), e[1].clone(), e[0].clone()];

				let t1 = combine("b4band", &e, &f);
				let t2 = combine("b4band", &not_e, &g);
				let ch = combine(comb, &t1, &t2);
				let [ca, cb, cc, cd] = actual(
					&format!("(ch {e0} {f0} {g0})"),
					&format!("(ch {e1} {f1} {g1})")
				);

				self.smt += &format!(
					"; Base-4 Ch propagation, round {i}\n\
					(assert (= {cha} {ca}))\n\
					(assert (= {chb} {cb}))\n\
					(assert (= {chc} {cc}))\n\
					(assert (= {chd} {cd}))\n",
					cha = ch[0],
					chb = ch[1],
					chc = ch[2],
					chd = ch[3]
				);
			}

			// Maj(a, b, c)
			{
				let (a0, a1) = inputs('a');
				let (b0, b1) = inputs('b');
				let (c0, c1) = inputs('c');
				let (a, b, c) = (masks('a'), masks('b'), masks('c'));

				let t_ab = combine("b4band", &a, &b);
				let t_ac = combine("b4band", &a, &c);
				let t_bc = combine("b4band", &b, &c);
				let t_abc = combine(comb, &t_ab, &t_ac);
				let maj = combine(comb, &t_abc, &t_bc);
				let [ma, mb, mc, md] = actual(
					&format!("(maj {a0} {b0} {c0})"),
					&format!("(maj {a1} {b1} {c1})")
				);

				self.smt += &format!(
					"; Base-4 Maj propagation, round {i}\n\
					(assert (= {maja} {ma}))\n\
					(assert (= {majb} {mb}))\n\
					(assert (= {majc} {mc}))\n\
					(assert (= {majd} {md}))\n",
					maja = maj[0],
					majb = maj[1],
					majc = maj[2],
					majd = maj[3]
				);
			}
		}
	}

	fn assert_messages_not_same_base4(&mut self) {
		self.comment("Assert messages not the same (absolute and base-4 form)");

		let ones = self.b4_ones();
		let mut s = String::new();
		for i in 0..self.rounds.min(16) {
			s += &format!("\t(distinct m0_w{i} m1_w{i})\n");
			s += &format!("\t(distinct (bvor B4_w{i}_A B4_w{i}_D) {ones})\n");
		}

		if self.rounds == 1 {
			self.smt += &format!("(assert (and\n{s}))\n");
		} else if self.rounds > 1 {
			self.smt += &format!("(assert (or\n{s}))\n");
		}
	}

	fn assert_initial_vector_not_same_base4(&mut self) {
		self.comment("Assert starting vectors (CV) not the same (absolute and base-4 form)");

		let ones = self.b4_ones();
		let mut s = String::new();
		for var in 'a'..='h' {
			s += &format!("\t(distinct m0_{var}0 m1_{var}0)\n");
			s += &format!("\t(distinct (bvor B4_cv_{var}_A B4_cv_{var}_D) {ones})\n");
		}

		self.smt += &format!("(assert (or\n{s}))\n");
	}

	fn assert_hash_same_base4(&mut self) {
		self.comment("Assert output hash is the same (absolute and base-4 form)");

		let ones = self.b4_ones();
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut s = String::new();
		for i in 0..final_size {
			s += &format!("\t(= m0_hash{i} m1_hash{i})\n");
			s += &format!("\t(= (bvor B4_hash{i}_A B4_hash{i}_D) {ones})\n");
		}

		self.smt += format!("(assert (and\n{s}))\n").as_str();
	}
}

#[cfg(test)]
mod tests {
	use sha2_core::structs::hash_function::HashFunction;

	use super::*;
	use crate::smt_lib::smt_retriever::EncodingType;

	fn base4_builder(collision_type : CollisionType, rounds : u8) -> SmtBuilder {
		SmtBuilder {
			smt : String::new(),
			hash_function : HashFunction::SHA256,
			rounds,
			collision_type,
			encoding : EncodingType::Base4 {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			}
		}
	}

	#[test]
	fn ones_mask_matches_word_size() {
		let builder = base4_builder(CollisionType::Standard, 1);

		assert_eq!(builder.b4_ones(), format!("#b{}", "1".repeat(32)));
	}

	#[test]
	fn absolute_naming_uses_message_prefix() {
		let standard = base4_builder(CollisionType::Standard, 1);
		assert_eq!(standard.b4_abs(0, 'a', 0), "a0");
		assert_eq!(standard.b4_abs(1, 'a', 0), "a0");
		assert_eq!(standard.b4_abs(0, 'e', 3), "m0_e3");
		assert_eq!(standard.b4_abs(1, 'h', 3), "m1_h3");

		let free_start = base4_builder(CollisionType::FreeStart, 1);
		assert_eq!(free_start.b4_abs(0, 'a', 0), "m0_a0");
		assert_eq!(free_start.b4_abs(1, 'h', 0), "m1_h0");
	}

	#[test]
	fn pair_definition_shape() {
		let mut builder = base4_builder(CollisionType::Standard, 1);
		builder.define_base4_pair("w0", "m0_w0", "m1_w0");

		assert_eq!(
			builder.smt,
			"(define-fun B4_w0_A () Word (bvand (bvnot m0_w0) (bvnot m1_w0)))\n\
			(define-fun B4_w0_B () Word (bvand (bvnot m0_w0) m1_w0))\n\
			(define-fun B4_w0_C () Word (bvand m0_w0 (bvnot m1_w0)))\n\
			(define-fun B4_w0_D () Word (bvand m0_w0 m1_w0))\n"
		);
	}

	#[test]
	fn conditions_cover_cv_message_working_vars_and_hash() {
		let mut builder = base4_builder(CollisionType::Standard, 1);
		builder.define_base4_conditions();

		assert!(
			builder
				.smt
				.contains("; Base-4 condition masks for the chaining value"),
			"missing chaining-value section, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot a0) (bvnot a0)))"),
			"missing shared chaining-value pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_w0_D () Word (bvand m0_w0 m1_w0))"),
			"missing message pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_sa1_A () Word (bvand (bvnot m0_a1) (bvnot m1_a1)))"),
			"missing working-variable pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder.smt.contains(
				"(define-fun B4_hash0_A () Word (bvand (bvnot m0_hash0) (bvnot m1_hash0)))"
			),
			"missing final-hash pair, got:\n{}",
			builder.smt
		);
	}

	#[test]
	fn conditions_use_separate_cvs_for_free_start() {
		let mut builder = base4_builder(CollisionType::FreeStart, 1);
		builder.define_base4_conditions();

		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot m0_a0) (bvnot m1_a0)))"),
			"free-start chaining value must pair both CVs, got:\n{}",
			builder.smt
		);
	}

	#[test]
	fn conditions_skip_working_variables_for_zero_rounds() {
		let mut builder = base4_builder(CollisionType::Standard, 0);
		builder.define_base4_conditions();

		assert!(
			!builder.smt.contains("working variables"),
			"zero rounds must not emit working-variable masks, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_h_D () Word (bvand h0 h0))"),
			"chaining-value masks must still be emitted, got:\n{}",
			builder.smt
		);
	}

	fn generated(collision_type : CollisionType) -> String {
		let mut builder = base4_builder(collision_type, 1);
		Base4Encoding
			.generate(&mut builder)
			.expect("base4 generation must succeed without a solver");
		builder.smt
	}

	fn section_positions(smt : &str) -> Vec<usize> {
		[
			";; SETUP",
			";; TYPE",
			";; FUNCTIONS",
			";; CONSTANTS",
			";; MESSAGE EXPANSION",
			";; MESSAGE COMPRESSION",
			";; BASE-4 CONDITIONS",
			";; BASE-4 PROPAGATION LEMMAS",
			";; ASSERTIONS",
			";; GO!"
		]
		.iter()
		.map(|marker| {
			smt.find(marker)
				.expect("generated output missing a section")
		})
		.collect()
	}

	#[test]
	fn full_generation_contains_proven_function_definitions() {
		let smt = generated(CollisionType::Standard);

		assert!(
			smt.contains(
				"(define-fun b4band_d ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word\n\t(bvand Xd Yd))"
			),
			"missing verbatim b4band_d definition, got:\n{}",
			smt
		);
		assert!(
			smt.contains(
				"(define-fun b4bor_a ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word\n\t(bvand Xa Ya))"
			),
			"missing verbatim b4bor_a definition, got:\n{}",
			smt
		);
		assert!(
			smt.contains(
				"(define-fun b4bxor_a ((Xa Word) (Xb Word) (Xc Word) (Xd Word) (Ya Word) (Yb Word) (Yc Word) (Yd Word)) Word\n\t(bvor (bvand Xa Ya) (bvand Xb Yb) (bvand Xc Yc) (bvand Xd Yd)))"
			),
			"missing verbatim b4bxor_a definition, got:\n{}",
			smt
		);
	}

	#[test]
	fn full_generation_contains_cv_and_first_round_pairs() {
		let smt = generated(CollisionType::Standard);

		assert!(
			smt.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot a0) (bvnot a0)))"),
			"missing shared chaining-value pair, got:\n{}",
			smt
		);
		assert!(
			smt.contains("(define-fun B4_w0_A () Word (bvand (bvnot m0_w0) (bvnot m1_w0)))"),
			"missing first-round message pair, got:\n{}",
			smt
		);
	}

	#[test]
	fn standard_generation_asserts_messages_not_same_and_hash_same() {
		let smt = generated(CollisionType::Standard);
		let ones = format!("#b{}", "1".repeat(32));

		assert!(
			smt.contains("; Assert messages not the same (absolute and base-4 form)"),
			"missing messages-not-same assertion block, got:\n{}",
			smt
		);
		assert!(
			smt.contains("\t(distinct m0_w0 m1_w0)\n"),
			"missing absolute message-difference assertion, got:\n{}",
			smt
		);
		assert!(
			smt.contains(&format!("(distinct (bvor B4_w0_A B4_w0_D) {ones})")),
			"missing base-4 message-difference assertion, got:\n{}",
			smt
		);
		assert!(
			!smt.contains("; Assert starting vectors (CV) not the same"),
			"standard collision must not assert CV difference, got:\n{}",
			smt
		);

		assert!(
			smt.contains("; Assert output hash is the same (absolute and base-4 form)"),
			"missing hash-same assertion block, got:\n{}",
			smt
		);
		assert!(
			smt.contains("\t(= m0_hash0 m1_hash0)\n"),
			"missing absolute hash-equality assertion, got:\n{}",
			smt
		);
		assert!(
			smt.contains(&format!("(= (bvor B4_hash0_A B4_hash0_D) {ones})")),
			"missing base-4 hash-equality assertion, got:\n{}",
			smt
		);

		assert!(
			smt.contains("(check-sat)"),
			"missing check-sat, got:\n{}",
			smt
		);
		assert!(
			section_positions(&smt).is_sorted(),
			"sections out of order, got:\n{}",
			smt
		);
	}

	#[test]
	fn free_start_generation_asserts_cv_not_same_and_hash_same() {
		let smt = generated(CollisionType::FreeStart);
		let ones = format!("#b{}", "1".repeat(32));

		assert!(
			smt.contains("; Assert starting vectors (CV) not the same (absolute and base-4 form)"),
			"missing CV-not-same assertion block, got:\n{}",
			smt
		);
		assert!(
			smt.contains("\t(distinct m0_a0 m1_a0)\n"),
			"missing absolute CV-difference assertion, got:\n{}",
			smt
		);
		assert!(
			smt.contains(&format!("(distinct (bvor B4_cv_a_A B4_cv_a_D) {ones})")),
			"missing base-4 CV-difference assertion, got:\n{}",
			smt
		);
		assert!(
			!smt.contains("; Assert messages not the same"),
			"free-start collision must not assert message difference, got:\n{}",
			smt
		);

		assert!(
			smt.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot m0_a0) (bvnot m1_a0)))"),
			"free-start chaining value must pair both CVs in generated output, got:\n{}",
			smt
		);
		assert!(
			smt.contains("\t(= m0_hash0 m1_hash0)\n"),
			"missing absolute hash-equality assertion, got:\n{}",
			smt
		);

		assert!(
			smt.contains("(check-sat)"),
			"missing check-sat, got:\n{}",
			smt
		);
		assert!(
			section_positions(&smt).is_sorted(),
			"sections out of order, got:\n{}",
			smt
		);
	}
}
