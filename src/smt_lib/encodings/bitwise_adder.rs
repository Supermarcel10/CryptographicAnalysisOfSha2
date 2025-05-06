use std::error::Error;
use crate::smt_lib::smt_lib::SmtBuilder;


fn bvadd(exprs: Vec<&str>) -> String {
	let mut s = String::from("(bvadd");
	for expr in exprs {
		s.push_str(&format!(" {expr}"))
	}
	s.push(')');
	s
}

fn bitwise_add(exprs: Vec<&str>) -> String {
	if exprs.len() > 6 {
		unimplemented!("Bitwise add only implemented up to 6 expressions.")
	}

	let mut s = String::from(format!("(bitadd-{} ", exprs.len()));

	for (i, expr) in exprs.iter().enumerate() {
		if i != 0 {
			s.push(' ');
		}
		s.push_str(expr);
	}
	s.push(')');
	s
}

impl SmtBuilder {
	pub(super) fn define_bitwise_add(&self) -> String {
		String::from("(define-fun bitadd-2 ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
		(let (
			(p0 (bvxor a b))
			(g0 (bvand a b))
		)
		(
			let (
				(g1 (bvor g0 (bvand p0 (bvshl g0 #x00000001))))
				(p1 (bvand p0 (bvshl p0 #x00000001)))
			)
			(
				let (
					(g2 (bvor g1 (bvand p1 (bvshl g1 #x00000002))))
					(p2 (bvand p1 (bvshl p1 #x00000002)))
				)
				(
					let (
						(g3 (bvor g2 (bvand p2 (bvshl g2 #x00000004))))
						(p3 (bvand p2 (bvshl p2 #x00000004)))
					)
					(
						let (
							(g4 (bvor g3 (bvand p3 (bvshl g3 #x00000008))))
							(p4 (bvand p3 (bvshl p3 #x00000008)))
						)
						(
							let (
								(g5 (bvor g4 (bvand p4 (bvshl g4 #x00000010))))
								(p5 (bvand p4 (bvshl p4 #x00000010)))
							)
							(
								let (
									(g6 (bvor g5 (bvand p5 (bvshl g5 #x00000020))))
									(p6 (bvand p5 (bvshl p5 #x00000020)))
								)
								(
									bvxor p0 (bvshl g6 #x00000001)
								)
							)
						)
					)
				)
			)
		))
	)

	; Adder Helpers using some Walace Tree reduction principles
	(define-fun bitadd-3 ((a (_ BitVec 32)) (b (_ BitVec 32)) (c (_ BitVec 32))) (_ BitVec 32)
		(let (
			(sum (bvxor a b c))
			(carry (bvshl (bvor (bvand a b) (bvand a c) (bvand b c)) #x00000001))
		)
		(
			bitadd-2 sum carry
		))
	)
	(define-fun bitadd-4 ((a (_ BitVec 32)) (b (_ BitVec 32)) (c (_ BitVec 32)) (d (_ BitVec 32))) (_ BitVec 32)
		(let (
			(sum (bvxor a b c))
			(carry (bvshl (bvor (bvand a b) (bvand a c) (bvand b c)) #x00000001))
		)
		(
			bitadd-3 sum carry d
		))
	)
	(define-fun bitadd-5 ((a (_ BitVec 32)) (b (_ BitVec 32)) (c (_ BitVec 32)) (d (_ BitVec 32)) (e (_ BitVec 32))) (_ BitVec 32)
		(let (
			(sum1 (bvxor a b c))
			(carry1 (bvshl (bvor (bvand a b) (bvand a c) (bvand b c)) #x00000001))
			(sum2 (bvxor d e))
			(carry2 (bvshl (bvand d e) #x00000001))
		)
		(
			bitadd-4 sum1 carry1 sum2 carry2
		))
	)
	(define-fun bitadd-6 ((a (_ BitVec 32)) (b (_ BitVec 32)) (c (_ BitVec 32)) (d (_ BitVec 32)) (e (_ BitVec 32)) (f (_ BitVec 32))) (_ BitVec 32)
		(let (
			(sum1 (bvxor a b c))
			(carry1 (bvshl (bvor (bvand a b) (bvand a c) (bvand b c)) #x00000001))
			(sum2 (bvxor d e f))
			(carry2 (bvshl (bvor (bvand d e) (bvand d f) (bvand e f)) #x00000001))
		)
		(
			bitadd-4 sum1 carry1 sum2 carry2
		))
	)")
	}

	pub(super) fn add(
		&self,
		exprs: Vec<&str>,
	) -> Result<String, Box<dyn Error>> {
		if exprs.len() < 2 {
			return Err(Box::from("Add requires at least 2 expressions!"));
		}

		if self.encoding.alternative_add() {
			Ok(bitwise_add(exprs))
		} else {
			Ok(bvadd(exprs))
		}
	}
}

