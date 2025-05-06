(set-logic QF_BV)

; Full Adder
(define-fun bitadd-2 ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
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
)

; Input Variables
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(declare-const e (_ BitVec 32))
(declare-const f (_ BitVec 32))

; Assert mismatch
(assert (or
	(distinct (bitadd-2 a b) (bvadd a b))
	(distinct (bitadd-3 a b c) (bvadd a b c))
	(distinct (bitadd-4 a b c d) (bvadd a b c d))
	(distinct (bitadd-5 a b c d e) (bvadd a b c d e))
	(distinct (bitadd-6 a b c d e f) (bvadd a b c d e f))
))


(check-sat)
