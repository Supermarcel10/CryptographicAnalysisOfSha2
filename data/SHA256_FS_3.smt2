;; SETUP
(set-option :produce-models true)
(set-logic QF_BV)


;; TYPE
(define-sort Word () (_ BitVec 32))


;; FUNCTIONS
(define-fun ch ((e Word) (f Word) (g Word)) Word
	(bvxor (bvand e f) (bvand (bvnot e) g))
)
(define-fun maj ((a Word) (b Word) (c Word)) Word
	(bvxor (bvand a b) (bvand a c) (bvand b c))
)
(define-fun sigma0 ((a Word)) Word
	(bvxor ((_ rotate_right 2) a) ((_ rotate_right 13) a) ((_ rotate_right 22) a))
)
(define-fun sigma1 ((e Word)) Word
	(bvxor ((_ rotate_right 6) e) ((_ rotate_right 11) e) ((_ rotate_right 25) e))
)
(define-fun gamma0 ((x Word)) Word
	(bvxor ((_ rotate_right 7) x) ((_ rotate_right 18) x) (bvlshr x (_ bv3 32)))
)
(define-fun gamma1 ((x Word)) Word
	(bvxor ((_ rotate_right 17) x) ((_ rotate_right 19) x) (bvlshr x (_ bv10 32)))
)
(define-fun t1 ((h Word) (e Word) (f Word) (g Word) (k Word) (w Word)) Word
	(bvadd h (sigma1 e) (ch e f g) k w)
)
(define-fun t2 ((a Word) (b Word) (c Word)) Word
	(bvadd (sigma0 a) (maj a b c))
)
(define-fun expandMessage ((a Word) (b Word) (c Word) (d Word)) Word
	(bvadd a (gamma0 b) c (gamma1 d))
)

;; CONSTANTS
; Define K constants
(define-fun k0 () Word #x428a2f98)
(define-fun k1 () Word #x71374491)
(define-fun k2 () Word #xb5c0fbcf)

; Define H constants (IV/CV)
(declare-fun m0_a0 () Word)
(declare-fun m1_a0 () Word)
(declare-fun m0_b0 () Word)
(declare-fun m1_b0 () Word)
(declare-fun m0_c0 () Word)
(declare-fun m1_c0 () Word)
(declare-fun m0_d0 () Word)
(declare-fun m1_d0 () Word)
(declare-fun m0_e0 () Word)
(declare-fun m1_e0 () Word)
(declare-fun m0_f0 () Word)
(declare-fun m1_f0 () Word)
(declare-fun m0_g0 () Word)
(declare-fun m1_g0 () Word)
(declare-fun m0_h0 () Word)
(declare-fun m1_h0 () Word)


;; MESSAGE EXPANSION
; MESSAGE 0
; Initial state
(declare-fun m0_w0 () Word)
(declare-fun m0_w1 () Word)
(declare-fun m0_w2 () Word)
; Message expansion irrelevant for 3 rounds

; MESSAGE 1
; Initial state
(declare-fun m1_w0 () Word)
(declare-fun m1_w1 () Word)
(declare-fun m1_w2 () Word)
; Message expansion irrelevant for 3 rounds


;; MESSAGE COMPRESSION
; MESSAGE 0
(define-fun m0_t1_1 () Word (t1 m0_h0 m0_e0 m0_f0 m0_g0 k0 m0_w0))
(define-fun m0_t2_1 () Word (t2 m0_a0 m0_b0 m0_c0))
(define-fun m0_a1 () Word (bvadd m0_t1_1 m0_t2_1))
(define-fun m0_b1 () Word m0_a0)
(define-fun m0_c1 () Word m0_b0)
(define-fun m0_d1 () Word m0_c0)
(define-fun m0_e1 () Word (bvadd m0_d0 m0_t1_1))
(define-fun m0_f1 () Word m0_e0)
(define-fun m0_g1 () Word m0_f0)
(define-fun m0_h1 () Word m0_g0)
(define-fun m0_t1_2 () Word (t1 m0_h1 m0_e1 m0_f1 m0_g1 k1 m0_w1))
(define-fun m0_t2_2 () Word (t2 m0_a1 m0_b1 m0_c1))
(define-fun m0_a2 () Word (bvadd m0_t1_2 m0_t2_2))
(define-fun m0_b2 () Word m0_a1)
(define-fun m0_c2 () Word m0_b1)
(define-fun m0_d2 () Word m0_c1)
(define-fun m0_e2 () Word (bvadd m0_d1 m0_t1_2))
(define-fun m0_f2 () Word m0_e1)
(define-fun m0_g2 () Word m0_f1)
(define-fun m0_h2 () Word m0_g1)
(define-fun m0_t1_3 () Word (t1 m0_h2 m0_e2 m0_f2 m0_g2 k2 m0_w2))
(define-fun m0_t2_3 () Word (t2 m0_a2 m0_b2 m0_c2))
(define-fun m0_a3 () Word (bvadd m0_t1_3 m0_t2_3))
(define-fun m0_b3 () Word m0_a2)
(define-fun m0_c3 () Word m0_b2)
(define-fun m0_d3 () Word m0_c2)
(define-fun m0_e3 () Word (bvadd m0_d2 m0_t1_3))
(define-fun m0_f3 () Word m0_e2)
(define-fun m0_g3 () Word m0_f2)
(define-fun m0_h3 () Word m0_g2)

; MESSAGE 1
(define-fun m1_t1_1 () Word (t1 m1_h0 m1_e0 m1_f0 m1_g0 k0 m1_w0))
(define-fun m1_t2_1 () Word (t2 m1_a0 m1_b0 m1_c0))
(define-fun m1_a1 () Word (bvadd m1_t1_1 m1_t2_1))
(define-fun m1_b1 () Word m1_a0)
(define-fun m1_c1 () Word m1_b0)
(define-fun m1_d1 () Word m1_c0)
(define-fun m1_e1 () Word (bvadd m1_d0 m1_t1_1))
(define-fun m1_f1 () Word m1_e0)
(define-fun m1_g1 () Word m1_f0)
(define-fun m1_h1 () Word m1_g0)
(define-fun m1_t1_2 () Word (t1 m1_h1 m1_e1 m1_f1 m1_g1 k1 m1_w1))
(define-fun m1_t2_2 () Word (t2 m1_a1 m1_b1 m1_c1))
(define-fun m1_a2 () Word (bvadd m1_t1_2 m1_t2_2))
(define-fun m1_b2 () Word m1_a1)
(define-fun m1_c2 () Word m1_b1)
(define-fun m1_d2 () Word m1_c1)
(define-fun m1_e2 () Word (bvadd m1_d1 m1_t1_2))
(define-fun m1_f2 () Word m1_e1)
(define-fun m1_g2 () Word m1_f1)
(define-fun m1_h2 () Word m1_g1)
(define-fun m1_t1_3 () Word (t1 m1_h2 m1_e2 m1_f2 m1_g2 k2 m1_w2))
(define-fun m1_t2_3 () Word (t2 m1_a2 m1_b2 m1_c2))
(define-fun m1_a3 () Word (bvadd m1_t1_3 m1_t2_3))
(define-fun m1_b3 () Word m1_a2)
(define-fun m1_c3 () Word m1_b2)
(define-fun m1_d3 () Word m1_c2)
(define-fun m1_e3 () Word (bvadd m1_d2 m1_t1_3))
(define-fun m1_f3 () Word m1_e2)
(define-fun m1_g3 () Word m1_f2)
(define-fun m1_h3 () Word m1_g2)

; Final state update
(define-fun m0_hash0 () Word (bvadd m0_a0 m0_a3))
(define-fun m1_hash0 () Word (bvadd m1_a0 m1_a3))
(define-fun m0_hash1 () Word (bvadd m0_b0 m0_b3))
(define-fun m1_hash1 () Word (bvadd m1_b0 m1_b3))
(define-fun m0_hash2 () Word (bvadd m0_c0 m0_c3))
(define-fun m1_hash2 () Word (bvadd m1_c0 m1_c3))
(define-fun m0_hash3 () Word (bvadd m0_d0 m0_d3))
(define-fun m1_hash3 () Word (bvadd m1_d0 m1_d3))
(define-fun m0_hash4 () Word (bvadd m0_e0 m0_e3))
(define-fun m1_hash4 () Word (bvadd m1_e0 m1_e3))
(define-fun m0_hash5 () Word (bvadd m0_f0 m0_f3))
(define-fun m1_hash5 () Word (bvadd m1_f0 m1_f3))
(define-fun m0_hash6 () Word (bvadd m0_g0 m0_g3))
(define-fun m1_hash6 () Word (bvadd m1_g0 m1_g3))
(define-fun m0_hash7 () Word (bvadd m0_h0 m0_h3))
(define-fun m1_hash7 () Word (bvadd m1_h0 m1_h3))


;; ASSERTIONS
; Assert starting vectors (CV) not the same
(assert (or
	(distinct m0_a0 m1_a0)
	(distinct m0_b0 m1_b0)
	(distinct m0_c0 m1_c0)
	(distinct m0_d0 m1_d0)
	(distinct m0_e0 m1_e0)
	(distinct m0_f0 m1_f0)
	(distinct m0_g0 m1_g0)
	(distinct m0_h0 m1_h0)
))

; Assert output hash is the same
(assert (and
	(= m0_hash0 m1_hash0)
	(= m0_hash1 m1_hash1)
	(= m0_hash2 m1_hash2)
	(= m0_hash3 m1_hash3)
	(= m0_hash4 m1_hash4)
	(= m0_hash5 m1_hash5)
	(= m0_hash6 m1_hash6)
	(= m0_hash7 m1_hash7)
))


;; GO!
(check-sat)


;; GET OUTPUT
; H Constants (IV/CV)
(get-value (m0_a0 m1_a0 m0_b0 m1_b0 m0_c0 m1_c0 m0_d0 m1_d0 m0_e0 m1_e0 m0_f0 m1_f0 m0_g0 m1_g0 m0_h0 m1_h0))

; Output hash
(get-value (m0_hash0 m0_hash1 m0_hash2 m0_hash3 m0_hash4 m0_hash5 m0_hash6 m0_hash7))

; Output round A/E/W state changes
(get-value (m0_a0 m1_a0 m0_e0 m1_e0 m0_w0 m1_w0 m0_a1 m1_a1 m0_e1 m1_e1 m0_w1 m1_w1 m0_a2 m1_a2 m0_e2 m1_e2 m0_w2 m1_w2))
