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
; K constants irrelevant for 0 rounds

; Define H constants (IV/CV)
(declare-fun a0 () Word)
(declare-fun b0 () Word)
(declare-fun c0 () Word)
(declare-fun d0 () Word)
(declare-fun e0 () Word)
(declare-fun f0 () Word)
(declare-fun g0 () Word)
(declare-fun h0 () Word)


;; MESSAGE EXPANSION
; MESSAGE 0
; Initial state
; Message expansion irrelevant for 0 rounds

; MESSAGE 1
; Initial state
; Message expansion irrelevant for 0 rounds


;; MESSAGE COMPRESSION
; MESSAGE 0

; MESSAGE 1

; Final state update
(define-fun m0_hash0 () Word (bvadd a0 a0))
(define-fun m1_hash0 () Word (bvadd a0 a0))
(define-fun m0_hash1 () Word (bvadd b0 b0))
(define-fun m1_hash1 () Word (bvadd b0 b0))
(define-fun m0_hash2 () Word (bvadd c0 c0))
(define-fun m1_hash2 () Word (bvadd c0 c0))
(define-fun m0_hash3 () Word (bvadd d0 d0))
(define-fun m1_hash3 () Word (bvadd d0 d0))
(define-fun m0_hash4 () Word (bvadd e0 e0))
(define-fun m1_hash4 () Word (bvadd e0 e0))
(define-fun m0_hash5 () Word (bvadd f0 f0))
(define-fun m1_hash5 () Word (bvadd f0 f0))
(define-fun m0_hash6 () Word (bvadd g0 g0))
(define-fun m1_hash6 () Word (bvadd g0 g0))


;; ASSERTIONS
; Assert messages not the same

; Assert output hash is the same
(assert (and
	(= m0_hash0 m1_hash0)
	(= m0_hash1 m1_hash1)
	(= m0_hash2 m1_hash2)
	(= m0_hash3 m1_hash3)
	(= m0_hash4 m1_hash4)
	(= m0_hash5 m1_hash5)
	(= m0_hash6 m1_hash6)
))


;; GO!
(check-sat)


;; GET OUTPUT
; H Constants (IV/CV)
(get-value (a0 b0 c0 d0 e0 f0 g0 h0))

; Output hash
(get-value (m0_hash0 m0_hash1 m0_hash2 m0_hash3 m0_hash4 m0_hash5 m0_hash6))
