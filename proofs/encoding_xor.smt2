(set-option :produce-models true)
(set-logic QF_BV)

(define-sort BV4 () (_ BitVec 4))


; Input variables
(declare-fun LEFT_X () BV4)
(declare-fun RIGHT_X () BV4)
(declare-fun LEFT_Y () BV4)
(declare-fun RIGHT_Y () BV4)


; Differential variables for X
(define-fun X_a () BV4 (bvand (bvnot LEFT_X) (bvnot RIGHT_X)))
(define-fun X_b () BV4 (bvand (bvnot LEFT_X) RIGHT_X))
(define-fun X_c () BV4 (bvand LEFT_X (bvnot RIGHT_X)))
(define-fun X_d () BV4 (bvand LEFT_X RIGHT_X))


; Differential variables for Y
(define-fun Y_a () BV4 (bvand (bvnot LEFT_Y) (bvnot RIGHT_Y)))
(define-fun Y_b () BV4 (bvand (bvnot LEFT_Y) RIGHT_Y))
(define-fun Y_c () BV4 (bvand LEFT_Y (bvnot RIGHT_Y)))
(define-fun Y_d () BV4 (bvand LEFT_Y RIGHT_Y))


; Theory Diff
(define-fun LEFT_XY () BV4 (bvxor LEFT_X LEFT_Y))
(define-fun RIGHT_XY () BV4 (bvxor RIGHT_X RIGHT_Y))


; Actual
(define-fun a_XY () BV4 (bvand (bvnot LEFT_XY) (bvnot RIGHT_XY)))
(define-fun b_XY () BV4 (bvand (bvnot LEFT_XY) RIGHT_XY))
(define-fun c_XY () BV4 (bvand LEFT_XY (bvnot RIGHT_XY)))
(define-fun d_XY () BV4 (bvand LEFT_XY RIGHT_XY))


; Logic
(define-fun a2 () BV4 
    (bvor (bvand X_a Y_a) 
          (bvand X_b Y_b) 
          (bvand X_c Y_c) 
          (bvand X_d Y_d)
    )
)

(define-fun b2 () BV4 
    (bvor (bvand X_a Y_b)
          (bvand X_b Y_a)
          (bvand X_c Y_d)
          (bvand X_d Y_c)
    )
)

(define-fun c2 () BV4 
    (bvor (bvand X_a Y_c)
          (bvand X_c Y_a)
          (bvand X_b Y_d)
          (bvand X_d Y_b)
    )
)

(define-fun d2 () BV4 
    (bvor (bvand X_a Y_d)
          (bvand X_d Y_a)
          (bvand X_b Y_c)
          (bvand X_c Y_b)
    )
)


; Assert mismatch
(assert (not (and 
    (= a2 a_XY)
    (= b2 b_XY)
    (= c2 c_XY)
    (= d2 d_XY)
)))

(check-sat)
