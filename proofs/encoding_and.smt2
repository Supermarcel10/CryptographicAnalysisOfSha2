(set-option :produce-models true)
(set-logic QF_BV)

(define-sort BV4 () (_ BitVec 4))


; Input Variables
(declare-fun LEFT_X () BV4)
(declare-fun RIGHT_X () BV4)
(declare-fun LEFT_Y () BV4)
(declare-fun RIGHT_Y () BV4)


; Differential variables for X
(define-fun X_a () BV4 (bvand (bvnot LEFT_X) (bvnot RIGHT_X)))
(define-fun X_b () BV4 (bvand (bvnot LEFT_X) RIGHT_X))
(define-fun X_c () BV4 (bvand LEFT_X (bvnot RIGHT_X)))
(define-fun X_d () BV4 (bvand LEFT_X RIGHT_X))
(define-fun X_f () BV4 (bvor X_b X_d))  ; f = b OR d
(define-fun X_g () BV4 (bvor X_c X_d))  ; g = c OR d


; Differential variables for Y
(define-fun Y_a () BV4 (bvand (bvnot LEFT_Y) (bvnot RIGHT_Y)))
(define-fun Y_b () BV4 (bvand (bvnot LEFT_Y) RIGHT_Y))
(define-fun Y_c () BV4 (bvand LEFT_Y (bvnot RIGHT_Y)))
(define-fun Y_d () BV4 (bvand LEFT_Y RIGHT_Y))
(define-fun Y_f () BV4 (bvor Y_b Y_d))  ; f = b OR d
(define-fun Y_g () BV4 (bvor Y_c Y_d))  ; g = c OR d


; Theory Diff
(define-fun LEFT_XY () BV4 (bvand LEFT_X LEFT_Y))
(define-fun RIGHT_XY () BV4 (bvand RIGHT_X RIGHT_Y))


; Actual
(define-fun a_XY () BV4 (bvand (bvnot LEFT_XY) (bvnot RIGHT_XY)))
(define-fun b_XY () BV4 (bvand (bvnot LEFT_XY) RIGHT_XY))
(define-fun c_XY () BV4 (bvand LEFT_XY (bvnot RIGHT_XY)))
(define-fun d_XY () BV4 (bvand LEFT_XY RIGHT_XY))


; Logic
(define-fun d2 () BV4 (bvand X_d Y_d))
(define-fun b2 () BV4 (bvand (bvand X_f Y_f) (bvnot d2)))
(define-fun c2 () BV4 (bvand (bvand X_g Y_g) (bvnot d2)))
(define-fun a2 () BV4 (bvnot (bvor d2 (bvor c2 b2))))


; Assert mismatch
(assert (not (and 
    (= a2 a_XY)
    (= b2 b_XY)
    (= c2 c_XY)
    (= d2 d_XY)
)))


(check-sat)
