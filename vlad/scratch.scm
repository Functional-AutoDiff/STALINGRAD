(+ 1 2) ===> 3
(- 1 2) ===> -1
; (- 1)
(* 1 2) ===> 2
(/ 1 2) ===> 0.5
(sqrt 2) ===> 1.414213562373095
(exp 1) ===> 2.718281828459045
(= 1 1)
(< 1 2)
(zero? 4) ===> #f
(zero? 0)
(positive? -1) ===> #f
(positive? 1)
(negative? 2) ===> #f
(negative? -1)
(sin 3) ===> .1411200080598672
(cos 3) ===> -.9899924966004454
(log 2) ===> .6931471805599453
(atan 2 3) ===> .5880026035475675
(real? 4)
(real? 2.073e-2)


;(define (abs x) (if (negative? x) (- 0 x) x))
;(abs -3)

;(let ((ignore (write (* 2 (real 3)))))
;  3)


;; (define (fact x)
;;   (if (= x 0)
;;       1
;;       (* x (fact (- x 1)))))

;; (fact 5)
;; (fact (real 5))

(perturb 1) ===> (perturbation 1)
;(write (perturb 1))
(perturbation? (perturb 1))
(perturbation? 1) ===> #f
(bundle 1 (perturb 1)) ===> (forward 1 (perturbation 1))
(forward? (bundle 1 (perturb 1)))
(forward? 1) ===> #f
(forward? (perturb 1)) ===> #f
(unperturb (perturb 1)) ===> 1
(primal (bundle 1 (perturb 1))) ===> 1
(tangent (bundle 1 (perturb 1))) ===> (perturbation 1)
(perturb (cons 1 2)) ===> (perturbation (1 . 2))
(perturb #t) ===> (perturbation #t)
(bundle (cons 1 2) (perturb (cons 3 4))) ===> (forward (1 . 2) (perturbation (3 . 4)))
(*j 1) ===> (reverse 1)

;((*j sin) (*j 1))
;(define (car (cons x y)) x)
;(define (cdr (cons x y)) y)
;(reverse? (car ((*j sin) (*j 1))))
;(procedure? (cdr ((*j sin) (*j 1))))
;((cdr ((*j sin) (*j 1))) (sensitize 1))
(reverse? (*j sin))
(plus (cons 1 2) (cons 2 3)) ===> (3 . 5)

;; (define (double-loop)
;;   (let* ((x (read-real))
;;          (y (write (* 3 x))))
;;     (double-loop)))

;; (double-loop)

