#lang rosette/safe

(require
  "../lib/core.rkt"
  "../lib/unittest.rkt"
)

(provide (all-defined-out))

(define
  (verify-refinement
    #:implstate impl-state
    #:impl impl-func
    #:specstate spec-state
    #:spec spec-func
    #:abs abs-function
    #:ri rep-invariant
    [args null]
    [ce-handler (lambda (sol) (void))])

  (define ri0 (rep-invariant impl-state))

  (define pre (check-asserts (equal? spec-state (abs-function impl-state))))

  (check-sat? (solve (assert ri0)) "rep-invariant satisfiable")
  (check-sat? (solve (assert pre)) "spec-state satisfiable")

  ; spec state transition
  (apply spec-func spec-state args)
  ; make sure spec-func doesn't generate assertions
  (check-equal? (asserts) null "spec no asserts")

  ; impl state transition
  (define impl-asserted
    (with-spectre-asserts-only (apply impl-func impl-state args)))
  (check-unsat? (verify (assert (=> ri0 (apply && impl-asserted)))) "impl no-assert")

  (define-values (ri1 ri1-asserted)
    (with-asserts (rep-invariant impl-state)))
  (check-unsat? (verify (assert (=> ri0 (apply && ri1-asserted)))) "rep-invariant no-assert")

  (define-values (post post-asserted)
    (with-asserts (equal? spec-state (abs-function impl-state))))

  (check-unsat? (verify (assert (=> ri0 (apply && post-asserted)))) "impl no asserts")

  (let ([sol (verify (assert (=> (&& pre ri0) post)))])
    (when (sat? sol) (ce-handler sol))
    (check-unsat? sol))

  (check-unsat? (verify (assert (=> (&& pre ri0) ri1))) "rep-invariant after")

(void))
