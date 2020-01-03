#lang rosette

; import serval functions with prefix "core:"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))

  ; import Arm AArch64
  "base.rkt" "interp.rkt" "asm.rkt"
)

(provide (all-defined-out))

#|
  Sign implementation
|#

; The following absolutely does not implement sign - used for early bringup
(define sign-implementation0 (asm-block 0 (vector
  (ret 30)
)))

#|
Version #1: idiomatic AArch64 code that avoids branches
    cmp     X0, #0 ; NZCV <- cmp(X0, 0)
    cset.le X0     ; X0 <- if cond_le(NZCV) then 0 else 1 ; cset is an alias of cinc
    cinv.ge X0     ; X0 <- if cond_ge(NZCV) then X0 else NOT(X0)
    movz    X1, #0 ; X1 <- 0   ; clear (unused) scratch register to match RISC-V version
    ret     X30    ; return    ; X30 is the default if omitted
|#

(define sign-implementation1 (asm-block 0 (vector
  (cmp-immediate 1 00 0 0)
  (cset          1 00 cond-le)
  (csinv         1 00 00 cond-ge)
  (movz          1 01 0 0)
  (ret           30)
)))

#|
Version #2: variant on version #1 that gratuitiously saves/restores X0 from stack
    str     X0, [SP, #-8]! ; SP -= 8; [SP] <- X0;
    ldr     X0, [SP], #8   ; X0 <- [SP]; SP += 8;
    cmp     X0, #0         ; NZCV <- cmp(X0, 0)
    cset.le X0             ; X0 <- if cond_le(NZCV) then 0 else 1 ; cset is an alias of cinc
    cinv.ge X0             ; X0 <- if cond_ge(NZCV) then X0 else NOT(X0)
    movz    X1, #0         ; X1 <- 0   ; clear (unused) scratch register to match RISC-V version
    ret     X30            ; return    ; X30 is the default if omitted
|#

(define sign-implementation2 (asm-block 0 (vector
  (str-imm-pre   00 31 -8 3)
  (ldr-imm-post  00 31 8 3 #f)
  (cmp-immediate 1 00 0 0)
  (cset          1 00 cond-le)
  (csinv         1 00 00 cond-ge)
  (movz          1 01 0 0)
  (ret           30)
)))


#|
Version #3: AArch64 code that mirrors some of the branching structure of RISC-V original
0: cmp     X0, #0 ; NZCV <- cmp(X0, 0)
1: cset.le X0     ; X0 <- if cond_le(NZCV) then 0 else 1 ; cset is an alias of cinc
2: blt     3      ; branch to 3 if cond_le(NZCV)
3: ret     X30    ; return to address in link register (X30)
4: movn    X0, #0 ; X0 <- NOT(0)
5: ret     X30    ; return to address in link register (X30)
|#

; todo: add asm for version 3

#|
  Sign specification
|#

; Note that we mark the struct as mutable and transparent
; for better debugging and interoperability with Serval libraries
(struct state (a0 a1) #:mutable #:transparent) ; specification state

; functional specification for the sign code
(define (spec-sign s)
  (define a0 (state-a0 s))
  (define sign (cond
    [(bvsgt a0 (bv 0 64))  (bv  1 64)]
    [(bvslt a0 (bv 0 64))  (bv -1 64)]
    [else                  (bv  0 64)]))
  ; the following line is what the RISC-V version contained - looks like an
  ; implementation detail, not a specification requirement to me
  ; (define scratch (if (negative? a0) 1 0)) ; why is this needed in the specification and why define it this way?
  (define scratch (bv 0 64))
  (state sign scratch))

; abstraction function: impl. cpu state to spec. state
(define (AF cpu)
  (state (cpu-X cpu 64 0) (cpu-X cpu 64 1)))

; Mutable version of sign specification
(define (spec-sign-update s)
  (let ([s2 (spec-sign s)])
    (set-state-a0! s (state-a0 s2))
    (set-state-a1! s (state-a1 s2))))


#| Running interpreter on concrete state and check result |#

(define (check-run program x)
  ; todo: should initial state require that LR (X30) contains a legal return address or that SP makes sense?
  (define cstate (init-cpu-concrete test:symbols test:globals))
  (set-cpu-X! cstate 64 0 (bv x 64)) ; test input value for X0
  (define astate0 (AF cstate))
  ; (printf "Concrete state before ~a\n" cstate)
  ; (printf "Abstract state before ~a\n" astate0)
  (interpret cstate program)
  (define astate1 (AF cstate))
  ; (printf "Concrete state after ~a\n" cstate)
  ; (printf "Result ~a\n" (cpu-X cstate 64 0))
  ; (printf "Abstract state after ~a\n" astate1)
  ; (printf "Expected abstract state after ~a\n" (spec-sign astate0))
  (check-equal? astate1 (spec-sign astate0))
  )


#| Memory map |#

; Note: the following hardwired memory map does not work - any stack
; accesses are likely to fail.
; Also, we somehow have to insert the code contents into the memory map
; as a big table of constants.
(define test:symbols
  (list
    ; an entry for each block of memory
    (list #x0000 #x1000 'R "code")
    (list #x1000 #x2000 'B "stack")
    ))

(define test:globals (hash
  ; treat the stack as an array of 8-byte aligned objects
  "stack" (lambda () (core:marray 512 (core:mcell 8)))
  ))


#| State-machine refinement |#

; Fresh implementation state
(define mstate-init (init-cpu-symbolic test:symbols test:globals))
(define mstate (cpu-copy mstate-init))


; Fresh specification state
(define-symbolic a0 a1 (bitvector 64))
(define s (state a0 a1))

; Counterexample handler for debugging
(define (handle-counterexample sol)
  (printf "Verification failed:\n")
  (printf "Initial implementation state: ~a\n" (evaluate mstate-init sol))
  (printf "Initial specification state: ~a\n" (evaluate (state a0 a1) sol))
  (printf "Final implementation state ~a\n" (evaluate mstate sol))
  (printf "Final specification state ~a\n" (evaluate s sol)))

; Verify refinement
(define (verify-refinement program)
  (core:verify-refinement
  #:implstate mstate
  #:impl (lambda (cpu) (interpret cpu program))
  #:specstate s
  #:spec spec-sign-update
  #:abs AF
  #:ri (const #t)
  null
  handle-counterexample))

#| Safety property |#

(define (~ s1 s2)
  (equal? (state-a0 s1) (state-a0 s2))) ; filter out a1

; note that the safety property is checked on the specification, not on the implementation
(define (verify-safety)
  (core:check-step-consistency
    #:state-init (λ () (define-symbolic* X Y (bitvector 64)) (state X Y))
    #:state-copy (λ (s) (struct-copy state s))
    #:unwinding ~
    spec-sign-update))

; run a single return instruction
(interpret (init-cpu-concrete test:symbols test:globals) sign-implementation0)

; test sign on three concrete test values
(check-run sign-implementation1 3)
(check-run sign-implementation1 0)
(check-run sign-implementation1 -3)

; test memory-based sign implementation on one concrete test value
(check-run sign-implementation2 -3)

; invoke test directly so that I get a useful stackdump when things fail
; (printf "Started checking refinement\n")
; (verify-refinement sign-implementation1)
; (printf "Finished checking refinement\n")
;
; (printf "Started checking safety\n")
; (verify-safety)
; (printf "Finished checking safety\n")

; the following line makes my laptop fan run - what does test-case+ do?
;  (test-case+ "ToyArm Refinement" (verify-refinement sign-implementation1))

(define (rt) (run-tests (test-suite+ "ToyArm tests"
  (test-case+ "ToyArm Interpreter -3" (check-run sign-implementation1 -3))
  (test-case+ "ToyArm Interpreter  0" (check-run sign-implementation1 0))
  (test-case+ "ToyArm Interpreter  3" (check-run sign-implementation1 3))
  (test-case+ "ToyArm Refinement" (verify-refinement sign-implementation1))
  (test-case+ "ToyArm Safety" (verify-safety))
  )))

(rt)

; end
