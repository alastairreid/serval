#lang rosette

; import serval functions with prefix "core:"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))

  (prefix-in rosette:
    rosette/base/core/bitvector)

  ; import Arm AArch64
  "base.rkt"
)

(provide (all-defined-out))

; privileged execution support

(define (aarch64-check-system-access cpu op0 op1 CRn CRm op2 rd L)
  ; todo
  #f
  )

(define (aarch64-sys-reg-read cpu sys_op0 sys_op1 sys_crn sys_crm sys_op2)
  ; todo
  #f
  )

(define (aarch64-sys-reg-write cpu sys_op0 sys_op1 sys_crn sys_crm sys_op2 val)
  ; todo
  #f
  )

(define (aarch64-check-for-svc-trap cpu imm16)
  ; todo
  #f
  )

(define (aarch64-check-for-smc-undef-or-trap cpu imm16)
  ; todo
  #f
  )

(define (aarch64-take-exception cpu level exception return vect-offset)
  (core:bug-on #t "todo"))

(define (aarch64-call-supervisor cpu imm16)
  ; todo: ss-advance
  ; todo: check HRC_EL2.TGE
  (define route-to-el2 #f)
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'supervisor-call) ; todo: immediate
  (define level
    (cond
      [(bvsgt (cpu-pstate-el cpu) (bv 1 2)) (cpu-pstate-el cpu)]
      [route-to-el2 (bv 2 2)]
      [else (bv 1 2)]))
  (aarch64-take-exception level exception return vect-offset))

(define (aarch64-call-hypervisor cpu imm16)
  ; todo: ss-advance
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'hypervisor-call) ; todo: immediate
  (define level (if (equal? (cpu-pstate-el cpu) (bv 3 2)) (bv 3 2) (bv 2 2)))
  (aarch64-take-exception level exception return vect-offset))

(define (aarch64-call-secure-monitor cpu imm16)
  ; todo: ss-advance
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'monitor-call) ; todo: immediate
  (define level (bv 3 2))
  (aarch64-take-exception level exception return vect-offset))

