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

  (prefix-in implementation:
    (combine-in
      "test.binary.rkt"
      "test.globals.rkt"
      "test.map.rkt")))

(provide (all-defined-out))


#| Running interpreter on concrete state and check result |#

(define (check-run pc)

  ; allocate the stack
  ; (hash-set! implementation:globals "stack" (lambda () (core:mcell 65536)))
  ; (hash-set! implementation:globals "stack" (lambda () (core:marray 65536 (core:mcell 1))))
  (hash-set! implementation:globals "stack" (lambda () (core:marray 8192 (core:mcell 8))))
  (define symbols (list* (list #x00000 #x10000 'B "stack") implementation:symbols))
  ; (define symbols implementation:symbols)

  (define cstate (init-cpu-concrete symbols implementation:globals implementation:binary))
  (set-cpu-pc! cstate (bv pc 64))
  (set-cpu-sp! cstate (bv #x10000 64))

  (printf "Concrete state before ~a\n" cstate)
  (interpret cstate implementation:binary)
  (printf "Concrete state after ~a\n" cstate)
  )

; run a test function
(check-run implementation:entry)

; end
