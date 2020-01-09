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
  (hash-set! implementation:globals "code" (lambda () (core:marray 16384 (core:mcell 4))))
  (define symbols (list*
                    (list #x000000 #x010000 'B "stack")
                    (list #x400000 #x410000 'B "code")
                    implementation:symbols))
  ; (define symbols implementation:symbols)

  (define cstate (init-cpu-concrete symbols implementation:globals implementation:binary))
  ; copy binary into memory
  (for ([(addr data) implementation:binary])
            ; (printf "~x -> ~x\n" addr data)
            (mem-write! cstate 4 (bv addr 64) (bv 0 64) (bv data 32)))
  (set-cpu-pc! cstate (bv pc 64))
  (set-cpu-sp! cstate (bv #x10000 64))

  (printf "Concrete state before ~a\n" cstate)
  (interpret cstate implementation:binary)
  (printf "Concrete state after ~a\n" cstate)
  )

; run a test function
(check-run implementation:entry)

; end
