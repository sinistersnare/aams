#lang racket

; a [k=0]-CFA based on the tiny-scheme-cek.rkt
; a CFA is an abstract interpretation, so we take the semantics of
; the tiny-scheme-cek, and we lift it up to the abstract
; this way we can guarantee termination (??? CAN WE? or just decidability?)

