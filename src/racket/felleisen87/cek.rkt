#lang racket

; implementation of CEK machine from Felleisen 87:
; "Control Operators, the SECD Machine, and the λ-calculus"
; This implements the Control/Abort semantics.

(struct state (ctrl env kont) #:transparent)

(define (step st)
  (match st
    [(state (? symbol? x) ρ κ) ;; 1
     (state '‡ '() `(ret ,κ ,(hash-ref ρ x)))]
    [(state `(λ ,x ,M) ρ κ) ;; 2
     (state '‡ '() `(ret ,κ (clo (λ ,x ,M) ,ρ)))]
    [(state `(C ,M) ρ κ) ;; 6
     (state M ρ `(cont ,κ))]
    [(state `(A ,M) ρ κ) ;; 10
     (state M ρ '(stop))]
    [(state `(,M ,N) ρ κ) ;; 3
     (state M ρ `(arg ,κ ,N ,ρ))]
    [(state '‡ _ `(ret (arg ,κ ,N ,ρ) ,F)) ;; 4
     (state (N ρ `(fun ,κ ,F)))]
    [(state '‡ _ `(ret (fun ,κ (clo (λ ,x ,M) ,ρ)) ,V)) ;; 5
     (state M (hash-set ρ x V) κ)]
    [(state '‡ _ `(ret (cont ,κ) (clo (λ ,x ,M) ,ρ))) ;; 7
     (state M (hash-set ρ x `(κpt p κ)) '(stop))]
    [(state '‡ _ `(ret (cont ,κ) (κpt ,p ,κ0))) ;; 8
     (state '‡ '() `(ret ,κ0 (κpt ,p ,κ)))]
    [(state '‡ _ `(ret (fun ,κ (κpt ,p ,κ0)) ,V)) ;; 9
     (state '‡ '() `(ret ,κ0 ,V))]
    [(state _ _ '(stop)) st]))
