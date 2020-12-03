(((call/cc (λ (x) (call/cc x))) (λ (x) x)) 2)
; expect 2 as output
