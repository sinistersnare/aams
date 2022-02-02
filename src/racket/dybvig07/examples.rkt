#lang racket

(require racket/control)


;;;;; Examples showing how the prompt can be taken from the stack
;;;;; and what that may cause.
;;;;; This example is most prevalent in -F-, as there is a net
;;;;; loss of 1 prompt on the stack after -F- is used.
;;;;; This means that -F- is not purely functional!
;;;;; The other operators work in this example because they re-add the prompt at some point.
;;;;; (that is, -F+ does it after calling the k, the others never take it away in the first place)

; -F- does not work in this case, beacuse cupto/spawn/withSubCont
; removes the prompt when working, and it is never restored.
#;
((λ (p) (set p (+ (cupto p k (k 3))
                  (cupto p k (k 4)))))
 (new-prompt))

; this example uses -F+ (spawn from Hieb & Dybvig 90)
; we can use the prompt again here as it is replaced when
; the first continuation is reinstated.
#;
(spawn (λ (p) (+ (p (λ (k) (k 3)))
                 (p (λ (k) (k 4))))))

; not sure this does what we want really? Considering
; that `p` pushes the prompt, so its being pushed twice?
; but the example utilizing -F+ directly (not runnable in racket)
; has the same output (when tested in cekm.rkt)

;;;;
; Have the prompt escape so -F+ wont work if its not reinstated.
;;;;
#;
(spawn (λ (p) (+ (p (λ (k) 3))
                 (p (λ (k) (k 4))))))


; this doesnt work because the first -F+ fully aborts the continuation,
; which includes the second -F+ call, so its never used.
#;
((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) 3))
                         (-F+ p (λ (k) (k 3))))))
 (newPrompt))

#;
(+ 1 ((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) 3))
                         (-F+ p (λ (k) (k 3))))))
 (newPrompt)))

; +F- works because the prompt is left on the stack when control-at is called
; so we can call it again.
#;
((λ (p) (prompt-at p (+ (control-at p k (k 3))
                        (control-at p k (k 4)))))
 (new-prompt))

; +F+ works here, because it leaves the prompt on the stack, so we can shift-at again!
#;
((λ (p) (reset-at p (+ (shift-at p k (k 3))
                       (shift-at p k (k 4)))))
 (new-prompt))




;;;;; Worrying about the second +- is about if the prompt gets
;;;;; reinstated after reinstating the continuation.

;; works on cekm.rkt machine.
#;
((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) (k (-F- p (λ (k2) (k2 5)))))))))
 (newPrompt))
