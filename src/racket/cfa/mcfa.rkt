#lang racket

(require (only-in racket/hash hash-union))

; context sensitivity.
(define m 3)
(define (take xs n)
  (if (or (equal? n 0) (empty? xs))
      '()
      (cons (car xs) (take (cdr xs) (- n 1)))))

; state types
(struct E (e ρ σ aκ) #:transparent)
(struct A (v ρ σ aκ) #:transparent)

; address types
(struct baddr (x ρ) #:transparent)
(struct kaddr (e ρ) #:transparent)

(struct closure (lam ρ) #:transparent)

; environments are a representation of the call stack
(struct env (calls) #:transparent)

; Continuations
(struct ktype () #:transparent)
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef ρ aκ) #:transparent)
(struct setk ktype (a aκ) #:transparent)
(struct callcck ktype (callccexp aκ) #:transparent)
(struct applyk ktype (applyexp v? e ρ aκ) #:transparent)
(struct callk ktype (call done todo ρ aκ) #:transparent)

; abstract values
; the inner value lattice, then sets of closures, continuations, and primitives.
(struct aval (cval clos konts prims) #:transparent)

(define (truthy? av)
  (match av
    [(aval '⊤ _ _ _) #f]
    [(aval iv _ _ _) (not (equal? iv #f))]
    [_ #f]))
(define (falsy? av)
  (equal? av (make-aval #f)))

; aval construction, infers the correct aval based on input concrete value.
(define (make-aval v)
  (match v
    [(? closure?) (aval '⊥ (set v) (set) (set))]
    [(? ktype?) (aval '⊥ (set) (set v) (set))]
    [(? prim?) (aval '⊥ (set) (set) (set v))]
    [_ (aval v (set) (set) (set))]))

; constructs a top valued aval.
(define (make-top) (aval '⊤ (set) (set) (set)))

(define (is-number? v)
  (match v
    [(aval (? number? n) (? set?) (? set?) (? set?)) n]
    [_ '()]))

; primitive functions, implemented by the implementation
(struct prim (op) #:transparent)

(define prim-+
  (call/cc (λ (ret) (λ xs (make-aval
                           (foldl (λ (x res) (match (is-number? x)
                                               [(? number? n) (+ res n)]
                                               ['() (ret (make-top))]))
                                  0 xs))))))

(define prims
  (hash '+ (prim prim-+)
        '* (prim error)
        'equal? (prim error)
        'number? (prim error)
        'boolean? (prim error)
        'continuation? (prim error)
        'list (prim error)
        'cons (prim error)
        'car (prim error)
        'cdr (prim error)
        'null (prim (λ () (make-aval null)))))

; checks if a symbol is lambda or λ
(define (λ-start? s)
  (match s
    [(or (== 'λ) (== 'lambda)) #t]
    [else #f]))

; checks if the expression given is a lambda expression
(define (λ? e)
  (match e
    ; standard multiarg lambda
    [`(,(? λ-start?) (,_ ...) ,_) #t]
    ; vararg lambda
    [`(,(? λ-start?) ,(? symbol?) ,_) #t]
    [else #f]))

; checks a syntactic expression to see
; if its an atomically evaluable expression
(define (atomic? v)
  (match v
    [(or (? symbol?) (? λ?)
         (? number?) (? boolean?)
         `(quote ,_)) #t]
    [_ #f]))

(define (iv-join ivo ivn)
  (cond
    [(equal? '⊥ ivo) ivn]
    [(equal? '⊥ ivn) ivo]
    [(equal? ivo ivn) ivo]
    [else '⊤]))

(define (aval-join av1 av2)
  (match-define (aval iv-o clos-o ks-o ops-o) av1)
  (match-define (aval iv-n clos-n ks-n ops-n) av2)
  (define n-clos (set-union clos-o clos-n))
  (define n-ks (set-union ks-o ks-n))
  (define n-ops (set-union ops-o ops-n))
  (define n-iv (iv-join iv-o iv-n))
  (aval n-iv n-clos n-ks n-ops))

; STORE
(define (σ-join σ k v)
  (match k
    [(? kaddr?)
     (hash-set σ k (set-union (set v) (hash-ref σ k (set))))]
    [(? baddr?)
     (match (hash-ref σ k '())
       ['() (hash-set σ k v)]
       [(? aval? av-old) (hash-set σ k (aval-join av-old v))])]))

(define σ-ref hash-ref)
(define σ-has-key? hash-has-key?)

; ENVIRONMENT
;
; To make a new environment, you simply append
; the newest call to the stack, and increment the address
(define (ρ-new ρ e)
  (match-define (env calls) ρ)
  (env (take (cons e calls) m)))

; finds all variables that do not have a binding
; inside of the expression.
;
; returns a list of all unbound vars.
(define (find-free-vars e bound)
  (match e
    [`(,(? λ-start?) (,xs ...) ,eb)
     (find-free-vars eb (foldl (λ (x s) (set-add s x)) bound xs))]
    [`(,(? λ-start?) ,x ,eb)
     (find-free-vars eb (set-add bound x))]
    [(? symbol?) ; check if its bound or its a prim
     (if (or (set-member? bound e) (hash-has-key? prims e))
         '() (list e))]
    [(or (? number?) (? boolean?) `(quote ,_)) '()]
    [`(if ,ec ,et ,ef)
     (append (find-free-vars ec bound)
             (find-free-vars et bound)
             (find-free-vars ef bound))]
    [`(set! ,x ,e)
     (append (if (set-member? bound x) '() (list x))
             (find-free-vars e bound))]
    [`(call/cc ,e) (find-free-vars e bound)]
    [`(apply ,ef ,ea)
     (append (find-free-vars ef bound) (find-free-vars ea bound))]
    [`(let ([,xs ,es] ...) ,eb)
     (append (foldl (λ (e r) (append (find-free-vars e bound) r)) '() es)
             (find-free-vars eb (foldl (λ (x r) (set-add r x)) bound xs)))]
    [`(,es ...)
     (foldl (λ (e t) (append t (find-free-vars e bound))) '() es)]
    [_ (error (format "We do not cover the case of '~a'" e))]))

(define (call-clo clo arg-vals ρ σ ctx aκ)
  (match clo
    [(closure `(,_ (,xs ...) ,eb) ρλ)
     (define n-ρ (ρ-new ρ ctx))
     (define arg-addrs (map (λ (x) (baddr x n-ρ)) xs))
     (define free-vars (find-free-vars `(λ ,xs ,eb) (set)))
     (define free-addrs (map (λ (x) (baddr x n-ρ)) free-vars))
     (define free-vals (map (λ (x) (σ-ref σ (baddr x ρλ))) free-vars))
     (define n-σ
       (foldl (λ (k v res) (σ-join res k v))
              σ (append free-addrs arg-addrs) (append free-vals arg-vals)))
     (E eb n-ρ n-σ aκ)]
    [(closure `(,_ ,x ,eb) ρλ)
     (define n-ρ (ρ-new ρ ctx))
     (define arg-addr (baddr x n-ρ))
     (define free-vars (find-free-vars `(λ ,x ,eb) (set)))
     (define free-addrs (map (λ (x) (baddr x n-ρ)) free-vars))
     (define free-vals (map (λ (x) (σ-ref σ (baddr x ρλ))) free-vars))
     (define n-σ
       (foldl (λ (k v res) (σ-join res k v))
              (σ-join σ arg-addr arg-vals) free-addrs free-vals))
     (E eb n-ρ n-σ aκ)]))

(define (call-κ κ arg-vals ρ σ ctx)
  (match-define (list v) arg-vals)
  (define aκ (kaddr ctx ρ))
  (define n-σ (σ-join σ aκ κ))
  (A v ρ n-σ aκ))

(define (call-op primop arg-vals ρ σ aκ)
  (match-define (prim op) primop)
  (define v (apply op arg-vals))
  (A v ρ σ aκ))

(define (call vf arg-vals ρ σ ctx aκ)
  (match-define (aval _ clos κs ops) vf)
  (define ς-clo (map (λ (clo) (call-clo clo arg-vals ρ σ ctx aκ)) clos))
  (define ς-κ (map (λ (κ) (call-κ κ arg-vals ρ σ ctx)) κs))
  (define ς-op (map (λ (op) (call-op op arg-vals ρ σ aκ)) ops))
  (list->set (append ς-clo ς-κ ς-op)))

(define (atomic-eval ς)
  (match-define (E e ρ σ _) ς)
  (match e
    [(or (? boolean?) (? number?)) (make-aval e)]
    [`(quote ,e) (make-aval e)] ; already quoted :)
    [(? symbol?)
     #:when (and (not (σ-has-key? σ (baddr e ρ)))
                 (hash-has-key? prims e))
     (make-aval (hash-ref prims e))]
    [(? λ?) (make-aval (closure e ρ))]
    [(? symbol?) (σ-ref σ (baddr e ρ))]))

(define (step-eval ς)
  (match-define (E eς ρ σ aκ) ς)
  (match eς
    [(? atomic?)
     (define v (atomic-eval ς))
     (A v ρ σ aκ)]
    [`(if ,ec ,et ,ef)
     (define next-aκ (kaddr ec ρ))
     (define κ (ifk et ef ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ec ρ next-σ next-aκ)]
    [`(let ([,xs ,es] ...) ,eb)
     (E `((λ ,xs ,eb) ,@es) ρ σ aκ)]
    [`(set! ,x ,e)
     (define a (baddr x ρ))
     (define next-aκ (kaddr e ρ))
     (define κ (setk a aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(call/cc ,e)
     (define next-aκ (kaddr e ρ))
     (define κ (callcck eς aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(apply ,ef,e)
     (define next-aκ (kaddr ef ρ))
     (define κ (applyk eς '() e ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]
    [`(,ef ,es ...)
     (define next-aκ (kaddr ef ρ))
     (define κ (callk eς '() es ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]))

(define (step-apply ς)
  (match-define (A v ρ σ aκ) ς)
  (define κςs (σ-ref σ aκ))
  (define (process-κ κς)
    (match κς
      [(mtk) (set)]
      [(ifk et ef ρκ n-aκ)
       (define t-branch (set (E et ρκ σ n-aκ)))
       (define f-branch (set (E ef ρκ σ n-aκ)))
       (define both-branches (set-union t-branch f-branch))
       (if (truthy? v)
           t-branch
           (if (falsy? v)
               f-branch
               both-branches))]
      [(setk a n-aκ)
       (define n-σ (σ-join σ a v))
       (set (A (make-aval (void)) ρ n-σ n-aκ))]
      [(callcck ctx n-aκ)
       (define κs (σ-ref σ n-aκ))
       (foldl set-union (set)
              (list->set (set-map κs (λ (n-κ) (call v (list n-κ) ρ σ ctx n-aκ)))))]
      [(applyk ctx '() e ρκ n-aκ)
       (define n-n-aκ (kaddr e ρκ))
       (define n-κ (applyk ctx v e ρκ n-aκ))
       (define n-σ (σ-join σ n-n-aκ n-κ))
       (set (E e ρκ n-σ n-n-aκ))]
      [(applyk ctx vf _ _ n-aκ)
       (call vf v ρ σ ctx n-aκ)]
      [(callk ctx done (cons eh et) ρκ n-aκ)
       (define n-n-aκ (kaddr eh ρκ))
       (define n-κ (callk ctx (append done (list v)) et ρκ n-aκ))
       (define n-σ (σ-join σ n-n-aκ n-κ))
       (set (E eh ρκ n-σ n-n-aκ))]
      [(callk ctx done '() _ n-aκ)
       (match-define (cons vh vt) (append done (list v)))
       (call vh vt ρ σ ctx n-aκ)]))
  (foldl set-union (set) (set-map κςs (λ (κ) (process-κ κ)))))

; forms an initial state from an expression
(define (inject e)
  (define env0 (env '()))
  (define kaddr0 (kaddr e env0))
  (E e env0 (hash kaddr0 (set (mtk))) kaddr0))

(define fix? equal?)

; iterates an initial state until there is no more new states
(define (store-combine σ1 σ2)
  (hash-union σ1 σ2
              #:combine/key (λ (_ a b) (aval-join a b))))

(define (eval program)
  (define (step ς)
    (match ς
      [(? E?) (set (step-eval ς))]
      [(? A?) (step-apply ς)]))
  (define (combine ςs)
    (define global
      (foldl (λ (ς res) (match ς
                          [(E _ _ σ _)
                           (store-combine res σ)]
                          [(A _ _ σ _)
                           (store-combine res σ)]))
             (hash) (set->list ςs)))
    (list->set
     (set-map
      ςs (λ (ς) (match ς
                  [(E c e s k) (E c e global k)]
                  [(A c e s k) (A c e global k)])))))
  (define (run cfg todo)
    (match todo
      ['() cfg]
      [(cons doing tail)
       (if (hash-has-key? cfg doing)
           (run cfg tail)
           (let* ([stepped (step doing)]
                  [combined (combine stepped)]
                  [cfg (hash-set cfg doing combined)]
                  [todo (append (set->list combined) todo)])
             (run cfg todo)))]))
  (run (hash) (list (inject program))))

(define e eval)

; test suite?
#;
(list
 ; tests just functions doing function things, and also a free variable used.
 ; super simple, should complete in a state with (λ (a) a) as the value.
 (e '((λ (free) ((λ (d) d) ((λ (e) e) ((λ () free)))))
      ((λ (c) c) ((λ (b) b) (λ (a) a)))))
 ; smaller version of the last test
 (e '((λ (free) ((λ () free)))
      (λ (x) x)))
 ; testing simple function call and if expression and numbers
 ; returns 12
 (e '((λ (x) x) (if #f 3 12)))
 ; similar as the last test, but returns a singleton list of 12
 (e '((λ x x) (if #t 12 3)))
 ; testing let and set!, should return 42069
 (e '(let ([x 12]) ((λ (_) x) (set! x 42069))))
 ; testing that prims work, returns 489
 (e '(+ 420 69))
 ; testing applying a prim
 (e '(apply + (list 420 69)))
 )
