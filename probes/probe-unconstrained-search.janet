# A DELIBERATELY simplified interpreter: no absento, no not-in-envo.
# It is unsound (a program can forge a closure), but it exists for exactly
# one experiment: to learn what eats the search — the demands or the walk.
(import ../kanja :as k)
(var ev nil)
(defn lookupo [x env t]
  (k/fresh [y v rest]
    (k/== (k/llist* (k/cons* y v) rest) env)
    (k/conde [(k/== y x) (k/== v t)]
             [(k/=/= y x) (lookupo x rest t)])))
(defn plist [exp env val]
  (k/conde
    [(k/== k/NIL exp) (k/== k/NIL val)]
    [(k/fresh [a d ta td]
       (k/== (k/cons* a d) exp) (k/== (k/cons* ta td) val)
       (ev a env ta) (plist d env td))]))
(set ev (fn ev [exp env val]
  (k/conde
    [(k/fresh [v] (k/== (k/llist 'quote v) exp) (k/== v val))]
    [(k/fresh [args] (k/== (k/cons* 'list args) exp) (plist args env val))]
    [(k/symbolo exp) (lookupo exp env val)]
    [(k/fresh [rator rand x body env2 a]
       (k/== (k/llist rator rand) exp)
       (ev rator env (k/llist 'closure x body env2))
       (ev rand env a)
       (ev body (k/llist* (k/cons* x a) env2) val))]
    [(k/fresh [x body]
       (k/== (k/llist 'lambda (k/llist x) body) exp)
       (k/symbolo x)
       (k/== (k/llist 'closure x body env) val))])))
(def t0 (os/clock))
(def r (k/run 1 [q] (ev q k/NIL q)))
(printf "%d ms" (math/round (* 1000 (- (os/clock) t0))))
(each x r (printf "%s" (k/show x)))
