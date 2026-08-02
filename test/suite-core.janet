# Core: variables, unification, goals, macros, reification.
# Expected answers are taken from canonical miniKanren behaviour, not from
# whatever this implementation happens to print.

(import ../kanja :as k)
(import ./harness :as h)

(h/start-suite "core")

### ── logic variables ────────────────────────────────────────────────────────
(h/check-true "lvar? recognises its own variable" (k/lvar? (k/lvar 0)))
(h/check-true "lvar? is not fooled by an ordinary tuple" (not (k/lvar? [1 2])))
(h/check-true "lvar? is not fooled by a pair" (not (k/lvar? (k/cons* 1 k/NIL))))

### ── lists ──────────────────────────────────────────────────────────────────
(h/check "llist builds a list" (k/to-array (k/llist 1 2 3)) @[1 2 3])
(h/check "the empty list" (k/to-array (k/llist)) @[])
(h/check "nested lists are walked all the way down"
         (k/to-array (k/llist 1 (k/llist 2 3))) @[1 @[2 3]])

### ── unification ────────────────────────────────────────────────────────────
(h/check "equality of atoms" (k/run* [q] (k/== q 5)) @[5])
(h/check "the incompatible yields no answers" (k/run* [q] (k/== 1 2)) @[])
(h/check "a variable inside a native tuple" (k/run* [q] (k/== [1 q 3] [1 :two 3])) @[:two])
(h/check "native arrays unify element-wise"
         (k/run* [q] (k/== @[1 q] @[1 :yes])) @[:yes])
(h/check "different lengths do not unify" (k/run* [q] (k/== [1 2] [1 2 3])) @[])
(h/check "a variable is bound once"
         (k/run* [q] (k/== q 1) (k/== q 2)) @[])

### ── goals ──────────────────────────────────────────────────────────────────
(h/check "succeed changes nothing"
         (k/run* [q] (k/== q :ok) k/succeed) @[:ok])
(h/check "fail cuts the branch" (k/run* [q] (k/== q :ok) k/fail) @[])
(h/check "conj with no goals = succeed" (k/run* [q] (k/== q 1) (k/conj)) @[1])
(h/check "disj with no goals = fail" (k/run* [q] (k/== q 1) (k/disj)) @[])
(h/check "disj yields both branches"
         (k/run* [q] (k/disj (k/== q 1) (k/== q 2))) @[1 2])

### ── conde ──────────────────────────────────────────────────────────────────
(h/check "conde walks the branches"
         (k/run* [q] (k/conde [(k/== q :a)] [(k/== q :b)] [(k/== q :c)]))
         @[:a :b :c])
(h/check "a branch with two goals"
         (k/run* [q] (k/fresh [x] (k/conde [(k/== x 1) (k/== q x)]
                                           [(k/== x 2) (k/== q x)])))
         @[1 2])

### ── fresh and reification ──────────────────────────────────────────────────
(h/check "an unbound variable prints as _.0"
         (k/run* [q] k/succeed) @[(symbol "_.0")])
(h/check "two unbound ones are numbered in order of appearance"
         (k/run* [q] (k/fresh [x y] (k/== q [x y])))
         @[[(symbol "_.0") (symbol "_.1")]])
(h/check "the same variable gets one name"
         (k/run* [q] (k/fresh [x] (k/== q [x x])))
         @[[(symbol "_.0") (symbol "_.0")]])

### ── appendo: the relation that runs in every direction ─────────────────────
(defn appendo [l s out]
  (k/conde
    [(k/== l k/NIL) (k/== s out)]
    [(k/fresh [a d res]
       (k/== (k/cons* a d) l)
       (k/== (k/cons* a res) out)
       (appendo d s res))]))

(defn- answers [xs] (map k/to-array xs))

(h/check "appendo forwards"
         (answers (k/run* [q] (appendo (k/llist 1 2) (k/llist 3 4) q)))
         @[@[1 2 3 4]])
(h/check "appendo backwards: what was appended"
         (answers (k/run* [q] (appendo (k/llist 1 2) q (k/llist 1 2 3 4))))
         @[@[3 4]])
(h/check "appendo backwards: what stood in front"
         (answers (k/run* [q] (appendo q (k/llist 3 4) (k/llist 1 2 3 4))))
         @[@[1 2]])
(h/check "appendo every way: all splits of [1 2 3]"
         (answers (k/run* [q] (k/fresh [x y]
                                (appendo x y (k/llist 1 2 3))
                                (k/== q (k/llist x y)))))
         @[@[@[] @[1 2 3]] @[@[1] @[2 3]] @[@[1 2] @[3]] @[@[1 2 3] @[]]])

### ── infinite relations ─────────────────────────────────────────────────────
# The point of the interleaving search: a relation with infinitely many answers
# can be written down, and asking for N answers terminates.
(h/check "an infinite relation yields exactly as many as asked"
         (length (k/run 6 [q] (k/fresh [x y z]
                                (appendo x y z)
                                (k/== q (k/llist x y z)))))
         6)

# Completeness: an answer that lives behind an infinite sibling branch must
# still be reached. Depth-first search would hang here.
(defn- naturals [x]
  (k/conde
    [(k/== x :zero)]
    [(k/fresh [n] (k/== x (k/cons* :succ n)) (naturals n))]))

(h/check "an answer behind an infinite branch is still reachable"
         (k/run 1 [q] (k/conde [(k/fresh [x] (naturals x) k/fail)]
                               [(k/== q :found)]))
         @[:found])

### ── run over several variables at once ─────────────────────────────────────
###
### The canon does this: `(run* (a b) ...)` answers with a list of values in
### the order the variables are written. Until 02.08.2026 the macro silently
### took only the first, and goals mentioning the rest failed to compile with
### `unknown symbol x` — a message saying nothing about the cause.
### Expectations taken from the canon, answer order included.

(h/check "run* over two variables answers with a list"
         (map k/show (k/run* [a b] (k/== a 1) (k/== b 2))) @["(1 2)"])
(h/check "run* over three variables"
         (map k/show (k/run* [a b c] (k/== a 1) (k/== b 2) (k/== c 3))) @["(1 2 3)"])
(h/check "several variables with a fork: canon order"
         (map k/show (k/run* [a b] (k/conde [(k/== a 1) (k/== b 2)]
                                            [(k/== a 3) (k/== b 4)])))
         @["(1 2)" "(3 4)"])
(h/check "run with an answer limit over two variables"
         (length (k/run 2 [a b] (k/conde [(k/== a 1) (k/== b 2)]
                                         [(k/== a 3) (k/== b 4)]
                                         [(k/== a 5) (k/== b 6)])))
         2)
(h/check "a single variable works as before"
         (k/run* [q] (k/== q 5)) @[5])
(h/check "demands survive with several variables too"
         (map k/show (k/run* [a b] (k/symbolo a) (k/== b 1))) @["((_.0 1) (sym _.0))"])

### ── printing: the quote shorthand ──────────────────────────────────────────
###
### `(quote x)` prints as `'x`, the way every Lisp has written it since 1960.
###
### ⚠️ This is OURS, not the canon's: faster-minikanren prints the form in full.
### The step is deliberate and confined to printing — the checks below also
### pin down that the ENGINE is untouched, so that the shorthand can never
### become a difference in meaning.

(h/check "(quote x) prints as 'x"
         (k/show (k/llist 'quote 'x)) "'x")
(h/check "the quoted thing may be a list"
         (k/show (k/llist 'quote (k/llist 'lambda 'x))) "'(lambda x)")
(h/check "quote nested inside a list"
         (k/show (k/llist 'list 'x (k/llist 'quote 'x))) "(list x 'x)")
(h/check "quote inside quote"
         (k/show (k/llist 'quote (k/llist 'quote 'x))) "''x")
# The shorthand means exactly "a two-element list starting with quote".
# Anything else keeps its full form, or the printed text would say something
# the term does not.
(h/check "three elements are NOT shortened"
         (k/show (k/llist 'quote 'a 'b)) "(quote a b)")
(h/check "an improper tail is NOT shortened"
         (k/show (k/llist* 'quote 'a 'b)) "(quote a . b)")
# And through a real answer, where the hole is reified: the shorthand must
# survive reification, since that is the only path a user ever sees.
(h/check "the shorthand survives reification"
         (map k/show (k/run* [q] (k/fresh [x] (k/== q (k/llist 'quote x)))))
         @["'_.0"])
(h/check "a bare symbol quote is left alone"
         (k/show 'quote) "quote")
# 🔴 The engine knows nothing of this: only `show` does.
(h/check "to-array keeps the full structure"
         (k/to-array (k/llist 'quote 'x)) @['quote 'x])
(h/check "and the term still unifies as (quote x)"
         (k/run* [q] (k/== q (k/llist 'quote 'x))
                 (k/fresh [a] (k/== (k/llist 'quote a) q) (k/== a 'x)))
         @[(k/llist 'quote 'x)])

(h/finish)
