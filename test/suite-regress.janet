# Invariant guards. Added by ArkH on 02.08.2026 after a mutation audit.
#
# The other suites check that the engine does the right thing. This one checks
# that the invariants explained in the code by a comment CANNOT be removed
# silently.
#
# 🔴 Why it exists. A mutation run (12 one-at-a-time breakages of the engine,
# by a mutation bench kept beside the canon) caught eight and missed four —
# and three of the four missed ones sat directly under a comment explaining why
# it was done that way. The law drawn from that:
#
#     every comment explaining "why it is done this way" is a claim on a test.
#     If an invariant deserves an explanation, it deserves a mutation
#     that removes it.
#
# Each check below is named together with the mutation it must catch.

(import ../kanja :as k)
(import ../kanja/relations :as r)
(import ./harness :as h)

(h/start-suite "regress")

(def- _0 (symbol "_.0"))
(defn- L [& xs] (k/llist ;xs))
(defn- shown [answers] (map k/show answers))

### ── occurs-check ───────────────────────────────────────────────────────────
###
### Catches the mutation: `ext-s` without the occurs check.
###
### This one is worth more than all the other invariants together: its absence
### was the very reason the quine would not be generated, and it cost two
### agents two days and 8.6 GB of memory. Until 02.08 removing the occurs check
### turned NOT ONE check in the battery red.
###
### 🔴 Asked of `unify` DIRECTLY, not through `run`. Without the occurs check a
### circular term does not produce a wrong ANSWER — it sends the very first
### traversal into infinite recursion. A test written through `run` would not
### go red, it would HANG, and a hanging test is indistinguishable from a slow
### machine. A check is obliged to return a verdict, not silence.

(def- q0 (k/lvar 0))
(h/check-true "occurs-check: a variable will not bind to a pair containing itself"
              (nil? (k/unify q0 (k/cons* q0 q0) {})))
(h/check-true "occurs-check: nor to a list containing itself"
              (nil? (k/unify q0 (L 'quote q0) {})))
(h/check-true "occurs-check: nor to a native Janet tuple containing itself"
              (nil? (k/unify q0 [1 q0] {})))
(h/check-true "occurs-check does not get in the way of an ordinary binding"
              (not (nil? (k/unify q0 5 {}))))
(h/check "occurs-check shows at the relational level too: no answers, not infinity"
         (k/run* [q] (k/== q (k/cons* q q))) @[])

### ── absento is deferred ────────────────────────────────────────────────────
###
### Catches the mutation: `verify-absent` discards a demand that is not yet
### settled (`:maybe` treated as "no").
###
### Three answers instead of two are the whole reason absento needs a store
### (see the docstring of `occurs-tag`). A demand dropped at the first recheck
### looks like it works right up to the step where it should have fired.

(h/check "absento survives a recheck and fires on the SECOND step"
         (k/run* [q] (k/fresh [a] (k/absento :x q) (k/== q (L 1 a)) (k/== a :x))) @[])
(h/check "absento survives a recheck and lets a fitting value through"
         (shown (k/run* [q] (k/fresh [a] (k/absento :x q) (k/== q (L 1 a)) (k/== a :y))))
         @["(1 :y)"])
(h/check "absento survives TWO rechecks"
         (k/run* [q] (k/fresh [a b] (k/absento :x q) (k/== q (L 1 a)) (k/== a (L 2 b)) (k/== b :x)))
         @[])

### ── an answer does not state the same prohibition twice ────────────────────
###
### Catches the mutation: `distinct` removed from the assembly of constraints
### in `reify`.
###
### One prohibition stated twice reads as two different facts. For an answer
### that consists entirely of what it reports about itself, that is a lie about
### how much is known.

(h/check "the same prohibition stated twice appears once in the answer"
         (shown (k/run* [q] (k/=/= q 5) (k/=/= q 5))) @["(_.0 (=/= ((_.0 5))))"])
(h/check "and that does not swallow a second, different prohibition"
         (shown (k/run* [q] (k/=/= q 5) (k/=/= q 5) (k/=/= q 6)))
         @["(_.0 (=/= ((_.0 5)) ((_.0 6))))"])

### ── the shape of a conjunction ─────────────────────────────────────────────
###
### Catches the mutation: `conj` folded right instead of left.
###
### The SET of answers does not depend on it; the order and the cost do. On
### generating the quine the right fold costs 302 ms against 132 ms, and the
### battery stays green throughout.
###
### 🔴 THIS IS A WITNESS, NOT A REFERENCE. On this very query the canon answers
### `(1 8) (2 8) (1 9) (2 9)` — our order of answers on a conjunction of two
### many-valued `conde` does NOT match it (measured 02.08; bench in
### against faster-minikanren under Guile). Completeness is intact: on an
### infinite goal the order matches the canon exactly — see the next check.
### is what the engine does NOW, so that it cannot change silently while the
### divergence is unexplained. Once it is explained, the expectation becomes
### the canonical order and this record goes away.

(h/check "WITNESS: order on a conjunction of two conde (the canon gives another)"
         (shown (k/run* [q] (k/fresh [a b]
                              (k/conde [(k/== a 1)] [(k/== a 2)])
                              (k/conde [(k/== b 8)] [(k/== b 9)])
                              (k/== q (L a b)))))
         @["(1 8)" "(1 9)" "(2 8)" "(2 9)"])

### ── completeness of the search ─────────────────────────────────────────────
###
### Catches the mutation: `mplus` without the swap in the delayed case.
###
### The swap is the only thing that makes the search complete. Without it a
### branch with infinite offspring starves its sibling, and an answer that
### exists is never found. Expectations taken from the canon.

(defn- nat [n x] (k/conde [(k/== x n)] [(nat (+ n 1) x)]))

(h/check "an infinite goal does not starve a finite fork (canon order)"
         (shown (k/run 8 [q] (k/fresh [a b]
                               (k/conde [(k/== a :A)] [(k/== a :B)])
                               (nat 0 b)
                               (k/== q (L a b)))))
         @["(:A 0)" "(:B 0)" "(:A 1)" "(:B 1)" "(:A 2)" "(:B 2)" "(:A 3)" "(:B 3)"])

# The expectation here was first written "from meaning" — `0 :else 1 2 3 4`, on
# the reasoning that the first branch comes first. The engine answered
# otherwise, and the engine was right: the canon gives exactly
# `(else 0 1 2 3 4)`. The infinite branch leaves behind one delay, and the
# finite one gets its answer in first. Recorded from the reference.
(h/check "a finite branch does not sink behind an infinite one (canon order)"
         (k/run 6 [q] (k/conde [(nat 0 q)] [(k/== q :else)]))
         @[:else 0 1 2 3 4])

### ── absento, spread down the term ──────────────────────────────────────────
###
### Catches the mutations: the prohibition falling out of a compound node is
### dropped; it never reaches the prohibition store; the fold of an `absento`
### on a typed variable loses the demand.
###
### 🔴 The boundary this guards, in the operator's words: the answer must get
### shorter in FORM, never poorer in CONTENT. Spreading a demand down a term
### and folding part of it into `=/=` is a change to how it is stored and
### printed — never to what it forbids. Every expectation is from the canon.

# A compound node cannot CONTAIN the tag, only equal it — so what stays there
# is a plain prohibition, and it has to fire later like any other.
(h/check "a prohibition falling out of absento fires later"
         (k/run* [q] (k/fresh [a] (k/absento (L 1 2) (L 1 a)) (k/== a 2) (k/== q :ok))) @[])
(h/check "and does not interfere when the node turns out different"
         (k/run* [q] (k/fresh [a] (k/absento (L 1 2) (L 1 a)) (k/== a 3) (k/== q :ok))) @[:ok])

# Once a variable is known to be an atom, "the tag is nowhere inside it" and
# "it is not the tag" are the same statement. Folding them must not lose it.
(h/check "absento on a typed variable is shown as a prohibition, not dropped"
         (shown (k/run* [q] (k/symbolo q) (k/absento 'x q)))
         @["(_.0 (=/= ((_.0 x))) (sym _.0))"])
(h/check "and the folded demand still fires"
         (k/run* [q] (k/symbolo q) (k/absento 'x q) (k/== q 'x)) @[])
(h/check "the fold survives the demands arriving in the other order"
         (shown (k/run* [q] (k/absento 'x q) (k/symbolo q)))
         @["(_.0 (=/= ((_.0 x))) (sym _.0))"])

# The same, but the prohibition is born during a RECHECK rather than when the
# demand was stated: the demand sat on a bare variable, the variable became a
# compound term, and only then did the node appear that must not equal the tag.
# That prohibition has to reach the store, or it forbids nothing.
(h/check "a prohibition born during a recheck reaches the store and fires"
         (k/run* [q] (k/fresh [a] (k/absento (L 1 2) q) (k/== q (L 1 a)) (k/== a 2))) @[])
(h/check "and lets the term through when the node turns out different"
         (shown (k/run* [q] (k/fresh [a] (k/absento (L 1 2) q) (k/== q (L 1 a)) (k/== a 3))))
         @["(1 3)"])

# A demand is re-spread on every check, so a term that grows keeps it honest.
(h/check "a demand spread once still fires three bindings later"
         (k/run* [q] (k/fresh [a b] (k/absento :x q) (k/== q (L 1 a))
                                    (k/== a (L 2 b)) (k/== b :x)))
         @[])

### ── BOUNDARY: two worlds of lists ──────────────────────────────────────────
###
### Not a mutation — a boundary that until 02.08 was written down NOWHERE:
### not in §6 of the design document, not in the REPL cheat sheet, not in the
### tests.
###
### 🔴 Why this matters more than it looks. Janet tuples have a fixed length and
### cannot express "a list whose tail is not yet known", so the engine carries
### its own pairs. Consequence: the relations in `relations.janet` build pairs
### and DO NOT MEET native Janet tuples. Someone arriving from "The Reasoned
### Schemer" writes a list as a literal — and gets an EMPTY ANSWER. And an empty
### answer here means "no solutions": indistinguishable from a real one.
###
### The checks below pin this down as KNOWN behaviour. If tuples ever start
### meeting pairs, these checks go red, and the decision will be taken
### deliberately rather than discovered by a user.

(h/check "BOUNDARY: a Janet tuple does not equal a kanren list of the same items"
         (k/run* [q] (k/== [1 2 3] (L 1 2 3)) (k/== q :equal)) @[])
(h/check "BOUNDARY: a relation over lists does not work on a Janet tuple"
         (k/run* [q] (r/membero q [1 2 3])) @[])
(h/check "BOUNDARY: an empty tuple is not the empty kanren list"
         (k/run* [q] (r/nullo []) (k/== q :empty)) @[])
(h/check "but a tuple does unify with a tuple, element-wise"
         (map k/to-array (k/run* [q] (k/== q [1 2 3]))) @[[1 2 3]])
(h/check "and a relation over lists does work on a kanren list"
         (k/run* [q] (r/membero q (L 1 2 3))) @[1 2 3])

(h/finish)
