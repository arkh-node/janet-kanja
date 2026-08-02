# Type demands (symbolo, numbero) and absence (absento).
#
# Same discipline as the disequality suite: what matters is not that a demand
# rejects a value put in front of it, but that it SURVIVES and fires later.
# And that a standing demand is shown in the answer — an answer that hides it
# claims to know less than it does, which for a relational answer is a lie.

(import ../kanja :as k)
(import ./harness :as h)

(h/start-suite "constraints")

(def- _0 (symbol "_.0"))
(def- _1 (symbol "_.1"))

### ── decided on the spot ────────────────────────────────────────────────────
(h/check "symbolo accepts a keyword" (k/run* [q] (k/symbolo :a) (k/== q :ok)) @[:ok])
(h/check "symbolo accepts a symbol" (k/run* [q] (k/symbolo 'a) (k/== q :ok)) @[:ok])
(h/check "symbolo rejects a number" (k/run* [q] (k/symbolo 5) (k/== q :ok)) @[])
(h/check "symbolo rejects a list"
         (k/run* [q] (k/symbolo (k/llist 1)) (k/== q :ok)) @[])
(h/check "numbero accepts a number" (k/run* [q] (k/numbero 5) (k/== q :ok)) @[:ok])
(h/check "numbero rejects a keyword" (k/run* [q] (k/numbero :a) (k/== q :ok)) @[])

### ── the demand outlives the moment ─────────────────────────────────────────
(h/check "symbolo waits and lets through what fits"
         (k/run* [q] (k/symbolo q) (k/== q :late)) @[:late])
(h/check "symbolo waits and cuts off what does not fit"
         (k/run* [q] (k/symbolo q) (k/== q 5)) @[])
(h/check "numbero waits and cuts off what does not fit"
         (k/run* [q] (k/numbero q) (k/== q :a)) @[])
(h/check "a demand through an intermediary: x is tied to q BEFORE q has a value"
         (k/run* [q] (k/fresh [x] (k/symbolo x) (k/== x q) (k/== q 5))) @[])

### ── demands must agree ─────────────────────────────────────────────────────
(h/check "one thing cannot be both a symbol and a number"
         (k/run* [q] (k/symbolo q) (k/numbero q)) @[])
(h/check "two demands of the same kind coexist"
         (k/run* [q] (k/symbolo q) (k/symbolo q) (k/== q :a)) @[:a])
(h/check "a conflict through an intermediary is caught too"
         (k/run* [q] (k/fresh [x] (k/symbolo q) (k/numbero x) (k/== x q))) @[])

### ── absento: absence at any depth ──────────────────────────────────────────
(h/check "absento on a bare atom" (k/run* [q] (k/absento :x :y) (k/== q :ok)) @[:ok])
(h/check "absento catches the tag itself" (k/run* [q] (k/absento :x :x) (k/== q :ok)) @[])
(h/check "absento catches what is nested deep"
         (k/run* [q] (k/absento :x (k/llist 1 (k/llist 2 :x))) (k/== q :ok)) @[])
(h/check "absento lets through when the tag is absent"
         (k/run* [q] (k/absento :x (k/llist 1 (k/llist 2 :y))) (k/== q :ok)) @[:ok])
(h/check "absento catches it inside a native Janet tuple"
         (k/run* [q] (k/absento :x [1 [2 :x]]) (k/== q :ok)) @[])

# The point of the store: at the moment of the demand the term is not yet known.
(h/check "absento fires LATER, when the hole receives the tag"
         (k/run* [q] (k/absento :x (k/llist 1 (k/llist 2 q))) (k/== q :x)) @[])
(h/check "the same shape lets a different value through"
         (k/run* [q] (k/absento :x (k/llist 1 (k/llist 2 q))) (k/== q :y)) @[:y])
(h/check "absento is stronger than =/= : it forbids occurrence, not equality"
         (k/run* [q] (k/absento :x q) (k/== q (k/llist :x))) @[])
(h/check "=/= does not forbid the same — that is the difference"
         (length (k/run* [q] (k/=/= q :x) (k/== q (k/llist :x)))) 1)

### ── standing demands are shown in the answer ───────────────────────────────
(h/check "a surviving symbolo is visible" (k/run* [q] (k/symbolo q)) @[[_0 ~(sym ,_0)]])
(h/check "a surviving numbero is visible" (k/run* [q] (k/numbero q)) @[[_0 ~(num ,_0)]])
(h/check "a surviving absento is visible"
         (k/run* [q] (k/absento :x q)) @[[_0 ~(absento (:x ,_0))]])
(h/check "demands of different kinds are shown together"
         (k/run* [q] (k/symbolo q) (k/=/= q :a))
         @[[_0 ~(=/= ((,_0 :a))) ~(sym ,_0)]])
(h/check "a demand about an invisible variable is not shown"
         (k/run* [q] (k/fresh [x] (k/symbolo x) (k/== q :value))) @[:value])

### ── interaction with search ────────────────────────────────────────────────
(h/check "a demand acts in each branch separately"
         (k/run* [q] (k/numbero q) (k/conde [(k/== q 1)] [(k/== q :a)] [(k/== q 3)]))
         @[1 3])
(h/check "demand and relation together: only the numeric members"
         (k/run* [q] (k/numbero q)
                 (k/conde [(k/== q 1)] [(k/== q :two)] [(k/== q 3)] [(k/== q :four)]))
         @[1 3])

### ── absento: the tag need not be an atom ───────────────────────────────────
###
### Until 02.08.2026 the comparison against the tag came AFTER descending into
### the term, so a compound tag only ever met leaves — and a leaf it never
### equals. `absento` with a non-atomic tag silently succeeded always, handing
### back an answer where there is none. Every expectation below is taken from
### the canon (faster-minikanren under Guile), not derived from meaning.

(def- l12 (k/llist 1 2))

(h/check "a compound tag is caught at the root of the term"
         (k/run* [q] (k/absento l12 q) (k/== q (k/llist 1 2))) @[])
(h/check "a compound tag is caught at depth"
         (k/run* [q] (k/absento l12 q) (k/== q (k/llist 9 (k/llist 1 2)))) @[])
(h/check "a compound tag is caught deeper than one level"
         (k/run* [q] (k/absento l12 q) (k/== q (k/llist 9 (k/llist 8 (k/llist 1 2))))) @[])
(h/check "a compound tag fires LATER, when the term grows into it"
         (k/run* [q] (k/fresh [a] (k/absento l12 q) (k/== q (k/llist 9 a)) (k/== a (k/llist 1 2))))
         @[])
(h/check "a compound tag lets an unlike term through"
         (map k/to-array (k/run* [q] (k/absento l12 q) (k/== q (k/llist 1 3))))
         @[@[1 3]])
(h/check "a term cannot fail to contain itself"
         (k/run* [q] (k/absento q q)) @[])
(h/check "an atom cannot fail to contain itself"
         (k/run* [q] (k/absento 'x 'x) (k/== q :ok)) @[])

# A tag holding a FREE variable may still turn out different from the term, so
# the demand does not kill the branch, it waits. The canon answers `(ok)` here.
(h/check "a tag holding a free variable does not reject at once"
         (k/run* [q] (k/fresh [x] (k/absento (k/llist 1 x) (k/llist 1 2)) (k/== q :ok)))
         @[:ok])

# 🔴 The tag is reified just like the term. Until it was, a compound tag with a
# variable inside printed the engine's internals into the answer:
# `(:kanja/var 1)`. The PRINTED form is checked — what a person actually sees:
# that is where the raw variable leaked, and a structural check would miss it.
(h/check "a compound tag does not show the engine's internals in the answer"
         (map k/show (k/run* [q] (k/absento l12 q)))
         @["(_.0 (absento ((1 2) _.0)))"])
(h/check "a demand with an invisible variable in the TAG is not shown"
         (map k/show (k/run* [q] (k/fresh [x] (k/absento (k/llist 1 x) q) (k/== q (k/llist 1 2)))))
         @["(1 2)"])

# Here the tag's variable IS visible in the answer and the demand survived, so
# the tag must be reified like the term: `(1 _.0)`, not `(1 (:kanja/var 1))`.
# ⚠️ The canon prints the same thing differently — `(=/= ((_.0 1) (_.1 1)))
# (absento ((1 _.0) _.1))`: it pushes the demand down to the leaves and folds
# part of it into `=/=`. Same meaning, our shape. A known divergence.
(h/check "a visible variable in the tag is reified, not leaked raw"
         (map k/show (k/run* [q] (k/fresh [x y] (k/== q (k/llist x y)) (k/absento (k/llist 1 x) q))))
         @["((_.0 _.1) (=/= ((_.0 1) (_.1 1))) (absento ((1 _.0) _.1)))"])

(h/finish)
