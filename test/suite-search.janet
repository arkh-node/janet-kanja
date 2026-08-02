# Resumable search and the step budget.
#
# Two properties are claimed and therefore must be proved here:
#   1. taking answers in several sittings costs exactly what taking them in one
#      sitting costs — nothing is recomputed. Proved by the STEP COUNTER, not
#      by watching that the answers look right;
#   2. running out of budget is a different fact from running out of answers,
#      and the two are reported differently.

(import ../kanja :as k)
(import ./harness :as h)

(h/start-suite "search")

(defn- membero [x l]
  (k/conde
    [(k/fresh [d] (k/== (k/cons* x d) l))]
    [(k/fresh [a d] (k/== (k/cons* a d) l) (membero x d))]))

(def- six (k/llist 1 2 3 4 5 6))

### ── taking in one sitting vs in several ────────────────────────────────────

(def- in-one-go (k/search (fn [q] (membero q six))))
(def- all-of-them (k/take-more! in-one-go 6))

(def- in-parts (k/search (fn [q] (membero q six))))
(def- first-three (k/take-more! in-parts 3))
(def- next-three (k/take-more! in-parts 3))

(h/check "in one go — six answers" (length (all-of-them :answers)) 6)
(h/check "three and three — the same answers in the same order"
         (array/concat @[] (first-three :answers) (next-three :answers))
         (all-of-them :answers))
# 🔴 THIS is the proof of resumability: not "the answers look alike" but the COST is equal.
(h/check "and the same cost — nothing recomputed"
         (in-parts :steps) (in-one-go :steps))
# 🔴 "Exhausted" is a DISCOVERY, not a consequence of counting. Having taken six
# answers out of six we do not yet know a seventh is absent: to know, you look.
# Claiming exhaustion earlier would mean looking ahead — doing work nobody
# asked for, and losing the property that a take costs only what it yields.
(h/check "six taken, but exhaustion is not yet known"
         (k/search-exhausted? in-parts) false)
(def- nothing-left (k/take-more! in-parts 1))
(h/check "the next look yields no answers" (length (nothing-left :answers)) 0)
(h/check "and this is NOT a budget stop" (nothing-left :stopped-early) false)
(h/check "now it is exhausted" (k/search-exhausted? in-parts) true)

### ── the budget ─────────────────────────────────────────────────────────────

(def- stingy (k/search (fn [q] (membero q six))))
(def- too-few (k/take-more! stingy 6 1))

(h/check "the budget stops it and says so" (too-few :stopped-early) true)
(h/check "a search stopped early is NOT exhausted" (k/search-exhausted? stingy) false)
# "the budget ran out" and "the answers ran out" are different facts.
(h/check "an exhausted search is NOT marked as stopped early"
         ((k/take-more! (k/search (fn [q] (k/== q 1))) 5) :stopped-early) false)

(def- onward (k/take-more! stingy 6))
(h/check "after a stop the search resumes from the same place"
         (+ (length (too-few :answers)) (length (onward :answers))) 6)
(h/check "and the total cost is the same as without the stop"
         (stingy :steps) (in-one-go :steps))

### ── the budget on a search that would not finish soon ──────────────────────

(def- endless (k/search (fn [q] (k/fresh [x y] (membero x (k/llist* 1 2 y))
                                                   (k/== q x)))))
(def- a-piece (k/take-more! endless 3 2000))
(h/check "exactly as many as asked are taken from an infinite relation"
         (length (a-piece :answers)) 3)
(h/check "and it is not declared exhausted" (k/search-exhausted? endless) false)

### ── observability ──────────────────────────────────────────────────────────
# The counters are part of the interface, not debugging leftovers: with a
# complete interleaving search, "working hard" and "stuck in one call" look
# identical from outside, and only the work counters tell them apart.

(def- counted (k/search (fn [q] (membero q six))))
(k/take-more! counted 4)
(def- stats (k/search-stats counted))
(h/check "the stats know how many answers were given" (stats :answers) 4)
(h/check "and how many unifications it cost" (> (stats :unifications) 0) true)
(h/check "the stats' steps match the search counter" (stats :steps) (counted :steps))
(h/check "a healthy search has no error" (stats :error) nil)

### ── an error in a relation is neither swallowed nor fatal ──────────────────
# 🔴 The dangerous outcome here is not a crash — it is a broken relation that
# silently yields no answers and thereby looks like a true "nothing matches".
# The suite exists to make that outcome impossible.

(defn- broken-goal [x]
  (k/fresh [y] (k/== x y) (fn [state] (error "the relation is broken"))))

(def- broken (k/search (fn [q] (k/conde [(k/== q 1)] [(broken-goal q)]))))
(def- outcome (k/take-more! broken 5))

(h/check "answers obtained before the error are not lost" (outcome :answers) @[1])
(h/check "the error is returned, not swallowed" (outcome :error) "the relation is broken")
(h/check "the search is marked broken" (k/search-failed? broken) true)
(h/check "🔴 a broken search does NOT pass itself off as exhausted"
         (k/search-exhausted? broken) false)
(def- again (k/take-more! broken 5))
(h/check "taking again returns the same error, not emptiness"
         (again :error) "the relation is broken")
(h/check "and adds no answers" (length (again :answers)) 0)
(h/check "the error did not bring the process down — we got here" true true)

### ── run/run* keep working on top of the same machinery ─────────────────────

(h/check "run still answers" (k/run 2 [q] (membero q six)) @[1 2])
(h/check "run* still answers" (length (k/run* [q] (membero q six))) 6)

(h/finish)
