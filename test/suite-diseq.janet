# Disequality (=/=).
#
# The point of these tests is not that `=/=` rejects what is already equal —
# that much a plain check would do. The point is that a prohibition SURVIVES
# the moment it was stated and fires later, when some other goal finally makes
# the forbidden binding. A test suite that only checks the immediate case
# would pass on an implementation that forgets everything.

(import ../kanja :as k)
(import ./harness :as h)

(h/start-suite "diseq")

(def- _0 (symbol "_.0"))
(def- _1 (symbol "_.1"))

### ── decided on the spot ────────────────────────────────────────────────────
(h/check "already distinct — nothing to forbid, the goal passes"
         (k/run* [q] (k/=/= 1 2) (k/== q :ok)) @[:ok])
(h/check "already equal — the state is illegal"
         (k/run* [q] (k/=/= 1 1) (k/== q :ok)) @[])
(h/check "an equality after a prohibition is cut off"
         (k/run* [q] (k/=/= q 5) (k/== q 5)) @[])
(h/check "a prohibition after an equality is cut off"
         (k/run* [q] (k/== q 5) (k/=/= q 5)) @[])
(h/check "a consistent value passes"
         (k/run* [q] (k/=/= q 5) (k/== q 6)) @[6])

### ── the prohibition outlives the moment ────────────────────────────────────
# Neither x nor y is decided when the prohibition is stated. It must wait.
(h/check "a prohibition fires LATER, when both variables get values"
         (k/run* [q] (k/fresh [x y]
                       (k/=/= [x y] [1 2])
                       (k/== x 1) (k/== y 2)
                       (k/== q [x y])))
         @[])
(h/check "the same prohibition does not interfere when there is no match"
         (k/run* [q] (k/fresh [x y]
                       (k/=/= [x y] [1 2])
                       (k/== x 1) (k/== y 3)
                       (k/== q [x y])))
         @[[1 3]])
(h/check "goal order does not change the outcome (prohibition stated last)"
         (k/run* [q] (k/fresh [x y]
                       (k/== x 1) (k/== y 2)
                       (k/=/= [x y] [1 2])
                       (k/== q [x y])))
         @[])

### ── prohibition is a set, not a pair ───────────────────────────────────────
# =/= on compound terms forbids the CONJUNCTION: x=1 AND y=2 together.
# Forbidding each separately would be a different, stronger statement.
(h/check "the conjunction is forbidden, not each part separately"
         (k/run* [q] (k/fresh [x y]
                       (k/=/= [x y] [1 2])
                       (k/== x 1)
                       (k/== q :gotHere)))
         @[:gotHere])

### ── discharged prohibitions ────────────────────────────────────────────────
(h/check "an unsatisfiable prohibition is discharged and does not interfere"
         (k/run* [q] (k/fresh [x] (k/=/= [x 1] [x 2]) (k/== q x) (k/== x :whatever)))
         @[:whatever])

### ── prohibitions are shown in the answer ───────────────────────────────────
# Without this the answer would overstate what it knows: bare `_.0` claims
# "anything", while the truth is "anything except 5".
(h/check "a surviving prohibition is visible in the answer"
         (k/run* [q] (k/=/= q 5))
         @[[_0 ~(=/= ((,_0 5)))]])
(h/check "two prohibitions are both shown"
         (k/run* [q] (k/=/= q 5) (k/=/= q 6))
         @[[_0 ~(=/= ((,_0 5)) ((,_0 6)))]])
(h/check "a prohibition about an inner variable, unseen in the answer, is not shown"
         (k/run* [q] (k/fresh [x] (k/=/= x 5) (k/== q :value)))
         @[:value])

# Found by Lor's audit on 01.08: `in` on a missing key silently yields nil, and
# the answer printed `(=/= (_.0 nil))`. The printing defect is the surface;
# underneath is a logical one: that prohibition restricts nothing observable.
(h/check "a prohibition between a visible and an INVISIBLE variable restricts nothing"
         (k/run* [q] (k/fresh [x] (k/=/= q x)))
         @[_0])
# Stricter than Lor's sketch: FILTERING OUT the pair with an invisible side is
# not enough — the prohibition must be dropped WHOLE. A prohibition is a
# conjunction; with x free there is always a value of x breaking it, so q is
# unconstrained. Keeping the visible half would print «q ≠ 5», simply untrue.
(h/check "a prohibition with an invisible side is dropped WHOLE, not halved"
         (k/run* [q] (k/fresh [x] (k/=/= [q x] [5 3])))
         @[_0])
(h/check "and q really can be five"
         (k/run* [q] (k/fresh [x] (k/=/= [q x] [5 3]) (k/== q 5)))
         @[5])
(h/check "a fully visible prohibition is still shown (control)"
         (k/run* [q] (k/=/= q 5))
         @[[_0 ~(=/= ((,_0 5)))]])

### ── branching ──────────────────────────────────────────────────────────────
(h/check "a prohibition acts inside each branch separately"
         (k/run* [q] (k/=/= q 1) (k/conde [(k/== q 1)] [(k/== q 2)] [(k/== q 3)]))
         @[2 3])

(h/finish)
