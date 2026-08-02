# What generating the quine costs: stream forcings and unifications.
#
# 🔴 This probe did not run at all (`unknown symbol k/WALKS`): it called a
# counter of substitution walks that the engine does not have — the leftover of
# a measurement taken during the move to tuples. A dead path in checking code is
# worse than one in working code: it stays silent until the day someone relies
# on it. Fixed by ArkH 02.08.2026 to match the facts — no walk counter is kept,
# deliberately: `walk` is the hottest operation in the library, and it is to be
# measured with a profiler, not with an increment on every step.
#
# Canon baseline (faster-minikanren under Guile, quine + timing probe):
#   0.022-0.036 s, 13 117 unifications.
# We do an order of magnitude fewer unifications at a higher cost each: the
# bottleneck is not the walk but the price of one unification (writing into the
# substitution is linear in its size — see the honest debts in ZAMYSEL.md).

(import ../kanja :as k)
(import ../examples/interpreter :as i)

(set k/PULLS 0)
(set k/UNIFS 0)
(def t0 (os/clock))
(try (k/run 1 [q] (i/evalo q q)) ([e] (print "aborted: " e)))
(printf "quine in %.3f s: forcings %d, unifications %d"
        (- (os/clock) t0) k/PULLS k/UNIFS)
