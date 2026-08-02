# Minimal test harness.
#
# The verdict is the exit code, not the printed text: a test run that fails
# must be impossible to mistake for one that passed, by a human or by CI.
# `self-check` exists so the harness itself is proven able to fail.

(var- checks 0)
(var- failures @[])
(var- suite-name "")

(defn start-suite [name]
  (set suite-name name)
  (set checks 0)
  (set failures @[])
  (printf "── %s" name))

(defn check
  "Assert that `got` equals `expect`. `what` names what is being checked."
  [what got expect]
  (++ checks)
  (unless (deep= got expect)
    (array/push failures
                (string/format "%s\n      got:      %j\n      expected: %j" what got expect))))

(defn check-true [what got]
  (++ checks)
  (unless got (array/push failures (string/format "%s — expected true, got %j" what got))))

(defn end-suite []
  (if (empty? failures)
    (do (printf "   ✓ %s: %d checks" suite-name checks) 0)
    (do (printf "   ✗ %s: %d failures of %d" suite-name (length failures) checks)
        (each f failures (printf "     · %s" f))
        1)))

(defn finish
  "Exit with the verdict of the suite."
  []
  (os/exit (end-suite)))
