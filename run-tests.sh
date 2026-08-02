#!/usr/bin/env bash
# The single entry point for testing. The verdict IS the exit code.
cd "$(dirname "$0")" || exit 2
rc=0
for f in test/suite-*.janet; do
  janet "$f" || rc=1
done
[ $rc -eq 0 ] && echo "── ALL GREEN ──" || echo "── FAILURES ──"
exit $rc
