#!/usr/bin/env bash
# REPL banner. One line between two rules. Nothing else.
#
# How it got here, four edits in a row:
#   1. No poetry — a line that can be removed without losing a fact is removed.
#   2. No "(help) to start" — there was no help yet, and nothing unbuilt is promised.
#   3. No version — it goes stale on the first edit; the package manager prints versions.
#   4. No frame, no shadows — a rule above, a rule below, monochrome.
#
# Why this shape belongs here: the Janet ecosystem has no splash screens at all. Janet
# itself prints one line ("Janet 1.41.3 linux/x64/gcc - '(doc)' for help"), and libraries
# print nothing — they get imported. A banner only appears when a REPL is started, and it
# should be quieter than the code it introduces.
#
# 🔴 LOCALE. Under the C locale bash counts ${#txt} in BYTES. Nothing here measures width —
# the rules are fixed strings — but the locale is set anyway: the multi-byte "─" has to come
# out as a character rather than as rubbish in someone else's terminal.
# Check any edit with: env -i LC_ALL=C bash banner.sh
export LC_ALL=C.UTF-8
locale -a 2>/dev/null | grep -qi "^C.utf8" || export LC_ALL=en_US.UTF-8
set -u

R='\033[0m'; B='\033[1m'
RULE='\033[38;5;242m'     # rules — quieter than the text
SUB='\033[38;5;250m'      # the subtitle

NAME="${KANJA_NAME:-kanja}"
DESC="${KANJA_DESC:-miniKanren for Janet}"
LINE="──────────────────────────────"

printf "\n  ${RULE}%s${R}\n" "$LINE"
printf "  ${B}%s${R}  ${SUB}%s${R}\n" "$NAME" "$DESC"
printf "  ${RULE}%s${R}\n\n" "$LINE"
