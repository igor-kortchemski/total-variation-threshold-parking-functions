#!/usr/bin/env bash
# Runs a command while holding the project-wide compile lock, so that at most one Lean
# compilation runs at a time (AGENTS.md), even when several agents work in parallel.
#
# Usage, from the project root: scripts/compile-lock.sh lake build Parking.Foo
#                               scripts/compile-lock.sh lake env lean .scratch/Probe.lean
#
# The lock is the directory .scratch/compile.lock, created atomically by mkdir and
# removed when the command exits. Never infer a stale lock from `kill -0`: sandbox
# boundaries can deny process inspection even when the holder is still running.
# After an abnormal termination, inspect the recorded PID before manual recovery.
set -u
root="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$root/.scratch"
lock="$root/.scratch/compile.lock"
announced=""
while ! mkdir "$lock" 2>/dev/null; do
  holder=$(cat "$lock/pid" 2>/dev/null || true)
  if [ -z "$announced" ]; then
    echo "[compile-lock] waiting for the compile lock (held by ${holder:-?})" >&2
    announced=1
  fi
  sleep 2
done
echo $$ > "$lock/pid"
trap 'rm -rf "$lock"' EXIT INT TERM
"$@"
