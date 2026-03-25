#!/usr/bin/env bash

set -euo pipefail

# This shell script runs the entire artifact.

GREEN=$'\033[0;32m'
RED=$'\033[0;31m'
RESET=$'\033[0m'

# First we check the mechanization.
echo "Checking Lean mechanization: Cluster PPO (Preserved Program Orderings) are enforced."

if ! lean_output=$(lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1); then
  printf "%s\n" "$lean_output"
  exit 1
fi

while IFS= read -r line; do
  name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
  if echo "$line" | grep -q 'sorryAx'; then
    printf "%s  ✗ %s%s (contains sorryAx)\n" "$RED" "$name" "$RESET"
  else
    printf "%s  ✓ %s (PASS)%s\n" "$GREEN" "$name" "$RESET"
  fi
done < <(printf "%s\n" "$lean_output" | grep axioms || true)

echo "Checking Lean mechanization: Load Value Axiom (Reads read from Latest Write) is enforced."

if ! lean_output=$(lake lean CMCM/RfTheorem.lean 2>&1); then
  printf "%s\n" "$lean_output"
  exit 1
fi

axiom_lines=$(printf "%s\n" "$lean_output" | grep axioms || true)
if [ -z "$axiom_lines" ]; then
  printf "%s  ✓ %s (PASS)%s\n" "$GREEN" "CMCM/RfTheorem.lean" "$RESET"
else
while IFS= read -r line; do
  name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
  if echo "$line" | grep -q 'sorryAx'; then
    printf "%s  ✗ %s%s (contains sorryAx)\n" "$RED" "$name" "$RESET"
  else
    printf "%s  ✓ %s (PASS)%s\n" "$GREEN" "$name" "$RESET"
  fi
done < <(printf "%s\n" "$axiom_lines")
fi

# Now we run the murphi scripts.
echo "Checking Murphi axioms from the Paper's Case Studies."

(
  cd model-check-axioms || exit 1
  # Extra args passed to this script are forwarded to run_axioms.py.
  if [ "$#" -eq 0 ]; then
    murphi_args=(--threads 1 --memory-per-thread 50)
  else
    murphi_args=("$@")
  fi
  printf -v murphi_args_esc "%q " "${murphi_args[@]}"
  if [ -x "/opt/venv/bin/python3" ]; then
    if /opt/venv/bin/python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html ${murphi_args_esc}; then
      printf "%s  ✓ PASS%s\n" "$GREEN" "$RESET"
    else
      printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
    fi
  elif command -v nix-shell >/dev/null 2>&1; then
    if nix-shell python-murphi-script.nix --run "python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html ${murphi_args_esc}"; then
      printf "%s  ✓ PASS%s\n" "$GREEN" "$RESET"
    else
      printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
    fi
  else
    printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
    printf "No Python environment found. Install deps in /opt/venv or use nix-shell.\n"
    exit 1
  fi
)
