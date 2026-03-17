#!/usr/bin/env bash

set -euo pipefail

# This shell script runs the entire artifact.

GREEN=$'\033[0;32m'
RED=$'\033[0;31m'
RESET=$'\033[0m'

# First we check the mechanization.
echo "Checking Lean mechanization"

lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep axioms | while IFS= read -r line; do
  name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
  if echo "$line" | grep -q 'sorryAx'; then
    printf "%s  ✗ %s%s (contains sorryAx)\n" "$RED" "$name" "$RESET"
  else
    printf "%s  ✓ %s (PASS)%s\n" "$GREEN" "$name" "$RESET"
  fi
done

# Now we run the murphi scripts.
echo "Checking Murphi axioms"

(
  cd /home/anqi/compositional-protocol-proof/model-check-axioms || exit 1
  # Extra args passed to this script are forwarded to run_axioms.py.
  if nix-shell python-murphi-script.nix --run "python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html $*"; then
    printf "%s  ✓ PASS%s\n" "$GREEN" "$RESET"
  else
    printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
  fi
)
