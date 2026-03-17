#!/usr/bin/env sh

# This shell script runs the entire artifact

# First we check the mechanization
echo "Checking Lean mechanization"

GREEN='\033[0;32m'
RED='\033[0;31m'
BOLD='\033[1m'
RESET='\033[0m'

lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep axioms | while IFS= read -r line; do
  name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
  if echo "$line" | grep -q 'sorryAx'; then
    printf "${RED}  ✗ %s${RESET} (contains sorryAx)\n" "$name"
  else
    printf "${GREEN}  ✓ %s (PASS)${RESET}\n" "$name"
  fi
done


#Now we run the murphi scripts
echo "Checking Murphi axioms"
(
  cd /home/anqi/compositional-protocol-proof/model-check-axioms || exit 1
  # Extra args passed to this script are forwarded to run_axioms.py.
  MURPHI_ARGS="$*"
  if nix-shell python-murphi-script.nix --run "python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html ${MURPHI_ARGS}"; then
    printf "${GREEN}  ✓ PASS${RESET}\n"
  else
    printf "${RED}  ✗ FAIL${RESET}\n"
  fi
)
