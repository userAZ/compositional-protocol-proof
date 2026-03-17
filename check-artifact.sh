#!/usr/bin/env sh

# This shell script runs the entire artifact

# First we check the mechanization
echo "Checking Lean mechanization"

GREEN='\033[0;32m'
RED='\033[0;31m'
BOLD='\033[1m'
RESET='\033[0m'

pass=0
fail=0

lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep axioms | while IFS= read -r line; do
  name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
  if echo "$line" | grep -q 'sorryAx'; then
    printf "${RED}  ✗ %s${RESET} (contains sorryAx)\n" "$name"
    fail=$((fail + 1))
  else
    printf "${GREEN}  ✓ %s${RESET}\n" "$name"
    pass=$((pass + 1))
  fi
done

# Re-scan to get counts (since the while-pipe runs in a subshell)
total=$(lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep -c axioms)
sorry_count=$(lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep axioms | grep -c sorryAx)
ok_count=$((total - sorry_count))

echo ""
if [ "$sorry_count" -eq 0 ]; then
  printf "${GREEN}${BOLD}All %d theorem(s) are sorry-free!${RESET}\n" "$total"
else
  printf "${RED}${BOLD}%d/%d theorem(s) contain sorryAx${RESET}\n" "$sorry_count" "$total"
fi

#Now we run the murphi scripts
echo "TODO: add murphi scripts here!"
