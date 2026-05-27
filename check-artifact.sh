#!/usr/bin/env bash

set -euo pipefail

# This shell script runs the entire artifact.

GREEN=$'\033[0;32m'
RED=$'\033[0;31m'
RESET=$'\033[0m'

tmp_files=()
cleanup() {
  rm -f "${tmp_files[@]}"
}
trap cleanup EXIT

check_lean_theorem() {
  local message="$1"
  local import_name="$2"
  local theorem_name="$3"
  local check_file lean_output axiom_lines failed

  echo "$message"

  check_file=$(mktemp --suffix=.lean)
  tmp_files+=("$check_file")
  printf "import %s\n#print axioms %s\n" "$import_name" "$theorem_name" > "$check_file"

  if ! lean_output=$(lake env lean "$check_file" 2>&1); then
    printf "%s\n" "$lean_output"
    exit 1
  fi

  axiom_lines=$(printf "%s\n" "$lean_output" | grep 'depends on axioms' || true)
  if [ -z "$axiom_lines" ]; then
    printf "%s  ✗ %s%s (no axiom report found)\n" "$RED" "$theorem_name" "$RESET"
    printf "%s\n" "$lean_output"
    exit 1
  fi

  failed=0
  while IFS= read -r line; do
    name=$(echo "$line" | sed "s/^'\\([^']*\\)'.*/\\1/")
    if echo "$line" | grep -q 'sorryAx'; then
      printf "%s  ✗ %s%s (contains sorryAx)\n" "$RED" "$name" "$RESET"
      failed=1
    else
      printf "%s  ✓ %s (PASS)%s\n" "$GREEN" "$name" "$RESET"
    fi
  done < <(printf "%s\n" "$axiom_lines")

  if [ "$failed" -ne 0 ]; then
    exit 1
  fi
}

# First we check the mechanization.
check_lean_theorem \
  "Checking Lean mechanization: Cluster PPO (Preserved Program Orderings) are enforced." \
  "CompositionalProtocolProof.CompositionalMCM" \
  "CompoundProtocol.enforce_compound_consistency"

check_lean_theorem \
  "Checking Lean mechanization: Load Value Axiom (Reads read from Latest Write) is enforced." \
  "CMCM.RfTheorem" \
  "CMCM.rf_holds"

check_lean_theorem \
  "Checking Lean mechanization: Compound Memory Consistency Model (CMCM) acyclicity is enforced." \
  "CMCM.Herd.Proof" \
  "Herd.cmcm"

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
  if [ -x "/opt/venv/bin/python3" ]; then
    if /opt/venv/bin/python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html "${murphi_args[@]}"; then
      printf "%s  ✓ PASS%s\n" "$GREEN" "$RESET"
    else
      printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
      exit 1
    fi
  elif command -v nix-shell >/dev/null 2>&1; then
    printf -v murphi_args_esc "%q " "${murphi_args[@]}"
    if nix-shell python-murphi-script.nix --run "python3 scripts/run_axioms.py --clean --axioms-file axioms-to-run.txt --table-html runs/results.html ${murphi_args_esc}"; then
      printf "%s  ✓ PASS%s\n" "$GREEN" "$RESET"
    else
      printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
      exit 1
    fi
  else
    printf "%s  ✗ FAIL%s\n" "$RED" "$RESET"
    printf "No Python environment found. Install deps in /opt/venv or use nix-shell.\n"
    exit 1
  fi
)
