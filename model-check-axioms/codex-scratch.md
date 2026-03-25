
  Usage

  ./scripts/run_axioms.py --m 5000

  Common options

  - --mu-path ~/cmurphi5.5.0/src/mu
  - --include-path ~/cmurphi5.5.0/include
  - --axioms-file axioms-to-run.txt
  - --out-dir runs
  - --m 5000
  - --dry-run

  Selection file format (axioms-to-run.txt)

  - CXL-1 or RCCO-4 (all variants of that axiom number)
  - CXL-Axiom15
  - Full filename like CXL-Axiom1-ordered-directory-events.m
  - Substring like ordered-directory-events

  Next steps

  1. Update axioms-to-run.txt to the exact set you want.
  2. Run ./scripts/run_axioms.py --m 8000 (or your preferred memory)
