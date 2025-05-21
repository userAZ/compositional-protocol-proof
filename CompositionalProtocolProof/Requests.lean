import CompositionalProtocolProof.Common

inductive ReadWrite
| r : ReadWrite
| w : ReadWrite

-- abbrev Coherent, from Common.

inductive Consistency
| SC : Consistency
| Rel : Consistency
| Acq : Consistency
| Weak : Consistency

structure Request where
  rw          : ReadWrite
  coherent    : Coherent
  consistency : Consistency
