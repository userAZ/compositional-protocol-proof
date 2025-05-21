import CompositionalProtocolProof.Requests

abbrev ProtocolInterface := List Request

abbrev WeakWrite := {r : Request // r.rw = .w ∧ r.consistency = .Weak}
abbrev CoherentWeakWrite := {r : Request // r.rw = .w ∧ r.coherent = true ∧ r.consistency = .Weak}
abbrev CoherentReleaseWrite := {r : Request // r.rw = .w ∧ r.coherent = true ∧ r.consistency = .Rel}

-- def LazyOrEagerCoherentReleaseWrite : ProtocolInterface

-- def ProtocolInterfaceFamily
