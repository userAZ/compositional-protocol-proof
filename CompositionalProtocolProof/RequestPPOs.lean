import CompositionalProtocolProof.Requests

def ValidRequest.isPPOPair (v₁ v₂ : ValidRequest) : Prop := match v₁, v₂ with
  | ⟨⟨_,true,.SC⟩,_⟩, ⟨⟨_,true,.SC⟩,_⟩ => True -- All SC requests are ordered
  | ⟨⟨_,false,.Weak⟩,_⟩, ⟨⟨.w,false,.Rel⟩,_⟩ => True -- Weak requests are ordered before a Non-Coherent Release
  | ⟨⟨_,false,.Weak⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => True -- Weak requests are ordered before a Coherent Release
  | ⟨⟨.w,true,.Weak⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => True -- a Coherent Weak Write is ordered before a Coherent Release
  | ⟨⟨.w,false,.Rel⟩,_⟩, ⟨⟨.r,false,.Acq⟩,_⟩ => True -- a Non-Coherent Release is ordered before an Acquire
  | ⟨⟨.w,true,.Rel⟩,_⟩, ⟨⟨.r,false,.Acq⟩,_⟩ => True -- a Coherent Release is ordered before an Acquire
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,false,.Rel⟩,_⟩ => True -- an Acquire is ordered before a Non-Coherent Release
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => True -- an Acquire is ordered before a Coherent Release
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨_,false,.Weak⟩,_⟩ => True -- an Acquire is ordered before a weak non-coherent request
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,true,.Weak⟩,_⟩ => True -- an Acquire is ordered before a weak non-coherent request
  | _, _ => False -- Ordering is not required in all other cases
