module

public import IdealGeneration.CubicPrimitiveSplit
public import IdealGeneration.CubicPairC3Graph
public import IdealGeneration.CubicMixedLocality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Primitive labels of the seven-coordinate C.3 block. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicMixedLocality

/-- Only old pair centers and old edges incident to a center are retained. -/
def c3OldRelevant : PrimitiveIndex 7 → Prop
  | .vertexSlope i _ | .vertexHeight i _ => 3 ≤ i.val ∧ i.val < 5
  | .edgeSlope e _ | .edgeHeight e _ | .edgeLambda e => 3 ≤ e.val.2.val ∧ e.val.2.val < 5

/-- New parameters are at the new vertices or on edges meeting them. -/
def c3NewRelevant : PrimitiveIndex 7 → Prop
  | .vertexSlope i _ | .vertexHeight i _ => 5 ≤ i.val
  | .edgeSlope e _ | .edgeHeight e _ | .edgeLambda e => 5 ≤ e.val.2.val

abbrev C3OldIndex := {i : PrimitiveIndex 7 // c3OldRelevant i}
abbrev C3NewIndex := {i : PrimitiveIndex 7 // c3NewRelevant i} ⊕ (Fin 13 × Fin 7)

/-- Transfer primitive labels along an increasing coordinate embedding. -/
def c3PrimitiveImage {n m : ℕ} (e : Fin n ↪ Fin m) (he : StrictMono e) : PrimitiveIndex n → PrimitiveIndex m
  | .vertexSlope i d => .vertexSlope (e i) d
  | .vertexHeight i d => .vertexHeight (e i) d
  | .edgeSlope i d => .edgeSlope (edgeImage e he i) d
  | .edgeHeight i d => .edgeHeight (edgeImage e he i) d
  | .edgeLambda i => .edgeLambda (edgeImage e he i)

private theorem c3PrimitiveImage_congr {n m : ℕ} {e f : Fin n ↪ Fin m}
    {he : StrictMono e} {hf : StrictMono f} (h : ∀ i, e i = f i) (i : PrimitiveIndex n) :
    c3PrimitiveImage e he i = c3PrimitiveImage f hf i := by
  have hef : e = f := Function.Embedding.ext h
  subst f
  rfl

private theorem c3PrimitiveImage_comp {n m N : ℕ} (e : Fin n ↪ Fin m) (he : StrictMono e)
    (f : Fin m ↪ Fin N) (hf : StrictMono f) (i : PrimitiveIndex n) :
    c3PrimitiveImage f hf (c3PrimitiveImage e he i) = c3PrimitiveImage (e.trans f) (hf.comp he) i := by
  cases i <;> rfl

private theorem c3PrimitiveImage_oldPrimitiveIndex (m : ℕ) (i : PrimitiveIndex m) :
    c3PrimitiveImage (Fin.castAddEmb 2) (fun _ _ h => h) i = oldPrimitiveIndex m i := by
  cases i <;> rfl

private def c3OldLocalEdge (e : Edge 7) (h : e.val.2.val < 5) : Edge 5 :=
  ⟨(⟨e.val.1.val, lt_trans e.property h⟩, ⟨e.val.2.val, h⟩), e.property⟩

/-- Read a retained label in the five old local coordinates. -/
def c3OldLocalIndex : C3OldIndex → PrimitiveIndex 5
  | ⟨.vertexSlope i d, h⟩ => .vertexSlope ⟨i.val, h.2⟩ d
  | ⟨.vertexHeight i d, h⟩ => .vertexHeight ⟨i.val, h.2⟩ d
  | ⟨.edgeSlope e d, h⟩ => .edgeSlope (c3OldLocalEdge e h.2) d
  | ⟨.edgeHeight e d, h⟩ => .edgeHeight (c3OldLocalEdge e h.2) d
  | ⟨.edgeLambda e, h⟩ => .edgeLambda (c3OldLocalEdge e h.2)

@[simp] theorem oldPrimitiveIndex_c3OldLocalIndex (i : C3OldIndex) :
    oldPrimitiveIndex 5 (c3OldLocalIndex i) = i.val := by
  rcases i with ⟨i, hi⟩
  cases i <;> rfl

variable {k : ℕ}

/-- A retained primitive index in the old ambient cone. -/
def c3OldAmbientIndex (j : Fin k) (i : C3OldIndex) : PrimitiveIndex (10 + 2 * k) :=
  c3PrimitiveImage (pairC3TraceEmbedding j) (pairC3Trace_strictMono j) (c3OldLocalIndex i)

/-- An arbitrary local primitive index in the enlarged ambient cone. -/
def c3AmbientIndex (j : Fin k) : PrimitiveIndex 7 → PrimitiveIndex ((10 + 2 * k) + 2) :=
  c3PrimitiveImage (pairC3AmbientEmbedding j) (pairC3Ambient_strictMono j)

/-- Reading a retained primitive in the enlarged cone uses its old ambient label. -/
theorem c3AmbientIndex_old (j : Fin k) (i : C3OldIndex) :
    c3AmbientIndex j i.val = oldPrimitiveIndex (10 + 2 * k) (c3OldAmbientIndex j i) := by
  rw [← oldPrimitiveIndex_c3OldLocalIndex i, c3AmbientIndex, c3OldAmbientIndex,
    ← c3PrimitiveImage_oldPrimitiveIndex 5, ← c3PrimitiveImage_oldPrimitiveIndex (10 + 2 * k)]
  refine (c3PrimitiveImage_comp (Fin.castAddEmb 2) (fun _ _ h => h) (pairC3AmbientEmbedding j)
    (pairC3Ambient_strictMono j) (c3OldLocalIndex i)).trans ?_
  refine (c3PrimitiveImage_congr (f := (pairC3TraceEmbedding j).trans (Fin.castAddEmb 2))
    (hf := fun _ _ h => pairC3Trace_strictMono j h) (pairC3Ambient_old j) (c3OldLocalIndex i)).trans ?_
  exact (c3PrimitiveImage_comp (pairC3TraceEmbedding j) (pairC3Trace_strictMono j)
    (Fin.castAddEmb 2) (fun _ _ h => h) (c3OldLocalIndex i)).symm

/-- The same pair has the same retained labels after adding a later pair. -/
theorem c3OldAmbientIndex_castSucc (j : Fin k) (i : C3OldIndex) :
    c3OldAmbientIndex j.castSucc i = oldPrimitiveIndex (10 + 2 * k) (c3OldAmbientIndex j i) := by
  rw [c3OldAmbientIndex, c3OldAmbientIndex, ← c3PrimitiveImage_oldPrimitiveIndex]
  refine (c3PrimitiveImage_congr (f := (pairC3TraceEmbedding j).trans (Fin.castAddEmb 2))
    (hf := fun _ _ h => pairC3Trace_strictMono j h) ?_ (c3OldLocalIndex i)).trans ?_
  · intro t
    fin_cases t <;> rfl
  · exact (c3PrimitiveImage_comp (pairC3TraceEmbedding j) (pairC3Trace_strictMono j)
      (Fin.castAddEmb 2) (fun _ _ h => h) (c3OldLocalIndex i)).symm

variable {K : Type*} [Field K]

/-- Retained primitive values of a pair, read in its fixed local order. -/
def c3OldValue (P : Parameters K (10 + 2 * k)) (j : Fin k) (i : C3OldIndex) : K :=
  primitiveValue P (c3OldAmbientIndex j i)

/-- The retained local values are unchanged by an actual compatible extension. -/
theorem c3OldValue_compatible {P : Parameters K (10 + 2 * k)}
    {Q : Parameters K ((10 + 2 * k) + 2)} (h : Compatible P Q) (j : Fin k) :
    c3OldValue Q j.castSucc = c3OldValue P j := by
  funext i
  rw [c3OldValue, c3OldAmbientIndex_castSucc, primitiveValue_oldPrimitiveIndex h]
  rfl

end IdealGeneration.CubicSupported.B5
