module

public import IdealGeneration.CubicPairC3Indices

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Embedding the new local C.3 variables into the new ambient cone labels. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicMixedLocality

/-- The local primitive variables at the two new coordinates or edges meeting them. -/
abbrev C3NewPrimitiveIndex := {i : PrimitiveIndex 7 // c3NewRelevant i}

/-- A coordinate embedding transfers distinct primitive labels to distinct labels. -/
theorem c3PrimitiveImage_injective {n m : ℕ} (e : Fin n ↪ Fin m) (he : StrictMono e) :
    Function.Injective (c3PrimitiveImage e he) := by
  have hedge : Function.Injective (edgeImage e he) := by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (e.injective (congrArg (fun x => x.val.1) h))
      (e.injective (congrArg (fun x => x.val.2) h))
  intro a b h
  cases a <;> cases b <;> simp_all [c3PrimitiveImage, e.injective.eq_iff, hedge.eq_iff]

/-- The largest vertex involved in a primitive parameter. -/
def primitiveLastVertex {n : ℕ} : PrimitiveIndex n → ℕ
  | .vertexSlope i _ | .vertexHeight i _ => i.val
  | .edgeSlope e _ | .edgeHeight e _ | .edgeLambda e => e.val.2.val

private theorem primitiveLastVertex_lt {n : ℕ} (i : PrimitiveIndex n) :
    primitiveLastVertex i < n := by
  cases i with
  | vertexSlope i _ => exact i.isLt
  | vertexHeight i _ => exact i.isLt
  | edgeSlope e _ => exact e.val.2.isLt
  | edgeHeight e _ => exact e.val.2.isLt
  | edgeLambda e => exact e.val.2.isLt

private theorem primitiveLastVertex_old (n : ℕ) (i : PrimitiveIndex n) :
    primitiveLastVertex (oldPrimitiveIndex n i) = primitiveLastVertex i := by
  cases i <;> rfl

private theorem pairC3Ambient_ge_new {k : ℕ} (j : Fin k) (i : Fin 7) (hi : 5 ≤ i.val) :
    10 + 2 * k ≤ (pairC3Ambient j i).val := by
  have hi' := i.isLt
  let b : Fin 2 := ⟨i.val - 5, by omega⟩
  have hb : Fin.natAdd 5 b = i := Fin.ext (by
    change 5 + (i.val - 5) = i.val
    omega)
  rw [← hb, pairC3Ambient_new]
  exact Nat.le_add_right _ _

private theorem primitiveLastVertex_c3AmbientIndex_ge_new {k : ℕ}
    (j : Fin k) (i : PrimitiveIndex 7) (hi : c3NewRelevant i) :
    10 + 2 * k ≤ primitiveLastVertex (c3AmbientIndex j i) := by
  cases i with
  | vertexSlope i _ => exact pairC3Ambient_ge_new j i hi
  | vertexHeight i _ => exact pairC3Ambient_ge_new j i hi
  | edgeSlope e _ => exact pairC3Ambient_ge_new j e.val.2 hi
  | edgeHeight e _ => exact pairC3Ambient_ge_new j e.val.2 hi
  | edgeLambda e => exact pairC3Ambient_ge_new j e.val.2 hi

/-- A primitive reaching a new vertex cannot be in the image of the old cone. -/
theorem not_mem_oldPrimitiveIndex_of_lastVertex_ge {m : ℕ} (i : PrimitiveIndex (m + 2))
    (h : m ≤ primitiveLastVertex i) : i ∉ Set.range (oldPrimitiveIndex m) := by
  rintro ⟨p, rfl⟩
  rw [primitiveLastVertex_old] at h
  exact (not_lt_of_ge h) (primitiveLastVertex_lt p)

/-- A new C.3 primitive cannot be read from an old ambient label. -/
theorem c3AmbientIndex_not_mem_range_oldPrimitiveIndex {k : ℕ} (j : Fin k)
    (i : C3NewPrimitiveIndex) :
    c3AmbientIndex j i.val ∉ Set.range (oldPrimitiveIndex (10 + 2 * k)) :=
  not_mem_oldPrimitiveIndex_of_lastVertex_ge _
    (primitiveLastVertex_c3AmbientIndex_ge_new j i.val i.property)

/-- Renaming the new local C.3 primitives into the new ambient cone is injective. -/
def c3NewAmbientEmbedding {k : ℕ} (j : Fin k) :
    C3NewPrimitiveIndex ↪ NewPrimitiveIndex (10 + 2 * k) where
  toFun i := ⟨c3AmbientIndex j i.val, c3AmbientIndex_not_mem_range_oldPrimitiveIndex j i⟩
  inj' _ _ h := Subtype.ext
    (c3PrimitiveImage_injective (pairC3AmbientEmbedding j) (pairC3Ambient_strictMono j)
      (congrArg Subtype.val h))

@[simp] theorem c3NewAmbientEmbedding_val {k : ℕ} (j : Fin k) (i : C3NewPrimitiveIndex) :
    (c3NewAmbientEmbedding j i).val = c3AmbientIndex j i.val := rfl

end IdealGeneration.CubicSupported.B5
