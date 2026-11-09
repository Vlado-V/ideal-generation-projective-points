module

public import IdealGeneration.CubicSupportedRationalChart
public import IdealGeneration.CubicSupportedRestriction
public import Mathlib.Logic.Equiv.Set

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Old and new primitive cone parameters for the shared-open argument. -/

noncomputable section
namespace IdealGeneration.CubicSupported.RationalChart

open CubicRationalFormula

private def prefixEdge {n N : ℕ} (h : n ≤ N) : Edge n ↪ Edge N where
  toFun e := ⟨((Fin.castLEEmb h) e.val.1, (Fin.castLEEmb h) e.val.2), e.property⟩
  inj' a b hab := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Fin.castLEEmb h).injective (congrArg (fun e => e.val.1) hab)
    · exact (Fin.castLEEmb h).injective (congrArg (fun e => e.val.2) hab)

/-- Primitive labels of any initial coordinate prefix. -/
def primitivePrefixIndex {n N : ℕ} (h : n ≤ N) : PrimitiveIndex n ↪ PrimitiveIndex N where
  toFun
    | .vertexSlope i d => .vertexSlope ((Fin.castLEEmb h) i) d
    | .vertexHeight i d => .vertexHeight ((Fin.castLEEmb h) i) d
    | .edgeSlope e d => .edgeSlope (prefixEdge h e) d
    | .edgeHeight e d => .edgeHeight (prefixEdge h e) d
    | .edgeLambda e => .edgeLambda (prefixEdge h e)
  inj' := by
    intro i j he
    cases i <;> cases j <;> simp_all

/-- The primitive parameters of the old graph inside the enlarged graph. -/
def oldPrimitiveIndex (m : ℕ) : PrimitiveIndex m ↪ PrimitiveIndex (m + 2) :=
  primitivePrefixIndex (Nat.le_add_right m 2)

/-- Complementary primitive labels along a prefix embedding. -/
abbrev NewPrimitiveAlong {n N : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex N) :=
  {i : PrimitiveIndex N // i ∉ Set.range e}

/-- Parameters of the two new vertices and the edges incident to them. -/
abbrev NewPrimitiveIndex (m : ℕ) := NewPrimitiveAlong (oldPrimitiveIndex m)

open Classical in
/-- The new coordinates are listed first for the iterated polynomial ring of B.6. -/
def primitiveSplitEquiv {n N : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex N) :
    NewPrimitiveAlong e ⊕ PrimitiveIndex n ≃ PrimitiveIndex N :=
  (Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range e)))

@[simp] theorem primitiveSplitEquiv_inl {n N : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex N)
    (i : NewPrimitiveAlong e) : primitiveSplitEquiv e (.inl i) = i.val := rfl

@[simp] theorem primitiveSplitEquiv_inr {n N : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex N)
    (i : PrimitiveIndex n) : primitiveSplitEquiv e (.inr i) = e i := rfl

/-- The primitive parameter split for one addition of two variables. -/
def primitiveOldNewEquiv (m : ℕ) : NewPrimitiveIndex m ⊕ PrimitiveIndex m ≃ PrimitiveIndex (m + 2) :=
  primitiveSplitEquiv (oldPrimitiveIndex m)

@[simp] theorem primitiveOldNewEquiv_inl (m : ℕ) (i : NewPrimitiveIndex m) :
    primitiveOldNewEquiv m (.inl i) = i.val := rfl

@[simp] theorem primitiveOldNewEquiv_inr (m : ℕ) (i : PrimitiveIndex m) :
    primitiveOldNewEquiv m (.inr i) = oldPrimitiveIndex m i := rfl

variable {K : Type*} [Field K] {m : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)}

/-- Actual cone compatibility agrees on the old primitive assignment. -/
theorem primitiveValue_oldPrimitiveIndex (h : Compatible P Q) (i : PrimitiveIndex m) :
    primitiveValue Q (oldPrimitiveIndex m i) = primitiveValue P i := by
  cases i with
  | vertexSlope i d => exact h.vertexSlope_eq i d
  | vertexHeight i d => exact h.vertexHeight_eq i d
  | edgeSlope e d => exact h.edgeSlope_eq e d
  | edgeHeight e d => exact h.edgeHeight_eq e d
  | edgeLambda e => exact h.edgeLambda_eq e

/-- The split assignment specializes old coefficients to the old cone data. -/
theorem primitiveValue_split (h : Compatible P Q) (i : NewPrimitiveIndex m ⊕ PrimitiveIndex m) :
    primitiveValue Q (primitiveOldNewEquiv m i) =
      Sum.elim (fun j : NewPrimitiveIndex m => primitiveValue Q j.val) (primitiveValue P) i := by
  rcases i with i | i
  · rfl
  · exact primitiveValue_oldPrimitiveIndex h i

/-- The variables for the rational chart in the split coordinate space. -/
def splitPrimitiveVariable (m : ℕ) (i : PrimitiveIndex (m + 2)) :
    Formula (NewPrimitiveIndex m ⊕ PrimitiveIndex m) :=
  .var ((primitiveOldNewEquiv m).symm i)

/-- The split variables still match every actual primitive cone parameter. -/
theorem splitPrimitiveVariable_matches (h : Compatible P Q) (i : PrimitiveIndex (m + 2)) :
    Formula.Matches (Sum.elim (fun j : NewPrimitiveIndex m => primitiveValue Q j.val) (primitiveValue P))
      (splitPrimitiveVariable m i) (primitiveValue Q i) := by
  have he := primitiveValue_split h ((primitiveOldNewEquiv m).symm i)
  rw [Equiv.apply_symm_apply] at he
  rw [he]
  exact Formula.Matches.var _ _

end IdealGeneration.CubicSupported.RationalChart
