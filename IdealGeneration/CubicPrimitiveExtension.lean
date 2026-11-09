module

public import IdealGeneration.CubicPrimitiveChart
public import IdealGeneration.CubicPrimitiveSplit
public import IdealGeneration.CubicParameterCompatibility
public import IdealGeneration.CubicB22Higher

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The primitive chart guard for adding two variables with fixed old cone data. -/

noncomputable section
namespace IdealGeneration.CubicSupported.RationalChart

open MvPolynomial CubicParameterCompatibility

variable {K : Type*} [Field K] {m : ℕ}
variable (P : Parameters K m)

/-- Read the new primitive coordinates of an enlarged chart. -/
def newPrimitiveValue (Q : Parameters K (m + 2)) : NewPrimitiveIndex m → K :=
  fun j => primitiveValue Q j.val

/-- Combine arbitrary new primitive values with the given old chart's primitive values. -/
def splitPrimitiveAssignment (y : NewPrimitiveIndex m → K) : PrimitiveIndex (m + 2) → K :=
  Sum.elim y (primitiveValue P) ∘ (primitiveOldNewEquiv m).symm

theorem splitPrimitiveAssignment_split (y : NewPrimitiveIndex m → K)
    (j : NewPrimitiveIndex m ⊕ PrimitiveIndex m) :
    splitPrimitiveAssignment P y (primitiveOldNewEquiv m j) = Sum.elim y (primitiveValue P) j := by
  simp only [splitPrimitiveAssignment, Function.comp_apply, Equiv.symm_apply_apply]

@[simp] theorem splitPrimitiveAssignment_old (y : NewPrimitiveIndex m → K) (i : PrimitiveIndex m) :
    splitPrimitiveAssignment P y (oldPrimitiveIndex m i) = primitiveValue P i :=
  splitPrimitiveAssignment_split P y (.inr i)

@[simp] theorem splitPrimitiveAssignment_new (y : NewPrimitiveIndex m → K) (j : NewPrimitiveIndex m) :
    splitPrimitiveAssignment P y j.val = y j :=
  splitPrimitiveAssignment_split P y (.inl j)

theorem splitPrimitiveAssignment_eq_of_compatible {Q : Parameters K (m + 2)} (h : Compatible P Q) :
    splitPrimitiveAssignment P (newPrimitiveValue Q) = primitiveValue Q := by
  funext j
  obtain ⟨i, rfl⟩ := (primitiveOldNewEquiv m).surjective j
  rw [splitPrimitiveAssignment_split]
  rcases i with i | i
  · rfl
  · exact (primitiveValue_oldPrimitiveIndex h i).symm

/-- The primitive guard in split new and old coordinates. -/
def splitPrimitiveGuard (single : Edge (m + 2) → Bool) :
    MvPolynomial (NewPrimitiveIndex m ⊕ PrimitiveIndex m) K :=
  rename (primitiveOldNewEquiv m).symm (primitiveGuard single)

/-- The primitive guard in the new coordinates after fixing the old chart. -/
def primitiveExtensionGuard (single : Edge (m + 2) → Bool) : MvPolynomial (NewPrimitiveIndex m) K :=
  specialize (primitiveValue P) (sumAlgEquiv K _ _ (splitPrimitiveGuard single))

theorem eval_primitiveExtensionGuard (single : Edge (m + 2) → Bool) (y : NewPrimitiveIndex m → K) :
    eval y (primitiveExtensionGuard P single) =
      eval (splitPrimitiveAssignment P y) (primitiveGuard single) := by
  rw [primitiveExtensionGuard, eval_specialize_sumPolynomial, splitPrimitiveGuard, eval_rename]
  rfl

theorem eval_primitiveExtensionGuard_ne_zero_iff (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) :
    eval y (primitiveExtensionGuard P single) ≠ 0 ↔
      PrimitiveAdmissible single (splitPrimitiveAssignment P y) := by
  rw [eval_primitiveExtensionGuard, eval_primitiveGuard_ne_zero_iff]

/-- Any compatible enlarged chart supplies a nonzero value of the extension guard. -/
theorem eval_primitiveExtensionGuard_ne_zero_of_compatible {Q : Parameters K (m + 2)}
    (h : Compatible P Q) : eval (newPrimitiveValue Q) (primitiveExtensionGuard P Q.single) ≠ 0 := by
  rw [eval_primitiveExtensionGuard_ne_zero_iff, splitPrimitiveAssignment_eq_of_compatible P h]
  exact primitiveValue_admissible Q

/-- A compatible witness proves the guard is a nonzero polynomial on the fixed old chart. -/
theorem primitiveExtensionGuard_ne_zero_of_compatible {Q : Parameters K (m + 2)}
    (h : Compatible P Q) (single : Edge (m + 2) → Bool) (hs : Q.single = single) :
    primitiveExtensionGuard P single ≠ 0 := by
  intro hz
  apply eval_primitiveExtensionGuard_ne_zero_of_compatible P h
  rw [hs, hz, map_zero]

/-- Build the genuine enlarged cone chart at a nonzero value of the guard. -/
def extensionOfPrimitiveGuard (single : Edge (m + 2) → Bool) (y : NewPrimitiveIndex m → K)
    (hy : eval y (primitiveExtensionGuard P single) ≠ 0) : Parameters K (m + 2) :=
  parametersOfPrimitive single (splitPrimitiveAssignment P y)
    ((eval_primitiveExtensionGuard_ne_zero_iff P single y).mp hy)

@[simp] theorem extensionOfPrimitiveGuard_single (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) (hy : eval y (primitiveExtensionGuard P single) ≠ 0) :
    (extensionOfPrimitiveGuard P single y hy).single = single := rfl

@[simp] theorem primitiveValue_extensionOfPrimitiveGuard (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) (hy : eval y (primitiveExtensionGuard P single) ≠ 0) :
    primitiveValue (extensionOfPrimitiveGuard P single y hy) = splitPrimitiveAssignment P y :=
  primitiveValue_parametersOfPrimitive _ _ _

theorem extensionOfPrimitiveGuard_split (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) (hy : eval y (primitiveExtensionGuard P single) ≠ 0)
    (j : NewPrimitiveIndex m ⊕ PrimitiveIndex m) :
    primitiveValue (extensionOfPrimitiveGuard P single y hy) (primitiveOldNewEquiv m j) =
      Sum.elim y (primitiveValue P) j := by
  rw [primitiveValue_extensionOfPrimitiveGuard, splitPrimitiveAssignment_split]

@[simp] theorem extensionOfPrimitiveGuard_new (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) (hy : eval y (primitiveExtensionGuard P single) ≠ 0) :
    newPrimitiveValue (extensionOfPrimitiveGuard P single y hy) = y := by
  funext j
  exact extensionOfPrimitiveGuard_split P single y hy (.inl j)

/-- Agreement on the old primitive coordinates and graph flags is cone compatibility. -/
theorem compatible_of_primitiveValue_old {Q : Parameters K (m + 2)}
    (hs : ∀ e, Q.single (oldEdge m e) = P.single e)
    (h : ∀ i, primitiveValue Q (oldPrimitiveIndex m i) = primitiveValue P i) :
    Compatible P Q where
  single_eq := hs
  vertexSlope_eq i d := h (.vertexSlope i d)
  vertexHeight_eq i d := h (.vertexHeight i d)
  edgeSlope_eq e d := h (.edgeSlope e d)
  edgeHeight_eq e d := h (.edgeHeight e d)
  edgeLambda_eq e := h (.edgeLambda e)

theorem extensionOfPrimitiveGuard_compatible (single : Edge (m + 2) → Bool)
    (y : NewPrimitiveIndex m → K) (hy : eval y (primitiveExtensionGuard P single) ≠ 0)
    (hs : ∀ e, single (oldEdge m e) = P.single e) :
    Compatible P (extensionOfPrimitiveGuard P single y hy) :=
  compatible_of_primitiveValue_old P hs (fun i => extensionOfPrimitiveGuard_split P single y hy (.inr i))

/-- The normalized C.4 parameters provide an admissible fiber over every old rational B.5 chart. -/
theorem b5_primitiveExtensionGuard_ne_zero (n : ℕ) (P : Parameters ℚ (10 + 2 * n))
    (hP : P.single = B5.single) : primitiveExtensionGuard P B5.single ≠ 0 :=
  primitiveExtensionGuard_ne_zero_of_compatible P (B22.c4Extension_compatible n P hP) _ rfl

/-- The B.5 graph flags agree on every old edge of a chart reconstructed from the guard. -/
theorem b5_extensionOfPrimitiveGuard_compatible (n : ℕ) (P : Parameters K (10 + 2 * n))
    (hP : P.single = B5.single) (y : NewPrimitiveIndex (10 + 2 * n) → K)
    (hy : eval y (primitiveExtensionGuard P B5.single) ≠ 0) :
    Compatible P (extensionOfPrimitiveGuard P B5.single y hy) :=
  extensionOfPrimitiveGuard_compatible P B5.single y hy (fun e => (congrFun hP e).symm)

end IdealGeneration.CubicSupported.RationalChart
