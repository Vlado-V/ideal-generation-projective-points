module

public import IdealGeneration.QuadraticPairProjection
public import IdealGeneration.QuadraticLayerHeightOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual cleared coefficients in (A.5) are the affine height maps. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination.QuadraticLiftParameters
open MvPolynomial QuadraticLayerJacobian QuadraticLayerHeightOpen

variable {K P J : Type*} [Field K] [Fintype P]
variable (D : QuadraticLiftParameters K P J)

/-- The height-independent contribution to a selected normal lift. -/
def liftOffset (k : Fin 3) (j : J) : K × K :=
  solveLayerNormal (D.normal₀ j) (D.normal₁ j) 0 (-(D.normal₁ j).2 * D.pairedBaseValue k)

/-- The explicit two-row solve agrees with the affine inverse-column formula. -/
theorem layerCoefficients_eq_affineLift (k : Fin 3) (j : J) :
    D.layerCoefficients k j = affineLift (D.normal₀ j) (D.normal₁ j)
      (D.liftOffset k j) (fun n => normalBasisValue k n.1 n.2)
      (D.height₀ j, D.height₁ j) := by
  apply Prod.ext <;>
    simp [layerCoefficients, liftOffset, solveLayerNormal, affineLift,
      inverseColumn₀, inverseColumn₁, normalDet, div_eq_mul_inv, smul_eq_mul] <;> ring

/-- The base correction changes only the affine offset of the layer vector. -/
def clearingOffset (r : Fin 2) (j : J) : K × K := (D.offsetFirst r j, D.offsetSecond r j)

def adjustedOffset₀ (i : P × Bool) (j : J) : K × K :=
  D.liftOffset 0 j - D.clearingOffset 0 j + D.slope i • D.clearingOffset 1 j

def adjustedOffset₁ (j : J) : K × K := D.liftOffset 1 j - D.clearingOffset 1 j

/-- The two actual coefficients for the normal multipliers `s` and `t`. -/
def gammaPair (i : P × Bool) (j : J) : K × K := (D.pairGamma i 0 j, D.pairGamma i 1 j)

/-- The height Jacobian applies to the actual two coefficients after clearing the base. -/
theorem gammaPair_eq (i : P × Bool) (j : J) :
    D.gammaPair i j = -projectedHeightMap (D.normal₀ j) (D.normal₁ j)
      (D.slope i) (D.slope (partner i)) (D.adjustedOffset₀ i j) (D.adjustedOffset₁ j)
      (D.liftOffset 2 j) (D.height₀ j, D.height₁ j) := by
  apply Prod.ext <;>
    simp [gammaPair, pairGamma, clearedFirst, clearedSecond, combinedFirst, combinedSecond,
      layerCoefficients_eq_affineLift, projectedHeightMap, adjustedOffset₀, adjustedOffset₁,
      clearingOffset, affineLift, projectedCoefficient, normalBasisValue,
      normalQuadratic₀, normalQuadratic₁, normalQuadratic₂, div_eq_mul_inv, smul_eq_mul] <;> ring

/-- The data for the two selected layers is independent of their varying heights. -/
def twoLayerData (layers : Bool → J) (i : P × Bool) : TwoLayerData K where
  normal₀ b := D.normal₀ (layers b)
  normal₁ b := D.normal₁ (layers b)
  slope := D.slope i
  partnerSlope := D.slope (partner i)
  offset₀ b := D.adjustedOffset₀ i (layers b)
  offset₁ b := D.adjustedOffset₁ (layers b)
  offset₂ b := D.liftOffset 2 (layers b)

variable [DecidableEq J]

/-- Vary just the four heights in the two selected layers. -/
def withSelectedHeights (layers : Bool → J) (a : HeightIndex → K)
    (ha : ∀ h, a h ≠ 0) : QuadraticLiftParameters K P J where
  slope := D.slope
  distinguishedPair := D.distinguishedPair
  normal₀ := D.normal₀
  normal₁ := D.normal₁
  baseHeight := D.baseHeight
  height₀ j := if j = layers false then a (false, false)
    else if j = layers true then a (true, false) else D.height₀ j
  height₁ j := if j = layers false then a (false, true)
    else if j = layers true then a (true, true) else D.height₁ j
  baseHeight_ne := D.baseHeight_ne
  height₀_ne j := by
    split_ifs
    · exact ha (false, false)
    · exact ha (true, false)
    · exact D.height₀_ne j
  height₁_ne j := by
    split_ifs
    · exact ha (false, true)
    · exact ha (true, true)
    · exact D.height₁_ne j
  determinant_ne := D.determinant_ne

omit [Fintype P] in
theorem withSelectedHeights₀ (layers : Bool → J) (hle : layers false ≠ layers true)
    (a : HeightIndex → K) (ha : ∀ h, a h ≠ 0) (b : Bool) :
    (D.withSelectedHeights layers a ha).height₀ (layers b) = a (b, false) := by
  cases b <;> simp [withSelectedHeights, Ne.symm hle]

omit [Fintype P] in
theorem withSelectedHeights₁ (layers : Bool → J) (hle : layers false ≠ layers true)
    (a : HeightIndex → K) (ha : ∀ h, a h ≠ 0) (b : Bool) :
    (D.withSelectedHeights layers a ha).height₁ (layers b) = a (b, true) := by
  cases b <;> simp [withSelectedHeights, Ne.symm hle]

/-- Evaluation at the changed heights gives the negative affine height row. -/
theorem gammaPair_withSelectedHeights (layers : Bool → J) (hle : layers false ≠ layers true)
    (a : HeightIndex → K) (ha : ∀ h, a h ≠ 0) (i : P × Bool) (b : Bool) :
    (D.withSelectedHeights layers a ha).gammaPair i (layers b) =
      -layerValue (D.twoLayerData layers i) b (layerHeights a b) := by
  rw [gammaPair_eq, D.withSelectedHeights₀ layers hle a ha b,
    D.withSelectedHeights₁ layers hle a ha b]
  rfl

/-- The actual layer forms can be made independent for all untouched indices,
along with additional nonzero polynomial conditions. -/
theorem exists_selected_heights [Infinite K] {Extra : Type*} [Fintype Extra]
    (layers : Bool → J) (hle : layers false ≠ layers true) (hc : Function.Injective D.slope)
    (h₀ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∀ b,
      directionDot (D.slope i) (D.normal₀ (layers b)) ≠ 0)
    (h₁ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∀ b,
      directionDot (D.slope i) (D.normal₁ (layers b)) ≠ 0)
    (extra : Extra → MvPolynomial HeightIndex K) (he : ∀ e, extra e ≠ 0) :
    ∃ a : HeightIndex → K, ∃ ha : ∀ h, a h ≠ 0,
      (∀ e, eval a (extra e) ≠ 0) ∧ ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
        normalDet ((D.withSelectedHeights layers a ha).gammaPair i (layers false))
          ((D.withSelectedHeights layers a ha).gammaPair i (layers true)) ≠ 0 := by
  classical
  let I := {i : P × Bool // i.1 ≠ D.distinguishedPair}
  let f : I ⊕ Extra → MvPolynomial HeightIndex K :=
    Sum.elim (fun i => determinantPolynomial (D.twoLayerData layers i.val)) extra
  have hf : ∀ x, f x ≠ 0 := by
    intro x
    cases x with
    | inl i =>
      apply determinantPolynomial_ne_zero
      · exact sub_ne_zero.mpr fun h => partner_ne i.val (hc h)
      · intro b
        exact D.determinant_ne (layers b)
      · exact h₀ i.val i.property
      · exact h₁ i.val i.property
    | inr e => exact he e
  obtain ⟨a, hpoly, ha⟩ := simultaneous_nonzero_heights f hf
  refine ⟨a, ha, fun e => hpoly (.inr e), ?_⟩
  intro i hi
  have hp : eval a (determinantPolynomial (D.twoLayerData layers i)) ≠ 0 :=
    hpoly (.inl ⟨i, hi⟩)
  rw [eval_determinantPolynomial] at hp
  rw [D.gammaPair_withSelectedHeights layers hle a ha i false,
    D.gammaPair_withSelectedHeights layers hle a ha i true]
  simpa [normalDet] using hp

end IdealGeneration.QuadraticElimination.QuadraticLiftParameters
