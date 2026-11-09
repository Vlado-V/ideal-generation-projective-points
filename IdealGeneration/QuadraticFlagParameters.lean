module

public import IdealGeneration.QuadraticFlagInterpolation
public import IdealGeneration.QuadraticPairEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The normal directions determine actual layer-correction coefficients. -/

noncomputable section
namespace IdealGeneration.QuadraticFlag

variable {K P J : Type*} [Field K]

/-- The unique correction for the two independent layer normal equations. -/
def layerCorrection (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (i : P × Bool) (j : J) : K × K :=
  normalCorrection (n₀ j).1 (n₀ j).2 (n₁ j).1 (n₁ j).2
    (-((n₁ j).1 + (n₁ j).2 * c i) * pairPoint p₀ i)

/-- The corrections satisfy both designated normal conditions in every layer. -/
theorem layerCorrection_spec (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hdet : ∀ j, (n₀ j).1 * (n₁ j).2 - (n₁ j).1 * (n₀ j).2 ≠ 0)
    (i : P × Bool) (j : J) :
    (n₀ j).1 * (layerCorrection c p₀ n₀ n₁ i j).1 +
      (n₀ j).2 * (layerCorrection c p₀ n₀ n₁ i j).2 = 0 ∧
    (n₁ j).1 * (pairPoint p₀ i + (layerCorrection c p₀ n₀ n₁ i j).1) +
      (n₁ j).2 * (c i * pairPoint p₀ i + (layerCorrection c p₀ n₀ n₁ i j).2) = 0 := by
  have h := normalCorrection_constraints (n₀ j).1 (n₀ j).2 (n₁ j).1 (n₁ j).2
    (-((n₁ j).1 + (n₁ j).2 * c i) * pairPoint p₀ i) (hdet j)
  change (n₀ j).1 * (layerCorrection c p₀ n₀ n₁ i j).1 +
      (n₀ j).2 * (layerCorrection c p₀ n₀ n₁ i j).2 = 0 ∧
    (n₁ j).1 * (layerCorrection c p₀ n₀ n₁ i j).1 +
      (n₁ j).2 * (layerCorrection c p₀ n₀ n₁ i j).2 =
        -((n₁ j).1 + (n₁ j).2 * c i) * pairPoint p₀ i at h
  exact ⟨h.1, by linear_combination h.2⟩

/-- Only the distinguished base pair receives layer corrections. -/
theorem layerCorrection_eq_zero_of_ne (c : P × Bool → K) (p₀ : P)
    (n₀ n₁ : J → K × K) (i : P × Bool) (j : J) (hi : i.1 ≠ p₀) :
    layerCorrection c p₀ n₀ n₁ i j = 0 := by
  classical
  have hp : pairPoint (K := K) p₀ i = 0 := by
    rcases i with ⟨p, q⟩
    cases q <;> simp [pairPoint, coordinatePoint, hi]
  simp [layerCorrection, normalCorrection, hp]

/-- Every independent pair of normal directions admits all the layer coefficients
required by the two-normal interpolation construction. -/
theorem exists_layerCorrections (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hdet : ∀ j, (n₀ j).1 * (n₁ j).2 - (n₁ j).1 * (n₀ j).2 ≠ 0) :
    ∃ a b : P × Bool → J → K,
      (∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0) ∧
      (∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
        (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0) := by
  exact ⟨fun i j => (layerCorrection c p₀ n₀ n₁ i j).1,
    fun i j => (layerCorrection c p₀ n₀ n₁ i j).2,
    fun i j => (layerCorrection_spec c p₀ n₀ n₁ hdet i j).1,
    fun i j => (layerCorrection_spec c p₀ n₀ n₁ hdet i j).2⟩

end IdealGeneration.QuadraticFlag
