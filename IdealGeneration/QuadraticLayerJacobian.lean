module

public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The height Jacobian for an untouched pair

The two inverse normal columns give the affine dependence of each chosen
quadratic lift on the two cone heights. Projection along the two base
directions then gives a two-dimensional affine map. Its determinant is
computed for arbitrary field elements.
-/

noncomputable section
namespace IdealGeneration.QuadraticLayerJacobian

variable {K : Type*} [Field K]

/-- The determinant of two normal directions, viewed as rows or columns. -/
def normalDet (n₀ n₁ : K × K) : K := n₀.1 * n₁.2 - n₁.1 * n₀.2

/-- Evaluation of a normal direction against a coefficient vector. -/
def normalPairing (n v : K × K) : K := n.1 * v.1 + n.2 * v.2

/-- The normal equation evaluated on the base direction `(1,c)`. -/
def directionDot (c : K) (n : K × K) : K := n.1 + c * n.2

/-- First column of the inverse normal matrix. -/
def inverseColumn₀ (n₀ n₁ : K × K) : K × K :=
  (n₁.2 / normalDet n₀ n₁, -n₁.1 / normalDet n₀ n₁)

/-- Second column of the inverse normal matrix. -/
def inverseColumn₁ (n₀ n₁ : K × K) : K × K :=
  (-n₀.2 / normalDet n₀ n₁, n₀.1 / normalDet n₀ n₁)

/-- Projection onto `(1,c')` along `(1,c)`, expressed as its scalar coefficient. -/
def projectedCoefficient (c c' : K) (v : K × K) : K :=
  (v.2 - c * v.1) / (c' - c)

/-- The displayed columns are the actual inverse of the two normal equations. -/
theorem inverseColumn_pairings (n₀ n₁ : K × K) (hD : normalDet n₀ n₁ ≠ 0) :
    normalPairing n₀ (inverseColumn₀ n₀ n₁) = 1 ∧
    normalPairing n₁ (inverseColumn₀ n₀ n₁) = 0 ∧
    normalPairing n₀ (inverseColumn₁ n₀ n₁) = 0 ∧
    normalPairing n₁ (inverseColumn₁ n₀ n₁) = 1 := by
  change n₀.1 * n₁.2 - n₁.1 * n₀.2 ≠ 0 at hD
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    dsimp [normalPairing, inverseColumn₀, inverseColumn₁, normalDet] <;>
    field_simp <;> ring

/-- Projection of the first inverse column. -/
theorem projectedCoefficient_inverseColumn₀ (n₀ n₁ : K × K) (c c' : K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0) :
    projectedCoefficient c c' (inverseColumn₀ n₀ n₁) =
      -directionDot c n₁ / (normalDet n₀ n₁ * (c' - c)) := by
  change n₀.1 * n₁.2 - n₁.1 * n₀.2 ≠ 0 at hD
  dsimp [projectedCoefficient, inverseColumn₀, normalDet, directionDot]
  field_simp
  ring

/-- Projection of the second inverse column. -/
theorem projectedCoefficient_inverseColumn₁ (n₀ n₁ : K × K) (c c' : K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0) :
    projectedCoefficient c c' (inverseColumn₁ n₀ n₁) =
      directionDot c n₀ / (normalDet n₀ n₁ * (c' - c)) := by
  change n₀.1 * n₁.2 - n₁.1 * n₀.2 ≠ 0 at hD
  dsimp [projectedCoefficient, inverseColumn₁, normalDet, directionDot]
  field_simp
  ring

/-- Both inverse columns have nonzero projected coefficient when the two
normal directions avoid the base direction. -/
theorem projectedCoefficient_inverseColumns_ne_zero (n₀ n₁ : K × K) (c c' : K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0)
    (hd₀ : directionDot c n₀ ≠ 0) (hd₁ : directionDot c n₁ ≠ 0) :
    projectedCoefficient c c' (inverseColumn₀ n₀ n₁) ≠ 0 ∧
      projectedCoefficient c c' (inverseColumn₁ n₀ n₁) ≠ 0 := by
  rw [projectedCoefficient_inverseColumn₀ n₀ n₁ c c' hD hδ,
    projectedCoefficient_inverseColumn₁ n₀ n₁ c c' hD hδ]
  exact ⟨div_ne_zero (neg_ne_zero.mpr hd₁) (mul_ne_zero hD hδ),
    div_ne_zero hd₀ (mul_ne_zero hD hδ)⟩

/-- The first column of the height Jacobian. -/
def jacobianColumn₀ (n₀ n₁ : K × K) (c c' : K) : K × K :=
  (-projectedCoefficient c c' (inverseColumn₀ n₀ n₁) * directionDot c n₀) • n₀

/-- The second column of the height Jacobian. -/
def jacobianColumn₁ (n₀ n₁ : K × K) (c c' : K) : K × K :=
  (-projectedCoefficient c c' (inverseColumn₁ n₀ n₁) * directionDot c n₁) • n₁

/-- Scaling both columns scales their determinant by the two scalars. -/
theorem normalDet_smul (r s : K) (u v : K × K) :
    normalDet (r • u) (s • v) = r * s * normalDet u v := by
  simp [normalDet, smul_eq_mul]
  ring

/-- The exact nonconstant Jacobian determinant in the untouched-pair argument. -/
theorem jacobianDet_formula (n₀ n₁ : K × K) (c c' : K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0) :
    normalDet (jacobianColumn₀ n₀ n₁ c c') (jacobianColumn₁ n₀ n₁ c c') =
      -(directionDot c n₀ ^ 2 * directionDot c n₁ ^ 2) /
        (normalDet n₀ n₁ * (c' - c) ^ 2) := by
  rw [jacobianColumn₀, jacobianColumn₁, normalDet_smul,
    projectedCoefficient_inverseColumn₀ n₀ n₁ c c' hD hδ,
    projectedCoefficient_inverseColumn₁ n₀ n₁ c c' hD hδ]
  field_simp

/-- Every factor in the Jacobian determinant is nonzero under the stated
normal-direction and base-direction hypotheses. -/
theorem jacobianDet_ne_zero (n₀ n₁ : K × K) (c c' : K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0)
    (hd₀ : directionDot c n₀ ≠ 0) (hd₁ : directionDot c n₁ ≠ 0) :
    normalDet (jacobianColumn₀ n₀ n₁ c c') (jacobianColumn₁ n₀ n₁ c c') ≠ 0 := by
  rw [jacobianDet_formula n₀ n₁ c c' hD hδ]
  exact div_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hd₀) (pow_ne_zero 2 hd₁)))
    (mul_ne_zero hD (pow_ne_zero 2 hδ))

/-- The actual affine correction of a quadratic lift as the two normal
heights vary. The offset records its height-independent coefficient vector. -/
def affineLift (n₀ n₁ offset : K × K) (Q : K × K → K) (θ : K × K) : K × K :=
  offset - (θ.1 * Q n₀) • inverseColumn₀ n₀ n₁ -
    (θ.2 * Q n₁) • inverseColumn₁ n₀ n₁

/-- Normal evaluation is additive in its coefficient vector. -/
theorem normalPairing_sub (n u v : K × K) :
    normalPairing n (u - v) = normalPairing n u - normalPairing n v := by
  change n.1 * (u.1 - v.1) + n.2 * (u.2 - v.2) =
    (n.1 * u.1 + n.2 * u.2) - (n.1 * v.1 + n.2 * v.2)
  ring

/-- Normal evaluation is homogeneous in its coefficient vector. -/
theorem normalPairing_smul (n v : K × K) (r : K) :
    normalPairing n (r • v) = r * normalPairing n v := by
  change n.1 * (r * v.1) + n.2 * (r * v.2) = r * (n.1 * v.1 + n.2 * v.2)
  ring

/-- The affine lift changes the two normal evaluations by the required
height times the corresponding quadratic value. -/
theorem affineLift_pairings (n₀ n₁ offset : K × K) (Q : K × K → K) (θ : K × K)
    (hD : normalDet n₀ n₁ ≠ 0) :
    normalPairing n₀ (affineLift n₀ n₁ offset Q θ) =
      normalPairing n₀ offset - θ.1 * Q n₀ ∧
    normalPairing n₁ (affineLift n₀ n₁ offset Q θ) =
      normalPairing n₁ offset - θ.2 * Q n₁ := by
  obtain ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩ := inverseColumn_pairings n₀ n₁ hD
  constructor
  · simp only [affineLift, normalPairing_sub, normalPairing_smul, h₀₀, h₀₁,
      mul_one, mul_zero, sub_zero]
  · simp only [affineLift, normalPairing_sub, normalPairing_smul, h₁₀, h₁₁,
      mul_one, mul_zero, sub_zero]

/-- The three normal quadratics are `s²`, `st`, and `t²`. -/
def normalQuadratic₀ (n : K × K) : K := n.1 ^ 2

def normalQuadratic₁ (n : K × K) : K := n.1 * n.2

def normalQuadratic₂ (n : K × K) : K := n.2 ^ 2

/-- The two projected combinations of the three actual affine lifts. -/
def projectedHeightMap (n₀ n₁ : K × K) (c c' : K)
    (offset₀ offset₁ offset₂ : K × K) (θ : K × K) : K × K :=
  (projectedCoefficient c c'
    (affineLift n₀ n₁ offset₀ normalQuadratic₀ θ +
      c • affineLift n₀ n₁ offset₁ normalQuadratic₁ θ),
   projectedCoefficient c c'
    (affineLift n₀ n₁ offset₁ normalQuadratic₁ θ +
      c • affineLift n₀ n₁ offset₂ normalQuadratic₂ θ))

/-- Its dependence on the two heights is affine, with precisely the two
Jacobian columns used in the untouched-pair calculation. -/
theorem projectedHeightMap_affine (n₀ n₁ : K × K) (c c' : K)
    (offset₀ offset₁ offset₂ : K × K) (θ : K × K) :
    projectedHeightMap n₀ n₁ c c' offset₀ offset₁ offset₂ θ =
      projectedHeightMap n₀ n₁ c c' offset₀ offset₁ offset₂ 0 +
        θ.1 • jacobianColumn₀ n₀ n₁ c c' + θ.2 • jacobianColumn₁ n₀ n₁ c c' := by
  apply Prod.ext <;>
    simp [projectedHeightMap, affineLift, projectedCoefficient, normalQuadratic₀,
      normalQuadratic₁, normalQuadratic₂, jacobianColumn₀, jacobianColumn₁,
      directionDot, div_eq_mul_inv, smul_eq_mul] <;> ring

/-- A nonzero two-column determinant permits arbitrary prescribed values
of their linear combination, with the usual explicit inverse. -/
theorem columnCombination_surjective (v₀ v₁ : K × K)
    (hD : normalDet v₀ v₁ ≠ 0) :
    Function.Surjective (fun θ : K × K => θ.1 • v₀ + θ.2 • v₁) := by
  intro y
  refine ⟨((y.1 * v₁.2 - v₁.1 * y.2) / normalDet v₀ v₁,
    (v₀.1 * y.2 - y.1 * v₀.2) / normalDet v₀ v₁), ?_⟩
  change v₀.1 * v₁.2 - v₁.1 * v₀.2 ≠ 0 at hD
  have hD' : v₁.2 * v₀.1 - v₁.1 * v₀.2 ≠ 0 := by
    rwa [mul_comm v₁.2 v₀.1]
  apply Prod.ext
  · change ((y.1 * v₁.2 - v₁.1 * y.2) / normalDet v₀ v₁) * v₀.1 +
      ((v₀.1 * y.2 - y.1 * v₀.2) / normalDet v₀ v₁) * v₁.1 = y.1
    dsimp only [normalDet]
    field_simp [hD']
    ring
  · change ((y.1 * v₁.2 - v₁.1 * y.2) / normalDet v₀ v₁) * v₀.2 +
      ((v₀.1 * y.2 - y.1 * v₀.2) / normalDet v₀ v₁) * v₁.2 = y.2
    dsimp only [normalDet]
    field_simp [hD']
    ring

/-- The actual projected affine height map is onto whenever the four
specified direction factors are nonzero. -/
theorem projectedHeightMap_surjective (n₀ n₁ : K × K) (c c' : K)
    (offset₀ offset₁ offset₂ : K × K)
    (hD : normalDet n₀ n₁ ≠ 0) (hδ : c' - c ≠ 0)
    (hd₀ : directionDot c n₀ ≠ 0) (hd₁ : directionDot c n₁ ≠ 0) :
    Function.Surjective (projectedHeightMap n₀ n₁ c c' offset₀ offset₁ offset₂) := by
  intro y
  obtain ⟨θ, hθ⟩ := columnCombination_surjective
    (jacobianColumn₀ n₀ n₁ c c') (jacobianColumn₁ n₀ n₁ c c')
    (jacobianDet_ne_zero n₀ n₁ c c' hD hδ hd₀ hd₁)
    (y - projectedHeightMap n₀ n₁ c c' offset₀ offset₁ offset₂ 0)
  change θ.1 • jacobianColumn₀ n₀ n₁ c c' + θ.2 • jacobianColumn₁ n₀ n₁ c c' =
    y - projectedHeightMap n₀ n₁ c c' offset₀ offset₁ offset₂ 0 at hθ
  refine ⟨θ, ?_⟩
  rw [projectedHeightMap_affine, add_assoc, hθ]
  abel

end IdealGeneration.QuadraticLayerJacobian
