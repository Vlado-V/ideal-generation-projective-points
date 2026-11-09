module

public import IdealGeneration.QuadraticLayerJacobian
public import IdealGeneration.RankOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Nonempty height conditions for two layers

Each untouched index gives a determinant polynomial in the four cone
heights. The two affine height maps can separately realize the coordinate
vectors, so this polynomial has an explicit nonzero value. Finitely many
such conditions hold simultaneously with every height nonzero.
-/

noncomputable section
namespace IdealGeneration.QuadraticLayerHeightOpen
open MvPolynomial QuadraticLayerJacobian

variable {K : Type*} [Field K]

/-- The two layers and the fixed coefficients for one untouched base index. -/
structure TwoLayerData (K : Type*) [Field K] where
  normal₀ : Bool → K × K
  normal₁ : Bool → K × K
  slope : K
  partnerSlope : K
  offset₀ : Bool → K × K
  offset₁ : Bool → K × K
  offset₂ : Bool → K × K

/-- Four independent heights, indexed by layer and normal direction. -/
abbrev HeightIndex := Bool × Bool

/-- Read the two heights belonging to one layer. -/
def layerHeights (a : HeightIndex → K) (layer : Bool) : K × K :=
  (a (layer, false), a (layer, true))

/-- The actual projected coefficient pair in one layer. -/
def layerValue (D : TwoLayerData K) (layer : Bool) (θ : K × K) : K × K :=
  projectedHeightMap (D.normal₀ layer) (D.normal₁ layer) D.slope D.partnerSlope
    (D.offset₀ layer) (D.offset₁ layer) (D.offset₂ layer) θ

/-- The polynomial pair for an affine two-height expression. -/
def affineVectorPolynomial (layer : Bool) (offset column₀ column₁ : K × K) :
    MvPolynomial HeightIndex K × MvPolynomial HeightIndex K :=
  (C offset.1 + C column₀.1 * X (layer, false) + C column₁.1 * X (layer, true),
   C offset.2 + C column₀.2 * X (layer, false) + C column₁.2 * X (layer, true))

/-- Evaluation recovers the affine expression coefficient by coefficient. -/
theorem eval_affineVectorPolynomial (layer : Bool) (offset column₀ column₁ : K × K)
    (a : HeightIndex → K) :
    (eval a (affineVectorPolynomial layer offset column₀ column₁).1,
      eval a (affineVectorPolynomial layer offset column₀ column₁).2) =
      offset + a (layer, false) • column₀ + a (layer, true) • column₁ := by
  apply Prod.ext <;> simp [affineVectorPolynomial, smul_eq_mul] <;> ring

/-- The actual affine coefficient pair encoded by height polynomials. -/
def layerPolynomial (D : TwoLayerData K) (layer : Bool) :
    MvPolynomial HeightIndex K × MvPolynomial HeightIndex K :=
  affineVectorPolynomial layer (layerValue D layer 0)
    (jacobianColumn₀ (D.normal₀ layer) (D.normal₁ layer) D.slope D.partnerSlope)
    (jacobianColumn₁ (D.normal₀ layer) (D.normal₁ layer) D.slope D.partnerSlope)

/-- The encoding evaluates to the actual two projected lift combinations. -/
theorem eval_layerPolynomial (D : TwoLayerData K) (layer : Bool) (a : HeightIndex → K) :
    (eval a (layerPolynomial D layer).1, eval a (layerPolynomial D layer).2) =
      layerValue D layer (layerHeights a layer) := by
  rw [layerPolynomial, eval_affineVectorPolynomial]
  exact (projectedHeightMap_affine (D.normal₀ layer) (D.normal₁ layer)
    D.slope D.partnerSlope (D.offset₀ layer) (D.offset₁ layer) (D.offset₂ layer)
    (layerHeights a layer)).symm

/-- The two-layer independence condition is an actual polynomial in four heights. -/
def determinantPolynomial (D : TwoLayerData K) : MvPolynomial HeightIndex K :=
  (layerPolynomial D false).1 * (layerPolynomial D true).2 -
    (layerPolynomial D true).1 * (layerPolynomial D false).2

/-- This polynomial evaluates to the determinant of the actual layer coefficients. -/
theorem eval_determinantPolynomial (D : TwoLayerData K) (a : HeightIndex → K) :
    eval a (determinantPolynomial D) =
      normalDet (layerValue D false (layerHeights a false))
        (layerValue D true (layerHeights a true)) := by
  rw [determinantPolynomial, map_sub, map_mul, map_mul]
  change normalDet
    (eval a (layerPolynomial D false).1, eval a (layerPolynomial D false).2)
    (eval a (layerPolynomial D true).1, eval a (layerPolynomial D true).2) = _
  rw [eval_layerPolynomial, eval_layerPolynomial]

/-- The two layers separately realize the two coordinate vectors, giving
a height assignment at which the determinant polynomial equals one. -/
theorem determinantPolynomial_has_unit_value (D : TwoLayerData K)
    (hδ : D.partnerSlope - D.slope ≠ 0)
    (hD : ∀ layer, normalDet (D.normal₀ layer) (D.normal₁ layer) ≠ 0)
    (hd₀ : ∀ layer, directionDot D.slope (D.normal₀ layer) ≠ 0)
    (hd₁ : ∀ layer, directionDot D.slope (D.normal₁ layer) ≠ 0) :
    ∃ a : HeightIndex → K, eval a (determinantPolynomial D) = 1 := by
  obtain ⟨θ₀, hθ₀⟩ := projectedHeightMap_surjective
    (D.normal₀ false) (D.normal₁ false) D.slope D.partnerSlope
    (D.offset₀ false) (D.offset₁ false) (D.offset₂ false)
    (hD false) hδ (hd₀ false) (hd₁ false) (1, 0)
  obtain ⟨θ₁, hθ₁⟩ := projectedHeightMap_surjective
    (D.normal₀ true) (D.normal₁ true) D.slope D.partnerSlope
    (D.offset₀ true) (D.offset₁ true) (D.offset₂ true)
    (hD true) hδ (hd₀ true) (hd₁ true) (0, 1)
  let a : HeightIndex → K := fun p =>
    if p.1 then (if p.2 then θ₁.2 else θ₁.1) else (if p.2 then θ₀.2 else θ₀.1)
  refine ⟨a, ?_⟩
  rw [eval_determinantPolynomial]
  change normalDet (layerValue D false θ₀) (layerValue D true θ₁) = 1
  change layerValue D false θ₀ = (1, 0) at hθ₀
  change layerValue D true θ₁ = (0, 1) at hθ₁
  rw [hθ₀, hθ₁]
  simp [normalDet]

/-- The determinant polynomial is nonzero for every admissible untouched index. -/
theorem determinantPolynomial_ne_zero (D : TwoLayerData K)
    (hδ : D.partnerSlope - D.slope ≠ 0)
    (hD : ∀ layer, normalDet (D.normal₀ layer) (D.normal₁ layer) ≠ 0)
    (hd₀ : ∀ layer, directionDot D.slope (D.normal₀ layer) ≠ 0)
    (hd₁ : ∀ layer, directionDot D.slope (D.normal₁ layer) ≠ 0) :
    determinantPolynomial D ≠ 0 := by
  obtain ⟨a, ha⟩ := determinantPolynomial_has_unit_value D hδ hD hd₀ hd₁
  intro hz
  rw [hz, map_zero] at ha
  exact zero_ne_one ha

/-- Every finite collection of nonzero height conditions has a simultaneous
solution at which all four heights are themselves nonzero. -/
theorem simultaneous_nonzero_heights [Infinite K] {I : Type*} [Fintype I]
    (p : I → MvPolynomial HeightIndex K) (hp : ∀ i, p i ≠ 0) :
    ∃ a : HeightIndex → K, (∀ i, eval a (p i) ≠ 0) ∧ ∀ h, a h ≠ 0 := by
  classical
  let family : I ⊕ HeightIndex → MvPolynomial HeightIndex K := Sum.elim p X
  have hfamily : ∀ j, family j ≠ 0 := by
    intro j
    cases j with
    | inl i => exact hp i
    | inr h => exact X_ne_zero h
  obtain ⟨a, ha⟩ := IdealGeneration.nonempty_principal_intersection family hfamily
  exact ⟨a, fun i => ha (.inl i), fun h => by simpa [family] using ha (.inr h)⟩

/-- Finitely many untouched indices, including both members of every pair,
can satisfy their two-layer independence conditions at the same nonzero heights. -/
theorem simultaneous_layer_independence [Infinite K] {I : Type*} [Fintype I]
    (D : I → TwoLayerData K)
    (hδ : ∀ i, (D i).partnerSlope - (D i).slope ≠ 0)
    (hD : ∀ i layer, normalDet ((D i).normal₀ layer) ((D i).normal₁ layer) ≠ 0)
    (hd₀ : ∀ i layer, directionDot (D i).slope ((D i).normal₀ layer) ≠ 0)
    (hd₁ : ∀ i layer, directionDot (D i).slope ((D i).normal₁ layer) ≠ 0) :
    ∃ a : HeightIndex → K,
      (∀ i, normalDet (layerValue (D i) false (layerHeights a false))
        (layerValue (D i) true (layerHeights a true)) ≠ 0) ∧ ∀ h, a h ≠ 0 := by
  obtain ⟨a, ha, hne⟩ := simultaneous_nonzero_heights
    (fun i => determinantPolynomial (D i))
    (fun i => determinantPolynomial_ne_zero (D i) (hδ i) (hD i) (hd₀ i) (hd₁ i))
  refine ⟨a, ?_, hne⟩
  intro i
  simpa only [eval_determinantPolynomial] using ha i

end IdealGeneration.QuadraticLayerHeightOpen
