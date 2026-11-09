module

public import IdealGeneration.ConeRepresentatives

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normalizing homogeneous representatives in an affine chart

Nonzero final coordinates can be rescaled to one. Homogeneous equation spaces
and their multiplication maps are preserved by this normalization.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

/-- Affine coordinates obtained by dividing by the final coordinate. -/
def normalizedCoordinates (z : Fin p → Fin (n + 1) → K) : PointCoordinates K n p :=
  fun ij => z ij.1 ij.2.castSucc / z ij.1 (Fin.last n)

/-- Scaling the normalized chart representative recovers the original one. -/
theorem normalizedCoordinates_scale (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) (i : Fin p) :
    (fun j => z i (Fin.last n) * chartPoint K (normalizedCoordinates z) i j) = z i := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp [normalizedCoordinates, mul_div_cancel₀ _ (hz i)]

/-- Nonzero rescaling preserves each homogeneous equation space. -/
theorem representativePiece_normalization (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) (d : ℕ) :
    representativePiece K z d = pointDegreePiece K (normalizedCoordinates z) d := by
  ext f
  simp only [mem_representativePiece, mem_pointDegreePiece]
  apply forall_congr'
  intro i
  have hs := homogeneous_eval_scale_eq_zero_iff f.property
    (chartPoint K (normalizedCoordinates z) i) (hz i)
  rw [normalizedCoordinates_scale z hz i] at hs
  exact hs

/-- Canonical identification of representative and normalized equation spaces. -/
def normalizationPieceEquiv (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) (d : ℕ) :
    representativePiece K z d ≃ₗ[K] pointDegreePiece K (normalizedCoordinates z) d :=
  LinearEquiv.ofEq _ _ (representativePiece_normalization z hz d)

/-- Normalize each component of a tuple of equations. -/
def normalizationSourceEquiv (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) (d : ℕ) :
    (Fin (n + 1) → representativePiece K z d) ≃ₗ[K]
      (Fin (n + 1) → pointDegreePiece K (normalizedCoordinates z) d) :=
  LinearEquiv.piCongrRight (fun _ => normalizationPieceEquiv z hz d)

/-- Normalization commutes with multiplication by coordinate variables. -/
theorem normalization_multiplication (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0)
    (f : Fin (n + 1) → representativePiece K z d) :
    pointMultiplication (normalizedCoordinates z) d (normalizationSourceEquiv z hz d f) =
      normalizationPieceEquiv z hz (d + 1) (representativeMultiplication K z d f) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Normalization preserves injectivity of the multiplication map. -/
theorem normalization_multiplication_injective_iff (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) :
    Function.Injective (representativeMultiplication K z d) ↔
      Function.Injective (pointMultiplication (normalizedCoordinates z) d) := by
  constructor
  · intro h f g hfg
    obtain ⟨f, rfl⟩ := (normalizationSourceEquiv z hz d).surjective f
    obtain ⟨g, rfl⟩ := (normalizationSourceEquiv z hz d).surjective g
    apply congrArg (normalizationSourceEquiv z hz d)
    apply h
    apply (normalizationPieceEquiv z hz (d + 1)).injective
    simpa only [← normalization_multiplication] using hfg
  · intro h f g hfg
    apply (normalizationSourceEquiv z hz d).injective
    apply h
    rw [normalization_multiplication, normalization_multiplication, hfg]

/-- Normalization preserves surjectivity of the multiplication map. -/
theorem normalization_multiplication_surjective_iff (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) :
    Function.Surjective (representativeMultiplication K z d) ↔
      Function.Surjective (pointMultiplication (normalizedCoordinates z) d) := by
  constructor
  · intro h f
    obtain ⟨f, rfl⟩ := (normalizationPieceEquiv z hz (d + 1)).surjective f
    obtain ⟨g, hg⟩ := h f
    exact ⟨normalizationSourceEquiv z hz d g, by rw [normalization_multiplication, hg]⟩
  · intro h f
    obtain ⟨g, hg⟩ := h (normalizationPieceEquiv z hz (d + 1) f)
    obtain ⟨g, rfl⟩ := (normalizationSourceEquiv z hz d).surjective g
    refine ⟨g, (normalizationPieceEquiv z hz (d + 1)).injective ?_⟩
    simpa only [← normalization_multiplication] using hg

/-- Normalization preserves maximal rank of the multiplication map. -/
theorem normalization_multiplication_maximalRank_iff (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) :
    HasMaximalRank (representativeMultiplication K z d) ↔
      HasMaximalRank (pointMultiplication (normalizedCoordinates z) d) := by
  unfold HasMaximalRank
  rw [normalization_multiplication_injective_iff z hz,
    normalization_multiplication_surjective_iff z hz]

/-- Normalization preserves the dimension of every equation space. -/
theorem normalization_finrank (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) ≠ 0) (d : ℕ) :
    finrank K (representativePiece K z d) =
      finrank K (pointDegreePiece K (normalizedCoordinates z) d) :=
  (normalizationPieceEquiv z hz d).finrank_eq

end IdealGeneration
