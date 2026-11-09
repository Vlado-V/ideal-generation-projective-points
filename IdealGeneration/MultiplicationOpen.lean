module

public import IdealGeneration.Multiplication
public import IdealGeneration.ScalarInterpolation
public import IdealGeneration.MainStatement

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Openness of point-ideal multiplication

Euler relations give a fixed source for evaluation. This realizes the
point-ideal rank condition by polynomial matrices, despite the varying
ideal components in the multiplication map itself.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

/-- Polynomial Euler relations of degree `d`. -/
abbrev EulerRelations (K : Type*) [Field K] (n d : ℕ) :=
  LinearMap.ker (formMultiplication K (n + 1) d)

/-- Evaluate Euler relations in the full, fixed component-value space. -/
def eulerEvaluation (a : PointCoordinates K n p) (d : ℕ) :
    EulerRelations K n d →ₗ[K] (Fin (n + 1) → Fin p → K) :=
  (componentEvaluation a d).comp (formMultiplication K (n + 1) d).ker.subtype

/-- Euler-relation evaluation is a polynomial family of linear maps. -/
theorem eulerEvaluation_isPolynomialFamily (n p d : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K n p => eulerEvaluation a d) := by
  apply isPolynomialFamily_linearMap (K := K) (V := EulerRelations K n d)
    (W := Fin (n + 1) → Fin p → K)
    (fun a : PointCoordinates K n p => eulerEvaluation a d)
  intro f
  let v : Fin (n + 1) × Fin p → (Fin (n + 1) → Fin p → K) :=
    fun ji => Pi.single ji.1 (Pi.single ji.2 1)
  have hterm (ji : Fin (n + 1) × Fin p) :
      IsPolynomialFamily (fun a : PointCoordinates K n p =>
        pointEvaluation K a d (f.val ji.1) ji.2 • v ji) := by
    have hscalar : IsPolynomialFamily (fun a : PointCoordinates K n p =>
        pointEvaluation K a d (f.val ji.1) ji.2) := by
      simpa only [eval_chartEvaluationPolynomial] using
        isPolynomialFamily_eval (chartEvaluationPolynomial (f.val ji.1) ji.2)
    exact hscalar.smul (isPolynomialFamily_const (v ji))
  have hs := IsPolynomialFamily.sum hterm
  have heq : (fun a : PointCoordinates K n p =>
      ∑ ji, pointEvaluation K a d (f.val ji.1) ji.2 • v ji) =
      (fun a => eulerEvaluation a d f) := by
    funext a j i
    simp [v, Pi.single_apply, eulerEvaluation, componentEvaluation,
      Fintype.sum_prod_type, ite_apply, LinearMap.pi_apply]
  exact heq ▸ hs

/-- Euler evaluations automatically satisfy the fiberwise Euler relation. -/
theorem eulerEvaluation_range_le (a : PointCoordinates K n p) (d : ℕ) :
    (eulerEvaluation a d).range ≤ (fiberMultiplication a).ker := by
  rintro y ⟨f, rfl⟩
  change fiberMultiplication a (componentEvaluation a d f.val) = 0
  have h := (pointEulerSquare a d).commutes f.val
  change pointEvaluation K a (d + 1) (formMultiplication K (n + 1) d f.val) =
    fiberMultiplication a (componentEvaluation a d f.val) at h
  rw [← h, f.property, map_zero]

/-- The fixed-target evaluation and the fiber-kernel evaluation have the same injectivity. -/
theorem eulerEvaluation_injective_iff (a : PointCoordinates K n p) (d : ℕ) :
    Function.Injective (eulerEvaluation a d) ↔
      Function.Injective (pointEulerSquare a d).leftOnKernel := by
  constructor
  · intro h x y hxy
    exact h (congrArg Subtype.val hxy)
  · intro h x y hxy
    exact h (Subtype.ext hxy)

/-- Surjectivity onto the fiber kernel means equality of the full-target image with that kernel. -/
theorem eulerEvaluation_range_eq_iff (a : PointCoordinates K n p) (d : ℕ) :
    (eulerEvaluation a d).range = (fiberMultiplication a).ker ↔
      Function.Surjective (pointEulerSquare a d).leftOnKernel := by
  constructor
  · intro h y
    have hy : y.val ∈ (eulerEvaluation a d).range := by rw [h]; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  · intro h
    apply le_antisymm (eulerEvaluation_range_le a d)
    intro y hy
    obtain ⟨x, hx⟩ := h ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- The normalized final coordinate makes the fiber Euler map surjective. -/
theorem fiberMultiplication_surjective (a : PointCoordinates K n p) :
    Function.Surjective (fiberMultiplication a) := by
  classical
  intro y
  refine ⟨fun j i => if j = Fin.last n then y i else 0, ?_⟩
  ext i
  change (∑ j, chartPoint K a i j * (if j = Fin.last n then y i else 0)) = y i
  simp

/-- The fiber Euler kernel has its constant expected dimension. -/
theorem finrank_fiberMultiplication_ker (a : PointCoordinates K n p) :
    finrank K (fiberMultiplication a).ker = n * p := by
  have h := (fiberMultiplication a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (fiberMultiplication_surjective a), finrank_top] at h
  simp only [Module.finrank_pi_fintype, finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith

/-- Scalar evaluation stays surjective on a principal open containing a surjective witness. -/
theorem pointEvaluation_surjective_principal_open
    (a₀ : PointCoordinates K n p) (h₀ : Function.Surjective (pointEvaluation K a₀ d)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) := by
  obtain ⟨D, hD, hgood⟩ := rank_polynomial_principal_open
    (fun a : PointCoordinates K n p => pointEvaluation K a d)
    (pointEvaluation_isPolynomialFamily n p d) a₀
  refine ⟨D, hD, fun a ha => ?_⟩
  have hr := hgood a ha
  rw [LinearMap.range_eq_top.mpr h₀, finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) hr

/-- An injective multiplication witness has a principal open of injective multiplication maps. -/
theorem pointMultiplication_injective_principal_open
    (a₀ : PointCoordinates K n p) (h₀ : Function.Injective (pointMultiplication a₀ d)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Function.Injective (pointMultiplication a d) := by
  have hE₀ : Function.Injective (eulerEvaluation a₀ d) :=
    (eulerEvaluation_injective_iff a₀ d).mpr
      ((pointEulerSquare a₀ d).injective_iff.mp
        ((pointMultiplication_injective_iff a₀ d).mp h₀))
  obtain ⟨D, hD, hgood⟩ := injective_polynomial_principal_open (K := K)
    (V := EulerRelations K n d) (W := Fin (n + 1) → Fin p → K)
    (fun a : PointCoordinates K n p => eulerEvaluation a d)
    (eulerEvaluation_isPolynomialFamily n p d) a₀ hE₀
  refine ⟨D, hD, fun a ha => ?_⟩
  exact (pointMultiplication_injective_iff a d).mpr
    ((pointEulerSquare a d).injective_iff.mpr
      ((eulerEvaluation_injective_iff a d).mp (hgood a ha)))

/-- A surjective multiplication witness with scalar postulation persists on a principal open. -/
theorem pointMultiplication_surjective_principal_open [CharZero K]
    (a₀ : PointCoordinates K n p) (hscalar : Function.Surjective (pointEvaluation K a₀ d))
    (h₀ : Function.Surjective (pointMultiplication a₀ d)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointMultiplication a d) := by
  have hleft₀ : Function.Surjective (pointEulerSquare a₀ d).leftOnKernel :=
    (pointEulerSquare a₀ d).surjective_iff
      (formMultiplication_surjective (n + 1) d)
      (componentEvaluation_surjective a₀ hscalar) |>.mp
      ((pointMultiplication_surjective_iff a₀ d).mp h₀)
  have hr₀ : finrank K (eulerEvaluation a₀ d).range = n * p := by
    rw [(eulerEvaluation_range_eq_iff a₀ d).mpr hleft₀, finrank_fiberMultiplication_ker]
  obtain ⟨D₁, hD₁, hgood₁⟩ := rank_polynomial_principal_open (K := K)
    (V := EulerRelations K n d) (W := Fin (n + 1) → Fin p → K)
    (fun a : PointCoordinates K n p => eulerEvaluation a d)
    (eulerEvaluation_isPolynomialFamily n p d) a₀
  obtain ⟨D₂, hD₂, hgood₂⟩ := pointEvaluation_surjective_principal_open a₀ hscalar
  refine ⟨D₁ * D₂, by simpa using mul_ne_zero hD₁ hD₂, fun a ha => ?_⟩
  have hparts : eval a D₁ ≠ 0 ∧ eval a D₂ ≠ 0 := by simpa using ha
  have hlow := hgood₁ a hparts.1
  rw [hr₀] at hlow
  have hupp := Submodule.finrank_mono (eulerEvaluation_range_le a d)
  rw [finrank_fiberMultiplication_ker] at hupp
  have hr : (eulerEvaluation a d).range = (fiberMultiplication a).ker :=
    Submodule.eq_of_le_of_finrank_eq (eulerEvaluation_range_le a d)
      (by rw [finrank_fiberMultiplication_ker]; exact le_antisymm hupp hlow)
  apply (pointMultiplication_surjective_iff a d).mpr
  apply (pointEulerSquare a d).surjective_iff
    (formMultiplication_surjective (n + 1) d)
    (componentEvaluation_surjective a (hgood₂ a hparts.2)) |>.mpr
  exact (eulerEvaluation_range_eq_iff a d).mp hr

/-- Maximal rank of point-ideal multiplication is open on the scalar-postulation locus. -/
theorem pointMultiplication_maximalRank_principal_open [CharZero K]
    (a₀ : PointCoordinates K n p) (hscalar : Function.Surjective (pointEvaluation K a₀ d))
    (h₀ : HasMaximalRank (pointMultiplication a₀ d)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → HasMaximalRank (pointMultiplication a d) := by
  rcases h₀ with hinj | hsurj
  · obtain ⟨D, hD, hgood⟩ := pointMultiplication_injective_principal_open a₀ hinj
    exact ⟨D, hD, fun a ha => Or.inl (hgood a ha)⟩
  · obtain ⟨D, hD, hgood⟩ := pointMultiplication_surjective_principal_open a₀ hscalar hsurj
    exact ⟨D, hD, fun a ha => Or.inr (hgood a ha)⟩

/-- One scalar-postulated multiplication witness proves the general-points assertion. -/
theorem idealGenerationAt_of_witness [CharZero K] (hn : 1 ≤ n)
    (a₀ : PointCoordinates K n p) (hscalar : Function.Surjective (pointEvaluation K a₀ d))
    (h₀ : HasMaximalRank (pointMultiplication a₀ d)) : IdealGenerationAt K n d p := by
  obtain ⟨D, hD, hgoodD⟩ := pointMultiplication_maximalRank_principal_open a₀ hscalar h₀
  obtain ⟨E, hE, hgoodE⟩ := generic_pointHilbertFunction (K := K) hn p
  have hDne : D ≠ 0 := by intro hz; simp [hz] at hD
  have hEne : E ≠ 0 := by
    obtain ⟨a, ha⟩ := hE
    intro hz
    simp [hz] at ha
  have hprod : D * E ≠ 0 := mul_ne_zero hDne hEne
  have hex : ∃ a : PointCoordinates K n p, eval a (D * E) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  refine ⟨D * E, hex, fun a ha => ?_⟩
  have hparts : eval a D ≠ 0 ∧ eval a E ≠ 0 := by simpa using ha
  obtain ⟨hdistinct, hpost⟩ := hgoodE a hparts.2
  exact ⟨hdistinct, hpost, hgoodD a hparts.1⟩

end IdealGeneration
