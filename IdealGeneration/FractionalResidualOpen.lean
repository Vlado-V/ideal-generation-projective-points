module

public import IdealGeneration.FractionalResidual
public import IdealGeneration.PointAvoidance
public import IdealGeneration.PointDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Openness of the outer residual problem

The partial trace image and scalar trace points stay fixed while the full
residual points move in their ordinary affine configuration space.
-/

noncomputable section
namespace IdealGeneration.FractionalResidualOpen
open MvPolynomial Module HyperplaneEuler DifferentialPoint
set_option maxHeartbeats 900000
variable {K : Type*} [Field K]

local instance tupleGroup {n d : ℕ} : AddCommGroup (Fin (n + 1) → Forms K (n + 2) d) :=
  Module.addCommMonoidToAddCommGroup K

/-- Reorganize a flat coordinate vector into its point and component indices. -/
def curryValues {I J : Type*} : ((I × J) → K) →ₗ[K] (I → J → K) where
  toFun v i j := v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full residual vector evaluation is polynomial in the point coordinates. -/
theorem offEvaluation_polynomial {n z d : ℕ} :
    IsPolynomialFamily (fun a : PointCoordinates K (n + 1) z =>
      FractionalResidual.offEvaluation (d := d) a) := by
  apply isPolynomialFamily_linearMap
  intro g
  have hflat : IsPolynomialFamily (fun a : PointCoordinates K (n + 1) z =>
      fun ij : Fin z × Fin (n + 1) => pointEvaluation K a d (g ij.2) ij.1) := by
    apply DeformationMatrix.isPolynomialFamily_pi
    intro ij
    simpa only [eval_chartEvaluationPolynomial] using
      (isPolynomialFamily_eval (chartEvaluationPolynomial (g ij.2) ij.1))
  exact hflat.linear_comp curryValues

/-- The outer residual matrix depends polynomially on every full point. -/
theorem residualConditions_polynomial {n z a d : ℕ}
    (A : Fin a → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 2) → K) :
    IsPolynomialFamily (fun Z : PointCoordinates K (n + 1) z =>
      residualConditions (fun i => chartPoint K Z i) A B y) := by
  apply isPolynomialFamily_linearMap
  intro g
  have hoff := (offEvaluation_polynomial (K := K) (n := n) (z := z) (d := d)).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Fin z → Fin (n + 1) → K) g)
  exact (hoff.prod_mk (isPolynomialFamily_const
    (fun i => eval (A i) (tangentProduct K (n + 1) d g).val))).prod_mk
      (isPolynomialFamily_const ((traceImage B y).mkQ (tupleEvaluation y g)))

/-- Scalar postulation and avoiding the hyperplane can be imposed on a residual injective open. -/
theorem injective_off_witness [Infinite K] {n z a d : ℕ}
    (A : Fin a → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 2) → K)
    (Z₀ : PointCoordinates K (n + 1) z)
    (hZ₀ : Function.Injective (residualConditions (fun i => chartPoint K Z₀ i) A B y))
    (hz : z ≤ N (n + 2) d) :
    ∃ Z : PointCoordinates K (n + 1) z,
      (∀ i, Z (i, 0) ≠ 0) ∧ Function.Surjective (pointEvaluation K Z d) ∧
      Function.Injective (residualConditions (fun i => chartPoint K Z i) A B y) := by
  obtain ⟨D, hD, hgood⟩ := injective_polynomial_principal_open
    (fun Z => residualConditions (fun i => chartPoint K Z i) A B y)
    (residualConditions_polynomial A B y) Z₀ hZ₀
  obtain ⟨E, hE, hscalar⟩ := generic_pointHilbertFunction_at (K := K) (n + 1) z d
  obtain ⟨Z₁, hZ₁D, hZ₁E⟩ := principal_opens_meet D E ⟨Z₀, hD⟩ hE
  have hprod : ∃ Z, eval Z (D * E) ≠ 0 := ⟨Z₁, by simpa only [map_mul] using mul_ne_zero hZ₁D hZ₁E⟩
  obtain ⟨Z, hZ, hoff⟩ := principal_open_meets_off_hyperplane (D * E) hprod
  have hparts : eval Z D ≠ 0 ∧ eval Z E ≠ 0 := by simpa only [map_mul, mul_ne_zero_iff] using hZ
  refine ⟨Z, hoff, ?_, hgood Z hparts.1⟩
  apply pointEvaluation_surjective_of_hilbert_eq
  have h := hscalar Z hparts.2
  rw [← N_chart (n + 1) d, min_eq_right hz] at h
  exact h

/-- The corresponding independent residual open has the same simultaneous scalar postulation. -/
theorem surjective_off_witness [Infinite K] {n z a d : ℕ}
    (A : Fin a → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 2) → K)
    (Z₀ : PointCoordinates K (n + 1) z)
    (hZ₀ : Function.Surjective (residualConditions (fun i => chartPoint K Z₀ i) A B y))
    (hz : z ≤ N (n + 2) d) :
    ∃ Z : PointCoordinates K (n + 1) z,
      (∀ i, Z (i, 0) ≠ 0) ∧ Function.Surjective (pointEvaluation K Z d) ∧
      Function.Surjective (residualConditions (fun i => chartPoint K Z i) A B y) := by
  obtain ⟨D, hD, hgood⟩ := rank_polynomial_principal_open
    (fun Z => residualConditions (fun i => chartPoint K Z i) A B y)
    (residualConditions_polynomial A B y) Z₀
  have honto (Z : PointCoordinates K (n + 1) z) (hZ : eval Z D ≠ 0) :
      Function.Surjective (residualConditions (fun i => chartPoint K Z i) A B y) := by
    have h := hgood Z hZ
    rw [LinearMap.range_eq_top.mpr hZ₀, finrank_top] at h
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) h))
  obtain ⟨E, hE, hscalar⟩ := generic_pointHilbertFunction_at (K := K) (n + 1) z d
  obtain ⟨Z₁, hZ₁D, hZ₁E⟩ := principal_opens_meet D E ⟨Z₀, hD⟩ hE
  have hprod : ∃ Z, eval Z (D * E) ≠ 0 := ⟨Z₁, by simpa only [map_mul] using mul_ne_zero hZ₁D hZ₁E⟩
  obtain ⟨Z, hZ, hoff⟩ := principal_open_meets_off_hyperplane (D * E) hprod
  have hparts : eval Z D ≠ 0 ∧ eval Z E ≠ 0 := by simpa only [map_mul, mul_ne_zero_iff] using hZ
  refine ⟨Z, hoff, ?_, honto Z hparts.1⟩
  apply pointEvaluation_surjective_of_hilbert_eq
  have h := hscalar Z hparts.2
  rw [← N_chart (n + 1) d, min_eq_right hz] at h
  exact h

end IdealGeneration.FractionalResidualOpen
