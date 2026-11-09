module

public import IdealGeneration.FractionalResidual

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The inner differential move in the fractional hyperplane transfer

Scalar rows are selected only after the entire trace configuration and its
resulting image subspace have been fixed.
-/

noncomputable section
namespace IdealGeneration.FractionalInner
open Module MvPolynomial HyperplaneEuler DifferentialPoint FractionalResidual
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local instance partialGroup {n z d : ℕ} (a : PointCoordinates K (n + 1) z)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :
    AddCommGroup (residualPartialSpace a d y L) := Module.addCommMonoidToAddCommGroup K

/-- The transverse affine line with fixed tangential coordinates. -/
def normalVelocity (n : ℕ) : Fin (n + 2) → K := Fin.cons 1 0

theorem normalLine_eq (n : ℕ) (y : Fin (n + 1) → K) (t : K) :
    (fun i : Fin (n + 2) => (Fin.cons 0 y : Fin (n + 2) → K) i +
      t * normalVelocity (K := K) n i) = (Fin.cons t y : Fin (n + 2) → K) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [normalVelocity]

/-- The selected separating scalar rows supply the actual inner injective move. -/
theorem moving_injective_of_selected_rows [Infinite K] {n z p d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, chartPoint K a i 0 ≠ 0)
    (P : PointCoordinates K n p) (s : Finset (Fin p))
    (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 1) → K)
    (hB : Function.Injective ((vectorEvaluation y).comp B.subtype))
    (hrows : Function.Injective (selectedScalarEvaluation (K := K)
      (V := ↥(residualPartialSpace a d y (traceImage B (Fin.cons 0 y))))
      (residualPartialScalarRow a d P y (traceImage B (Fin.cons 0 y))) s)) :
    ∃ t : K, t ≠ 0 ∧ Function.Injective
      (fixedEvaluation (fun i => chartPoint K a i) (selectedPoints P s) B (Fin.cons t y)) := by
  obtain ⟨t, ht, _, hgood⟩ := exists_moving_point_injective
    (fun i => chartPoint K a i) (selectedPoints P s) B
    (Fin.cons 0 y) (normalVelocity n) rfl (by simp [normalVelocity]) ha hB
    (differential_residual_zero_of_selected_injective a P s y _ hrows)
  exact ⟨t, ht, by simpa only [normalLine_eq] using hgood⟩

/-- Independent selected scalar rows supply the actual inner independent move. -/
theorem moving_independent_of_selected_rows [Infinite K] {n z p d : ℕ} {C : Type*}
    [AddCommGroup C] [Module K C]
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, chartPoint K a i 0 ≠ 0)
    (P : PointCoordinates K n p) (s : Finset (Fin p))
    (T : Relations K (n + 1) (d + 1) →ₗ[K] C) (y : Fin (n + 1) → K)
    (hyLast : y (Fin.last n) = 1)
    (hT : Function.Surjective T)
    (hTon : ∀ b : T.ker, ∀ i : s, vectorEvaluation (chartPoint K P i.val) b.val = 0)
    (haScalar : Function.Surjective (pointEvaluation K a d))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0)
    (hrows : LinearIndependent K (fun i : s =>
      residualPartialScalarRow a d P y (traceImage T.ker (Fin.cons 0 y)) i)) :
    ∃ t : K, t ≠ 0 ∧ Function.Surjective
      ((fixedConditionEvaluation (fun i => chartPoint K a i) (selectedPoints P s) T).prod
        (chartEvaluation (Fin.cons t y))) := by
  have hres := differential_residualConditions_surjective_of_selected_independent
    a P s y T.ker haScalar hy hrows
  obtain ⟨t, ht, _, _, hgood⟩ := exists_moving_point_independent_avoiding
    (fun i => chartPoint K a i) (selectedPoints P s) T (Fin.cons 0 y) (normalVelocity n)
    rfl (by simp [normalVelocity]) (by simpa using hyLast) ha
    (fun _ => rfl) hTon hT hres ∅ Set.finite_empty
  exact ⟨t, ht, by simpa only [normalLine_eq] using hgood⟩

/-- The injective row-selection conclusion works for a trace image depending on all of `P`. -/
theorem generic_inner_injective [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, chartPoint K a i 0 ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (p q : ℕ) (hp : (n + 1) * finrank K (pointDegreePiece K a d) ≤ p) (hq : q ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ P : PointCoordinates K n p, eval P D ≠ 0) ∧
      ∀ P, eval P D ≠ 0 →
        ∀ (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 1) → K),
          Function.Injective ((vectorEvaluation y).comp B.subtype) →
          (∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) →
          finrank K (residualPartialSpace a d y (traceImage B (Fin.cons 0 y))) ≤ q →
          ∃ s : Finset (Fin p), s.card = q ∧ ∃ t : K, t ≠ 0 ∧
            Function.Injective (fixedEvaluation (fun i => chartPoint K a i)
              (selectedPoints P s) B (Fin.cons t y)) := by
  obtain ⟨D, hD, hgood⟩ := generic_scalar_condition_selection a ha hmul p hp
  refine ⟨D, hD, fun P hP B y hB hy hdim => ?_⟩
  obtain ⟨_, _, hselect⟩ := hgood P hP y (traceImage B (Fin.cons 0 y)) hy
  obtain ⟨s, hs, _, hinj⟩ := hselect q hq
  obtain ⟨t, ht, hmove⟩ := moving_injective_of_selected_rows a ha P s B y hB (hinj hdim)
  exact ⟨s, hs, t, ht, hmove⟩

/-- The independent row-selection conclusion also permits the trace image to depend on all of `P`. -/
theorem generic_inner_independent [Infinite K] {n z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, chartPoint K a i 0 ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (haScalar : Function.Surjective (pointEvaluation K a d))
    (p q : ℕ) (hp : (n + 1) * finrank K (pointDegreePiece K a d) ≤ p) (hq : q ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ P : PointCoordinates K n p, eval P D ≠ 0) ∧
      ∀ P, eval P D ≠ 0 →
        ∀ {C : Type*} [AddCommGroup C] [Module K C]
          (T : Relations K (n + 1) (d + 1) →ₗ[K] C) (y : Fin (n + 1) → K),
          y (Fin.last n) = 1 → Function.Surjective T →
          (∀ b : T.ker, ∀ i, vectorEvaluation (chartPoint K P i) b.val = 0) →
          (∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) →
          q ≤ finrank K (residualPartialSpace a d y (traceImage T.ker (Fin.cons 0 y))) →
          ∃ s : Finset (Fin p), s.card = q ∧ ∃ t : K, t ≠ 0 ∧
            Function.Surjective
              ((fixedConditionEvaluation (fun i => chartPoint K a i) (selectedPoints P s) T).prod
                (chartEvaluation (Fin.cons t y))) := by
  obtain ⟨D, hD, hgood⟩ := generic_scalar_condition_selection a ha hmul p hp
  refine ⟨D, hD, fun P hP C _ _ T y hyLast hT hTon hy hdim => ?_⟩
  obtain ⟨_, _, hselect⟩ := hgood P hP y (traceImage T.ker (Fin.cons 0 y)) hy
  obtain ⟨s, hs, hLI, _⟩ := hselect q hq
  obtain ⟨t, ht, hmove⟩ := moving_independent_of_selected_rows
    a ha P s T y hyLast hT (fun b i => hTon b i.val) haScalar hy (hLI hdim)
  exact ⟨s, hs, t, ht, hmove⟩

end IdealGeneration.FractionalInner
