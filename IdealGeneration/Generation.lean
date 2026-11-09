module

public import IdealGeneration.MainStatement
public import IdealGeneration.Multiplication
public import IdealGeneration.PointDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Generation in the degrees above scalar interpolation. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

local instance (a : PointCoordinates K n p) (e : ℕ) :
    AddCommGroup (pointDegreePiece K a e) := Module.addCommMonoidToAddCommGroup K

/-- Scalar interpolation in degree `d` gives surjective ideal multiplication from degree `d+1`. -/
theorem pointMultiplication_surjective_of_previous_scalar
    [CharZero K]
    (a : PointCoordinates K n p)
    (hs : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (pointMultiplication a (d + 1)) := by
  classical
  intro f
  obtain ⟨g, hg⟩ := formMultiplication_surjective (K := K) (n + 1) (d + 1) f.val
  choose h hh using fun j => hs (pointEvaluation K a (d + 1) (g j))
  let R := formMultiplication K (n + 1) d h
  have hR : R ∈ pointDegreePiece K a (d + 1) := by
    apply (mem_pointDegreePiece a R).mpr
    intro i
    calc
      eval (chartPoint K a i) R.val =
          ∑ j, chartPoint K a i j * pointEvaluation K a d (h j) i := by
        simp [R, formMultiplication_val]
      _ = ∑ j, chartPoint K a i j * pointEvaluation K a (d + 1) (g j) i := by
        simp only [hh]
      _ = eval (chartPoint K a i) (formMultiplication K (n + 1) (d + 1) g).val := by
        simp [formMultiplication_val]
      _ = 0 := by
        rw [hg]
        exact (mem_pointDegreePiece a f.val).mp f.property i
  let r : pointDegreePiece K a (d + 1) := ⟨R, hR⟩
  let shift (j : Fin (n + 1)) : Forms K (n + 1) (d + 1) :=
    ⟨X (Fin.last n) * (h j).val, by
      change (X (Fin.last n) * (h j).val).IsHomogeneous (d + 1)
      simpa only [Nat.add_comm 1 d] using
        ((isHomogeneous_X (R := K) (Fin.last n)).mul (h j).property)⟩
  let u : Fin (n + 1) → pointDegreePiece K a (d + 1) := fun j =>
    ⟨g j - shift j, by
      apply (mem_pointDegreePiece a _).mpr
      intro i
      change eval (chartPoint K a i) ((g j).val - X (Fin.last n) * (h j).val) = 0
      simp only [map_sub, map_mul, eval_X, chartPoint_last, one_mul]
      exact sub_eq_zero.mpr (congrFun (hh j) i).symm⟩
  let v : Fin (n + 1) → pointDegreePiece K a (d + 1) := Pi.single (Fin.last n) r
  refine ⟨u + v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hcancel : (∑ j : Fin (n + 1), X j *
        ((g j).val - X (Fin.last n) * (h j).val)) +
      X (Fin.last n) * (∑ j : Fin (n + 1), X j * (h j).val) =
      ∑ j : Fin (n + 1), X j * (g j).val := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have hsums : (∑ j : Fin (n + 1), X j * (X (Fin.last n) * (h j).val)) =
        ∑ j : Fin (n + 1), X (Fin.last n) * (X j * (h j).val) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsums]
    ring
  have hlast : (∑ j : Fin (n + 1), X j *
      (v j).val.val) =
        X (Fin.last n) * R.val := by
    have hv (j : Fin (n + 1)) : (v j).val.val =
        if j = Fin.last n then R.val else 0 := by
      by_cases hj : j = Fin.last n <;> simp [v, hj, r]
    simp_rw [hv]
    simp [mul_ite]
  change (∑ j : Fin (n + 1), X j *
    ((u j).val.val + (v j).val.val)) = f.val.val
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hlast]
  change (∑ j : Fin (n + 1), X j *
    ((g j).val - X (Fin.last n) * (h j).val)) +
      X (Fin.last n) * (∑ j : Fin (n + 1), X j * (h j).val) = f.val.val
  rw [hcancel]
  exact congrArg Subtype.val hg

/-- Every subsequent ideal multiplication is surjective after scalar interpolation. -/
theorem pointMultiplication_surjective_above_scalar
    [CharZero K]
    (a : PointCoordinates K n p)
    (hs : Function.Surjective (pointEvaluation K a d))
    {e : ℕ} (he : d + 1 ≤ e) : Function.Surjective (pointMultiplication a e) := by
  cases e with
  | zero => omega
  | succ e =>
    exact pointMultiplication_surjective_of_previous_scalar a
      (pointEvaluation_surjective_above a (show d ≤ e by omega) hs)

/-- On the principal open in the main statement, all multiplication maps above
the initial multiplication have zero cokernel. -/
theorem idealGenerationAt_surjective_above [CharZero K] (n d p : ℕ)
    (hp : p ≤ (n + d).choose d) (h : IdealGenerationAt K n d p) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 → ∀ e, d + 1 ≤ e →
        Function.Surjective (pointMultiplication a e) := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  refine ⟨Δ, hΔ, fun a ha e he => ?_⟩
  have hs := (hgood a ha).2.1 d
  rw [min_eq_right hp] at hs
  exact pointMultiplication_surjective_above_scalar a
    (pointEvaluation_surjective_of_hilbert_eq a hs) he

/-- The multiplication cokernel has the exact number of new degree-`d+1` classes. -/
theorem pointMultiplication_cokernel_dimension (a : PointCoordinates K n p)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (hm : HasMaximalRank (pointMultiplication a d)) :
    finrank K ((pointDegreePiece K a (d + 1)) ⧸ (pointMultiplication a d).range) =
      (N (n + 1) (d + 1) - p) - (n + 1) * (N (n + 1) d - p) := by
  have h := cokernel_finrank_of_maximalRank (K := K)
    (V := Fin (n + 1) → pointDegreePiece K a d)
    (W := pointDegreePiece K a (d + 1)) (pointMultiplication a d) hm
  rw [pointMultiplication_source_finrank a hd, pointMultiplication_target_finrank a hd1] at h
  exact h

/-- The same principal open controls the initial cokernel and all higher multiplication maps. -/
theorem idealGenerationAt_generator_data [CharZero K] (n d p : ℕ)
    (hp : p ≤ N (n + 1) d) (h : IdealGenerationAt K n d p) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        finrank K ((pointDegreePiece K a (d + 1)) ⧸ (pointMultiplication a d).range) =
          (N (n + 1) (d + 1) - p) - (n + 1) * (N (n + 1) d - p) ∧
        ∀ e, d + 1 ≤ e → Function.Surjective (pointMultiplication a e) := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost, hm⟩ := hgood a ha
  have hd : pointHilbertFunction K a d = min (N (n + 1) d) p := by
    simpa only [N_chart] using hpost d
  have hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p := by
    simpa only [N_chart] using hpost (d + 1)
  refine ⟨pointMultiplication_cokernel_dimension a hd hd1 hm, fun e he => ?_⟩
  rw [min_eq_right hp] at hd
  exact pointMultiplication_surjective_above_scalar a
    (pointEvaluation_surjective_of_hilbert_eq a hd) he

end IdealGeneration
