module

public import IdealGeneration.Generation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Actual ideal generation from the homogeneous multiplication statements. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n p : ℕ}

/-- Each projective point ideal is homogeneous for the usual total-degree grading. -/
theorem singlePointIdeal_isHomogeneous (u : Fin n → K) :
    (singlePointIdeal K u).IsHomogeneous (fun e => Forms K (n + 1) e) := by
  apply Ideal.homogeneous_span
  rintro f ⟨j, rfl⟩
  refine ⟨1, ?_⟩
  exact (isHomogeneous_X (R := K) j.castSucc).sub
    ((isHomogeneous_X (R := K) (Fin.last n)).C_mul (u j))

/-- Intersecting the projective point ideals preserves the total-degree grading. -/
theorem pointIdeal_isHomogeneous (a : PointCoordinates K n p) :
    (pointIdeal K a).IsHomogeneous (fun e => Forms K (n + 1) e) := by
  apply Ideal.IsHomogeneous.iInf
  intro i
  exact singlePointIdeal_isHomogeneous (fun j => a (i, j))

/-- The actual homogeneous equations through a prescribed degree. -/
def boundedPointEquations (a : PointCoordinates K n p) (D : ℕ) : Set (Poly K (n + 1)) :=
  {f | ∃ e, e ≤ D ∧ f.IsHomogeneous e ∧ f ∈ pointIdeal K a}

/-- Scalar interpolation bounds the degrees of generators of the actual polynomial ideal. -/
theorem pointIdeal_eq_span_bounded [CharZero K]
    (a : PointCoordinates K n p) (d : ℕ)
    (hs : Function.Surjective (pointEvaluation K a d)) :
    pointIdeal K a = Ideal.span (boundedPointEquations a (d + 1)) := by
  classical
  let J := Ideal.span (boundedPointEquations a (d + 1))
  have hhom : ∀ e, ∀ f : Forms K (n + 1) e,
      f.val ∈ pointIdeal K a → f.val ∈ J := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro f hf
      by_cases he : e ≤ d + 1
      · exact Ideal.subset_span ⟨e, he, f.property, hf⟩
      cases e with
      | zero => omega
      | succ e =>
        have hmul := pointMultiplication_surjective_above_scalar a hs
          (show d + 1 ≤ e by omega)
        have hf' : f ∈ pointDegreePiece K a (e + 1) :=
          (homogeneous_mem_pointIdeal_iff a f).mp hf
        obtain ⟨g, hg⟩ := hmul ⟨f, hf'⟩
        have heq : (∑ j : Fin (n + 1), X j * (g j).val.val) = f.val :=
          congrArg (fun v : pointDegreePiece K a (e + 1) => v.val.val) hg
        rw [← heq]
        apply J.sum_mem
        intro j _
        apply J.mul_mem_left
        exact ih e (by omega) (g j).val
          ((homogeneous_mem_pointIdeal_iff a (g j).val).mpr (g j).property)
  apply le_antisymm
  · intro f hf
    rw [← DirectSum.sum_support_decompose (fun e => Forms K (n + 1) e) f]
    apply J.sum_mem
    intro e _
    exact hhom e (DirectSum.decompose (fun e => Forms K (n + 1) e) f e)
      (((pointIdeal_isHomogeneous a).mem_iff).mp hf e)
  · apply Ideal.span_le.mpr
    rintro f ⟨e, _, _, hf⟩
    exact hf

/-- General points with scalar interpolation are generated through the next degree. -/
theorem generic_pointIdeal_bounded_generation [CharZero K]
    (n p d : ℕ) (hn : 1 ≤ n) (hp : p ≤ (n + d).choose d) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        pointIdeal K a = Ideal.span (boundedPointEquations a (d + 1)) := by
  obtain ⟨Δ, hΔ, hgood⟩ := generic_pointHilbertFunction (K := K) hn p
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  have hpost := (hgood a ha).2 d
  rw [min_eq_right hp] at hpost
  exact pointIdeal_eq_span_bounded a d (pointEvaluation_surjective_of_hilbert_eq a hpost)

/-- The equations in the two degrees that occur in the initial-degree statement. -/
def twoDegreePointEquations (a : PointCoordinates K n p) (d : ℕ) : Set (Poly K (n + 1)) :=
  {f | (f.IsHomogeneous d ∨ f.IsHomogeneous (d + 1)) ∧ f ∈ pointIdeal K a}

/-- Scalar postulation in the initial-degree cell gives actual generation in two degrees. -/
theorem pointIdeal_eq_span_two_degrees [CharZero K]
    (a : PointCoordinates K n p) (d : ℕ) (hd : 1 ≤ d)
    (hpost : ∀ e, pointHilbertFunction K a e = min (N (n + 1) e) p)
    (hp0 : N (n + 1) (d - 1) ≤ p) (hp1 : p ≤ N (n + 1) d) :
    pointIdeal K a = Ideal.span (twoDegreePointEquations a d) := by
  have hs : Function.Surjective (pointEvaluation K a d) := by
    apply pointEvaluation_surjective_of_hilbert_eq a
    simpa only [min_eq_right hp1] using hpost d
  rw [pointIdeal_eq_span_bounded a d hs]
  apply le_antisymm
  · apply Ideal.span_mono
    rintro f ⟨e, he, hf, hI⟩
    refine ⟨?_, hI⟩
    by_cases hsmall : e < d
    · have hcount : N (n + 1) e ≤ p := by
        calc
          N (n + 1) e = (n + e).choose e := N_chart n e
          _ ≤ (n + (d - 1)).choose (d - 1) :=
            chart_formsCount_mono (by omega)
          _ = N (n + 1) (d - 1) := (N_chart n (d - 1)).symm
          _ ≤ p := hp0
      have hz : pointDegreePiece K a e = ⊥ := by
        apply Submodule.finrank_eq_zero.mp
        rw [pointDegreePiece_finrank a (hpost e), Nat.sub_eq_zero_of_le hcount]
      have hmem : (⟨f, hf⟩ : Forms K (n + 1) e) ∈ pointDegreePiece K a e :=
        (homogeneous_mem_pointIdeal_iff a ⟨f, hf⟩).mp hI
      rw [hz] at hmem
      have hzero : (⟨f, hf⟩ : Forms K (n + 1) e) = 0 := by simpa using hmem
      have hfzero : f = 0 := congrArg Subtype.val hzero
      rw [hfzero]
      exact Or.inl (isHomogeneous_zero (Fin (n + 1)) K d)
    · have heq : e = d ∨ e = d + 1 := by omega
      rcases heq with rfl | rfl
      · exact Or.inl hf
      · exact Or.inr hf
  · apply Ideal.span_mono
    rintro f ⟨hf | hf, hI⟩
    · exact ⟨d, by omega, hf, hI⟩
    · exact ⟨d + 1, le_rfl, hf, hI⟩

/-- General points in the initial-degree interval have an ideal generated in its
initial degree and the following degree. -/
theorem generic_pointIdeal_two_degree_generation [CharZero K]
    (n p d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hp0 : N (n + 1) (d - 1) ≤ p) (hp1 : p ≤ N (n + 1) d) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        pointIdeal K a = Ideal.span (twoDegreePointEquations a d) := by
  obtain ⟨Δ, hΔ, hgood⟩ := generic_pointHilbertFunction (K := K) hn p
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  apply pointIdeal_eq_span_two_degrees a d hd _ hp0 hp1
  intro e
  simpa only [N_chart] using (hgood a ha).2 e

end IdealGeneration
