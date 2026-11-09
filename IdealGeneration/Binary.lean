module

public import IdealGeneration.Multiplication
public import IdealGeneration.ScalarInterpolation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The projective-line base case

A one-dimensional space of equations has injective multiplication by coordinate
linear forms. In projective dimension one, scalar postulation makes both source
and target two-dimensional at the initial degree, giving the required base case.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n p d : ℕ}

/-- A one-dimensional equation space has no linear syzygies. -/
theorem pointMultiplication_injective_of_finrank_one
    (a : PointCoordinates K n p)
    (h : finrank K (pointDegreePiece K a d) = 1) :
    Function.Injective (pointMultiplication a d) := by
  have : Module.Free K (pointDegreePiece K a d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K a d)
  obtain ⟨g, hg, hspan⟩ := (finrank_eq_one_iff' (K := K) (V := pointDegreePiece K a d)).mp h
  have hgpoly : g.val.val ≠ 0 := by
    intro hz
    apply hg
    apply Subtype.ext
    exact Subtype.ext hz
  have hker : ∀ f : Fin (n + 1) → pointDegreePiece K a d,
      pointMultiplication a d f = 0 → f = 0 := by
    intro f hf
    choose c hc using fun j => hspan (f j)
    have hzero : (∑ j : Fin (n + 1), c j • (X j : Poly K (n + 1))) * g.val.val = 0 := by
      have hz := congrArg (fun q : pointDegreePiece K a (d + 1) => q.val.val) hf
      simp only [pointMultiplication_val, Submodule.coe_zero] at hz
      rw [Finset.sum_mul]
      convert hz using 1
      apply Finset.sum_congr rfl
      intro j _
      have hj := congrArg (fun q : pointDegreePiece K a d => q.val.val) (hc j)
      change c j • g.val.val = (f j).val.val at hj
      rw [← hj]
      simp
    have hlinear : ∑ j : Fin (n + 1), c j • (X j : Poly K (n + 1)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hgpoly
    have hc0 := (Fintype.linearIndependent_iff.mp (linearIndependent_X (Fin (n + 1)) K)) c hlinear
    funext j
    rw [← hc j, hc0 j, zero_smul]
    rfl
  
  intro f₁ f₂ hf
  apply sub_eq_zero.mp
  apply hker
  have hs : pointMultiplication a d (f₁ - f₂) =
      pointMultiplication a d f₁ - pointMultiplication a d f₂ := by
    apply Subtype.ext
    apply Subtype.ext
    change (∑ j, X j * ((f₁ j).val.val - (f₂ j).val.val)) =
      (∑ j, X j * (f₁ j).val.val) - ∑ j, X j * (f₂ j).val.val
    simp only [mul_sub, Finset.sum_sub_distrib]
  exact hs.trans (sub_eq_zero.mpr hf)

/-- On the projective line, scalar postulation at the initial degree proves surjectivity. -/
theorem binary_pointMultiplication_surjective_of_postulation
    (a : PointCoordinates K 1 d)
    (hd : pointHilbertFunction K a d = d)
    (hd1 : pointHilbertFunction K a (d + 1) = d) :
    Function.Surjective (pointMultiplication a d) := by
  have : Module.Free K (pointDegreePiece K a d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K a d)
  have : Module.Free K (pointDegreePiece K a (d + 1)) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K a (d + 1))
  have hsource : finrank K (pointDegreePiece K a d) = 1 := by
    have h := (pointDegreePiece K a d).finrank_quotient_add_finrank
    rw [finrank_chart_forms] at h
    change pointHilbertFunction K a d + _ = _ at h
    rw [hd] at h
    have he : (1 + d).choose d = d + 1 := by
      rw [Nat.add_comm, Nat.choose_succ_self_right]
    rw [he] at h
    omega
  have htarget : finrank K (pointDegreePiece K a (d + 1)) = 2 := by
    have h := (pointDegreePiece K a (d + 1)).finrank_quotient_add_finrank
    rw [finrank_chart_forms] at h
    change pointHilbertFunction K a (d + 1) + _ = _ at h
    rw [hd1] at h
    have he : (1 + (d + 1)).choose (d + 1) = d + 2 := by
      rw [Nat.add_comm 1 (d + 1), Nat.choose_succ_self_right]
    rw [he] at h
    omega
  have hdim : finrank K (Fin (1 + 1) → pointDegreePiece K a d) =
      finrank K (pointDegreePiece K a (d + 1)) := by
    rw [Module.finrank_pi_fintype]
    simp [hsource, htarget]
  with_unfolding_all exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := K) (V := Fin 2 → pointDegreePiece K a d) (V₂ := pointDegreePiece K a (d + 1)) (f := pointMultiplication a d) hdim).mp (pointMultiplication_injective_of_finrank_one a hsource)

/-- The projective-line case holds on a nonempty principal open. -/
theorem binary_ideal_generation [CharZero K] (d : ℕ) :
    ∃ E : MvPolynomial (Fin d × Fin 1) K,
      (∃ a : PointCoordinates K 1 d, eval a E ≠ 0) ∧
      ∀ a, eval a E ≠ 0 → DistinctPoints K a ∧
        Function.Surjective (pointMultiplication a d) := by
  obtain ⟨E, hE, hgood⟩ := generic_pointHilbertFunction (K := K) (n := 1) (by omega) d
  refine ⟨E, hE, fun a ha => ?_⟩
  obtain ⟨hdistinct, hpost⟩ := hgood a ha
  refine ⟨hdistinct, binary_pointMultiplication_surjective_of_postulation a ?_ ?_⟩
  · have he : (1 + d).choose d = d + 1 := by
      rw [Nat.add_comm, Nat.choose_succ_self_right]
    have hh := hpost d
    rw [he, min_eq_right (by omega)] at hh
    exact hh
  · have he : (1 + (d + 1)).choose (d + 1) = d + 2 := by
      rw [Nat.add_comm 1 (d + 1), Nat.choose_succ_self_right]
    have hh := hpost (d + 1)
    rw [he, min_eq_right (by omega)] at hh
    exact hh

end IdealGeneration
