module

public import IdealGeneration.ProjectiveTransport
public import IdealGeneration.CriticalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# From homogeneous representatives to general point ideals

Injective witnesses require no scalar hypothesis. For a surjective witness,
scalar evaluation in the initial degree must also be onto. This hypothesis is
stated either as actual evaluation surjectivity or its rank-nullity equality.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

/-- Simultaneous scalar evaluation on homogeneous representatives. -/
def representativeEvaluation (K : Type*) [Field K] {n p : ℕ}
    (z : Fin p → Fin n → K) (d : ℕ) : Forms K n d →ₗ[K] (Fin p → K) :=
  LinearMap.pi (fun i => evaluationLinear K n d (z i))

/-- The equations of the representatives form the scalar-evaluation kernel. -/
theorem representativeEvaluation_ker (z : Fin p → Fin n → K) (d : ℕ) :
    (representativeEvaluation K z d).ker = representativePiece K z d := by
  ext f
  simp [representativeEvaluation, mem_representativePiece, LinearMap.mem_ker,
    funext_iff, evaluationLinear]

/-- Scalar postulation expressed without truncated subtraction. -/
theorem representativeEvaluation_surjective_iff (z : Fin p → Fin n → K) (d : ℕ) :
    Function.Surjective (representativeEvaluation K z d) ↔
      finrank K (representativePiece K z d) + p = finrank K (Forms K n d) := by
  have htotal : finrank K (Fin p → K) = p := by simp
  have hdim := (representativeEvaluation K z d).finrank_range_add_finrank_ker
  rw [representativeEvaluation_ker] at hdim
  constructor
  · intro h
    rw [LinearMap.range_eq_top.mpr h, finrank_top, htotal] at hdim
    omega
  · intro h
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [htotal]
    omega

/-- The same exact dimension equality gives scalar surjectivity in a chart. -/
theorem pointEvaluation_surjective_of_piece_finrank (a : PointCoordinates K n p)
    (h : finrank K (pointDegreePiece K a d) + p = (n + d).choose d) :
    Function.Surjective (pointEvaluation K a d) := by
  apply pointEvaluation_surjective_of_hilbert_eq a
  have hdim := (pointDegreePiece K a d).finrank_quotient_add_finrank
  rw [finrank_chart_forms] at hdim
  change pointHilbertFunction K a d + finrank K (pointDegreePiece K a d) = _ at hdim
  omega

/-- An arbitrary nonzero homogeneous injection witness proves the general-points assertion. -/
theorem idealGenerationAt_of_representative_injective [CharZero K]
    (hn : 1 ≤ n) (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0)
    (hi : Function.Injective (representativeMultiplication K z d)) :
    IdealGenerationAt K n d p := by
  obtain ⟨a, _, hinj, _⟩ := exists_chart_transport z hz
  exact idealGenerationAt_of_injective_witness hn a ((hinj d).mp hi)

/-- A scalar-postulated maximal-rank witness in homogeneous coordinates proves
the general-points assertion. The exact dimension hypothesis includes the
scalar surjectivity needed on the surjective side. -/
theorem idealGenerationAt_of_representative_piece_finrank [CharZero K]
    (hn : 1 ≤ n) (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0)
    (hscalar : finrank K (representativePiece K z d) + p = (n + d).choose d)
    (hmax : HasMaximalRank (representativeMultiplication K z d)) :
    IdealGenerationAt K n d p := by
  obtain ⟨a, hdim, hinj, hsurj⟩ := exists_chart_transport z hz
  apply idealGenerationAt_of_witness hn a
  · apply pointEvaluation_surjective_of_piece_finrank a
    rw [← hdim d]
    exact hscalar
  · exact hmax.elim (fun h => Or.inl ((hinj d).mp h))
      (fun h => Or.inr ((hsurj d).mp h))

/-- A maximal-rank witness with actual scalar evaluation surjectivity proves
the general-points assertion after transport to a common affine chart. -/
theorem idealGenerationAt_of_representative_witness [CharZero K]
    (hn : 1 ≤ n) (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0)
    (hscalar : Function.Surjective (representativeEvaluation K z d))
    (hmax : HasMaximalRank (representativeMultiplication K z d)) :
    IdealGenerationAt K n d p := by
  apply idealGenerationAt_of_representative_piece_finrank hn z hz
  · simpa only [finrank_chart_forms] using
      (representativeEvaluation_surjective_iff z d).mp hscalar
  · exact hmax

/-- A surjective homogeneous multiplication witness retains the necessary
scalar-evaluation hypothesis explicitly. -/
theorem idealGenerationAt_of_representative_surjective [CharZero K]
    (hn : 1 ≤ n) (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0)
    (hscalar : Function.Surjective (representativeEvaluation K z d))
    (hs : Function.Surjective (representativeMultiplication K z d)) :
    IdealGenerationAt K n d p :=
  idealGenerationAt_of_representative_witness hn z hz hscalar (Or.inr hs)

/-- The injection wrapper indexed by the total number of homogeneous variables. -/
theorem idealGenerationAt_of_representative_injective_of_two_le [CharZero K]
    {N : ℕ} (hN : 2 ≤ N) (z : Fin p → Fin N → K) (hz : ∀ i, z i ≠ 0)
    (hi : Function.Injective (representativeMultiplication K z d)) :
    IdealGenerationAt K (N - 1) d p := by
  cases N with
  | zero => omega
  | succ n =>
      simpa only [Nat.add_one_sub_one] using
        idealGenerationAt_of_representative_injective (by omega : 1 ≤ n) z hz hi

/-- The scalar-postulated witness wrapper indexed by the total variable count. -/
theorem idealGenerationAt_of_representative_witness_of_two_le [CharZero K]
    {N : ℕ} (hN : 2 ≤ N) (z : Fin p → Fin N → K) (hz : ∀ i, z i ≠ 0)
    (hscalar : Function.Surjective (representativeEvaluation K z d))
    (hmax : HasMaximalRank (representativeMultiplication K z d)) :
    IdealGenerationAt K (N - 1) d p := by
  cases N with
  | zero => omega
  | succ n =>
      simpa only [Nat.add_one_sub_one] using
        idealGenerationAt_of_representative_witness (by omega : 1 ≤ n) z hz hscalar hmax

end IdealGeneration
