module

public import IdealGeneration.FinalInduction
public import IdealGeneration.TwoNormalIntegralTransfer
public import IdealGeneration.TwoNormalFractional

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The integral and fractional two-normal transfers in the final induction. -/

noncomputable section
namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- The appropriate two-normal transfer follows from the two lower degrees
and the result two projective dimensions below. -/
theorem two_normal_induction_step (n d : ℕ) (hd : 4 ≤ d)
    (hlarge : d * (d - 1) < n)
    (hprevious : ∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 1) p)
    (hsecond : ∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 2) p)
    (htrace : ∀ p, IdealGenerationAt K (n - 2) d p) :
    ∀ p, IdealGenerationAt K n d p := by
  have hsize : 12 ≤ d * (d - 1) := by
    have h := Nat.mul_le_mul hd (show 3 ≤ d - 1 by omega)
    norm_num at h ⊢
    exact h
  have hslice : ∀ p, IdealGenerationAt K (n - 1) (d - 1) p :=
    fun p => hprevious (n - 1) p (by omega)
  have hresidual : ∀ p, IdealGenerationAt K (n - 2) (d - 2) p :=
    fun p => hsecond (n - 2) p (by omega)
  by_cases h : ∃ r : ℕ, E (n - 1) d = (r : ℚ)
  · exact TwoNormalIntegral.proposition4_5 n d hd hlarge h hslice hresidual htrace
  · exact TwoNormalFractional.proposition5_1 n d hd hlarge h hslice hresidual htrace

/-- Once the two initial degrees are known, the complete higher-degree
induction gives maximal-rank multiplication for every general point count. -/
theorem allPointCounts_of_quadratic_and_cubic
    (hquadratic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p)
    (hcubic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p) :
    ∀ d, 2 ≤ d → ∀ n, 1 ≤ n → ∀ p, IdealGenerationAt K n d p :=
  allPointCounts_of_quadratic_cubic_and_two_normal hquadratic hcubic
    (fun n d _ hd hl => two_normal_induction_step n d hd hl)

end IdealGeneration
