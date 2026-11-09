module

public import IdealGeneration.FractionalInduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The degree-and-dimension induction of Section 6.2. -/

noncomputable section
namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- Quadratic and cubic bases, together with the remaining two-normal step,
complete the simultaneous degree and dimension induction. -/
theorem allPointCounts_of_quadratic_cubic_and_two_normal
    (hquadratic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p)
    (hcubic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p)
    (htwoNormal : ∀ n d, 1 ≤ n → 4 ≤ d → d * (d - 1) < n →
      (∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 1) p) →
      (∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 2) p) →
      (∀ p, IdealGenerationAt K (n - 2) d p) →
      ∀ p, IdealGenerationAt K n d p) :
    ∀ d, 2 ≤ d → ∀ n, 1 ≤ n → ∀ p, IdealGenerationAt K n d p := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases htwo : d = 2
    · subst d
      exact fun n hn p => hquadratic n p hn
    by_cases hthree : d = 3
    · subst d
      exact fun n hn p => hcubic n p hn
    have hd4 : 4 ≤ d := by omega
    have hprevious : ∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 1) p := by
      intro m p hm
      exact ih (d - 1) (by omega) (by omega) m hm p
    have hsecond : ∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 2) p := by
      intro m p hm
      exact ih (d - 2) (by omega) (by omega) m hm p
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro hn
      by_cases hwindow : n ≤ d * (d - 1)
      · exact one_hyperplane_induction d hd4 hprevious hsecond n hn hwindow
      · have hsize : 12 ≤ d * (d - 1) := by
          have h := Nat.mul_le_mul hd4 (show 3 ≤ d - 1 by omega)
          norm_num at h ⊢
          exact h
        have hsmall : ∀ p, IdealGenerationAt K (n - 2) d p :=
          ihn (n - 2) (by omega) (by omega)
        exact htwoNormal n d hn hd4 (by omega) hprevious hsecond hsmall

/-- The induction result implies the initial-degree formulation of Theorem 1.1. -/
theorem idealGenerationConjecture_of_quadratic_cubic_and_two_normal
    (hquadratic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p)
    (hcubic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p)
    (htwoNormal : ∀ n d, 1 ≤ n → 4 ≤ d → d * (d - 1) < n →
      (∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 1) p) →
      (∀ m p, 1 ≤ m → IdealGenerationAt K m (d - 2) p) →
      (∀ p, IdealGenerationAt K (n - 2) d p) →
      ∀ p, IdealGenerationAt K n d p) :
    IdealGenerationConjecture K := by
  intro n d p hn hd _ _
  exact allPointCounts_of_quadratic_cubic_and_two_normal
    hquadratic hcubic htwoNormal d hd n hn p

end IdealGeneration
