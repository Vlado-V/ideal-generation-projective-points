module

public import IdealGeneration.HigherIntegral
public import IdealGeneration.InductionNumerics
public import IdealGeneration.PlaneCase
public import IdealGeneration.BaseCase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The integral edges in the quartic degree induction. -/

noncomputable section
namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- The projective-line assertion extends from its critical count to every point count. -/
theorem idealGenerationAt_projectiveLine_all (d : ℕ) (hd : 1 ≤ d) :
    ∀ p, IdealGenerationAt K 1 d p := by
  have he : E 2 d = 1 := by
    simp only [E, N_two_variables, Nat.cast_add, Nat.cast_one]
    exact div_self (by positivity)
  have hl : lowerCritical 2 d = 1 := by simp [lowerCritical, he]
  have hu : upperCritical 2 d = 1 := by simp [upperCritical, he]
  have hi : IdealGenerationAt K 1 d (N 2 d - lowerCritical 2 d) := by
    simpa only [N_two_variables, hl, Nat.add_sub_cancel] using
      idealGenerationAt_projectiveLine (K := K) d
  have hs : IdealGenerationAt K 1 d (N 2 d - upperCritical 2 d) := by
    simpa only [N_two_variables, hu, Nat.add_sub_cancel] using
      idealGenerationAt_projectiveLine (K := K) d
  exact idealGenerationAt_all_of_critical (by omega) hd hi hs

/-- Cubics and the two fractional quartic edges supply the full quartic range of Proposition 6.1. -/
theorem quartic_one_hyperplane_range
    (hcubic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p)
    (hseven : ∀ p, IdealGenerationAt K 6 4 p)
    (htwelve : ∀ p, IdealGenerationAt K 11 4 p)
    (n : ℕ) (hn : 1 ≤ n) (hu : n ≤ 12) :
    ∀ p, IdealGenerationAt K n 4 p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hone : n = 1
    · subst n
      exact idealGenerationAt_projectiveLine_all 4 (by omega)
    by_cases htwo : n = 2
    · subst n
      exact idealGenerationAt_projectivePlane 4 (by omega)
    by_cases hseven' : n = 6
    · subst n
      exact hseven
    by_cases htwelve' : n = 11
    · subst n
      exact htwelve
    have hn3 : 3 ≤ n := by omega
    have hnprev : 1 ≤ n - 1 := by omega
    have hprev : n - 1 < n := by omega
    have heq : n - 1 + 1 = n := by omega
    obtain ⟨r, hr⟩ := quartic_trace_integral_of_not_exception (n + 1)
      (by omega) (by omega) (by omega) (by omega)
    have htrace : E (n - 1 + 1) (3 + 1) = (r : ℚ) := by
      simpa only [Nat.add_sub_cancel, heq] using hr
    have hG : IdealGenerationAt K (n - 1) (3 + 1)
        (N (n - 1 + 1) (3 + 1) - r) := by
      exact ih (n - 1) hprev hnprev (by omega) _
    have hprevious : IdealGenerationAt K (n - 1 + 1) 3
        (N (n - 1 + 2) 3 - ⌈hyperplaneResidualRatio (n - 1 + 2) (3 + 1)⌉₊) :=
      hcubic _ _ (by omega)
    have h := integral_hyperplane_transfer_of_maximal_rank (n - 1) 3 r
      (by omega) (by omega) htrace hG hprevious
    simpa only [heq] using h

end IdealGeneration
