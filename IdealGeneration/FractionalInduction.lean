module

public import IdealGeneration.FractionalHyperplaneTransfer
public import IdealGeneration.FractionalResidualBridge
public import IdealGeneration.FractionalResidualNatural
public import IdealGeneration.FractionalPointCounts
public import IdealGeneration.QuarticRange
public import IdealGeneration.ExceptionalQuintic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Applying the fractional transfer to the degree-induction bounds. -/

noncomputable section
namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- The higher-dimensional fractional edge uses only the two lower degrees. -/
theorem higher_fractional_induction_step (m d : ℕ) (hm : 3 ≤ m) (hd : 2 ≤ d)
    (hu : m + 2 ≤ (d + 3) * (d + 3 - 1) + 1)
    (hfrac : ¬ ∃ r : ℕ, E (m + 1) (d + 3) = (r : ℚ))
    (htop : ∀ p, IdealGenerationAt K m (d + 3) p)
    (hprevious : ∀ p, IdealGenerationAt K m (d + 2) p)
    (hsecond : ∀ p, IdealGenerationAt K (m + 1) (d + 1) p) :
    ∀ p, IdealGenerationAt K (m + 1) (d + 3) p := by
  have hgap := fractional_critical_gap (m + 1) (d + 3) hfrac
  have hgap' : upperCritical (m + 2 - 1) (d + 3) =
      lowerCritical (m + 2 - 1) (d + 3) + 1 := by simpa using hgap
  obtain ⟨hI, hS, hpos, horder, _, _⟩ := higherFractional_residual_counts_spec
    (m + 2) (d + 3) (by omega) (by omega) hu hgap'
  have hdef : N (m + 1) (d + 4) ≤ (m + 1) * N (m + 1) (d + 2) := by
    have h := higherFractional_defect_nonnegative (m + 2) (d + 3)
      (by omega) (by omega) hu
    simpa only [show m + 2 - 1 = m + 1 by omega,
      show d + 3 + 1 = d + 4 by omega, show d + 3 - 1 = d + 2 by omega] using h
  have hbudget : (m + 1) * fractionalResidualSCount (m + 2) (d + 3) ≤
      lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3) := by
    have h := fractional_scalar_budget_nat (m + 2) (d + 3) hS
      (higherFractional_scalar_budget (m + 2) (d + 3) (by omega) (by omega))
    simpa only [show m + 2 - 1 = m + 1 by omega] using h
  have hcell : lowerCritical (m + 1) (d + 3) +
      fractionalTraceRows (m + 2) (d + 3) + 2 ≤ N (m + 1) (d + 2) := by
    have h := (higherFractional_auxiliary_cells (m + 2) (d + 3)
      (by omega) (by omega) hu hgap' 2 (by omega)).2
    simpa only [show m + 2 - 1 = m + 1 by omega,
      show d + 3 - 1 = d + 2 by omega] using h.le
  have hres : ScalarInjectionAt K (m + 1) (d + 1)
      (fractionalResidualSCount (m + 2) (d + 3)) := by
    have h := higherFractional_residual_scalarInjectionAt (K := K)
      (m + 2) (d + 3) (by omega) (by omega) hu hgap' (by
        simpa only [show m + 2 - 1 = m + 1 by omega,
          show d + 3 - 2 = d + 1 by omega] using hsecond)
    simpa only [show m + 2 - 1 = m + 1 by omega,
      show d + 3 - 2 = d + 1 by omega] using h
  exact fractional_hyperplane_transfer_of_counts m d (by omega)
    hgap hdef hI hS hpos horder hbudget hcell hres htop hprevious

/-- Every odd four-variable edge of degree at least seven uses the second lower degree. -/
theorem four_fractional_induction_step (k : ℕ) (hk : 3 ≤ k)
    (hprevious : ∀ p, IdealGenerationAt K 3 (2 * k + 1 - 2) p) :
    ∀ p, IdealGenerationAt K 3 (2 * k + 1) p := by
  have hgap : upperCritical 3 (2 * k + 1) = lowerCritical 3 (2 * k + 1) + 1 := by
    rw [four_fractional_upper_trace, four_fractional_tau]
  obtain ⟨hI, hS, hpos, horder, _, _⟩ := four_fractional_residual_counts_spec k hk
  have hbudget : 3 * fractionalResidualSCount 4 (2 * k + 1) ≤
      lowerCritical 3 (2 * k + 1) + fractionalTraceRows 4 (2 * k + 1) := by
    have h := fractional_scalar_budget_nat 4 (2 * k + 1) hS
      (by simpa using four_fractional_scalar_budget k hk)
    simpa using h
  have hcell : lowerCritical 3 (2 * k + 1) + fractionalTraceRows 4 (2 * k + 1) + 2 ≤
      N 3 (2 * k + 1 - 1) := (four_fractional_auxiliary_cells k hk 2 (by omega)).2.le
  have hres := fourFractional_residual_scalarInjectionAt (K := K) k hk hprevious
  have hdegree : 2 * k - 2 + 3 = 2 * k + 1 := by omega
  have hresdegree : 2 * k - 2 + 1 = 2 * k + 1 - 2 := by omega
  rw [← hdegree]
  apply fractional_hyperplane_transfer_of_counts 2 (2 * k - 2) (by omega)
  · simpa only [hdegree] using hgap
  · simpa only [show 2 + 1 = 3 by omega,
      show 2 * k - 2 + 4 = 2 * k + 1 + 1 by omega,
      show 2 * k - 2 + 2 = 2 * k + 1 - 1 by omega] using
      four_fractional_defect_nonnegative k (by omega)
  · simpa only [hdegree] using hI
  · simpa only [hdegree] using hS
  · simpa only [hdegree] using hpos
  · simpa only [hdegree] using horder
  · simpa only [hdegree] using hbudget
  · simpa only [hdegree, show 2 * k - 2 + 2 = 2 * k + 1 - 1 by omega] using hcell
  · simpa only [hdegree, hresdegree] using hres
  · exact idealGenerationAt_projectivePlane _ (by omega)
  · exact idealGenerationAt_projectivePlane _ (by omega)

/-- The two exceptional quartic edges have the required fractional parameters. -/
theorem quartic_fractional_induction_step (m : ℕ) (hm : m = 5 ∨ m = 10)
    (hquadratic : ∀ p, IdealGenerationAt K (m + 1) 2 p)
    (hcubic : ∀ p, IdealGenerationAt K m 3 p)
    (htrace : ∀ p, IdealGenerationAt K m 4 p) :
    ∀ p, IdealGenerationAt K (m + 1) 4 p := by
  apply fractional_hyperplane_transfer m 1 (by rcases hm with rfl | rfl <;> omega)
  · intro h
    have hdvd := (E_integral_iff (m + 1) 4).mp h
    rcases hm with rfl | rfl <;> norm_num [N, Nat.choose] at hdvd
  · rcases hm with rfl | rfl <;> norm_num [N, Nat.choose]
  · rcases hm with rfl | rfl <;>
      norm_num [fractionalResidualI, fractionalTraceRows, fractionalTraceDefect,
        fractionalTraceRemainder, ambientResidue, N, Nat.choose]
  · rw [lowerCritical_successor_trace (m + 1) 4 (by rcases hm with rfl | rfl <;> omega)]
    rcases hm with rfl | rfl <;>
      norm_num [fractionalResidualS, fractionalTraceRows, fractionalTraceDefect,
        fractionalTraceRemainder, ambientComplementaryResidue, ambientResidue, N, Nat.choose]
  · rw [lowerCritical_successor_trace (m + 1) 4 (by rcases hm with rfl | rfl <;> omega)]
    rcases hm with rfl | rfl <;>
      norm_num [fractionalTraceRows, fractionalTraceDefect, N, Nat.choose]
  · apply scalarInjectionAt_of_idealGenerationAt (by rcases hm with rfl | rfl <;> omega)
      (fractionalResidualSCount (m + 2) 4)
    · rcases hm with rfl | rfl <;>
        norm_num [fractionalResidualSCount, fractionalTraceRows, fractionalTraceDefect,
          upperCritical, E, N, Nat.choose]
    · rcases hm with rfl | rfl <;>
        norm_num [fractionalResidualSCount, fractionalTraceRows, fractionalTraceDefect,
          upperCritical, E, N, Nat.choose]
    · exact hquadratic _
  · exact htrace
  · exact hcubic

/-- The full quartic range follows from quadratic and cubic ideal generation. -/
theorem quartic_range_of_lower_degrees
    (hquadratic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p)
    (hcubic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p)
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
    by_cases hsix : n = 6
    · subst n
      exact quartic_fractional_induction_step 5 (Or.inl rfl)
        (fun p => hquadratic 6 p (by omega)) (fun p => hcubic 5 p (by omega))
        (ih 5 (by omega) (by omega) (by omega))
    by_cases heleven : n = 11
    · subst n
      exact quartic_fractional_induction_step 10 (Or.inr rfl)
        (fun p => hquadratic 11 p (by omega)) (fun p => hcubic 10 p (by omega))
        (ih 10 (by omega) (by omega) (by omega))
    have hn3 : 3 ≤ n := by omega
    have heq : n - 1 + 1 = n := by omega
    obtain ⟨r, hr⟩ := quartic_trace_integral_of_not_exception (n + 1)
      (by omega) (by omega) (by omega) (by omega)
    have htrace : E (n - 1 + 1) (3 + 1) = (r : ℚ) := by
      simpa only [Nat.add_sub_cancel, heq] using hr
    have hG : IdealGenerationAt K (n - 1) (3 + 1)
        (N (n - 1 + 1) (3 + 1) - r) :=
      ih (n - 1) (by omega) (by omega) (by omega) _
    have hprevious : IdealGenerationAt K (n - 1 + 1) 3
        (N (n - 1 + 2) 3 - ⌈hyperplaneResidualRatio (n - 1 + 2) (3 + 1)⌉₊) :=
      hcubic _ _ (by omega)
    have h := integral_hyperplane_transfer_of_maximal_rank (n - 1) 3 r
      (by omega) (by omega) htrace hG hprevious
    simpa only [heq] using h

/-- The higher-degree one-hyperplane range follows by induction on projective dimension. -/
theorem higher_one_hyperplane_range (D : ℕ) (hD : 5 ≤ D)
    (hprevious : ∀ n p, 1 ≤ n → IdealGenerationAt K n (D - 1) p)
    (hsecond : ∀ n p, 1 ≤ n → IdealGenerationAt K n (D - 2) p)
    (n : ℕ) (hn : 1 ≤ n) (hu : n ≤ D * (D - 1)) :
    ∀ p, IdealGenerationAt K n D p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hone : n = 1
    · subst n
      exact idealGenerationAt_projectiveLine_all D (by omega)
    by_cases htwo : n = 2
    · subst n
      exact idealGenerationAt_projectivePlane D (by omega)
    have hn3 : 3 ≤ n := by omega
    have heqn : n - 1 + 1 = n := by omega
    have heqD : D - 1 + 1 = D := by omega
    by_cases hintegral : ∃ r : ℕ, E n D = (r : ℚ)
    · obtain ⟨r, hr⟩ := hintegral
      have htrace : E (n - 1 + 1) (D - 1 + 1) = (r : ℚ) := by
        simpa only [heqn, heqD] using hr
      have hG : IdealGenerationAt K (n - 1) (D - 1 + 1)
          (N (n - 1 + 1) (D - 1 + 1) - r) := by
        rw [heqD]
        exact ih (n - 1) (by omega) (by omega) (by omega) _
      have hprev : IdealGenerationAt K (n - 1 + 1) (D - 1)
          (N (n - 1 + 2) (D - 1) -
            ⌈hyperplaneResidualRatio (n - 1 + 2) (D - 1 + 1)⌉₊) :=
        hprevious _ _ (by omega)
      have h := integral_hyperplane_transfer_of_maximal_rank (n - 1) (D - 1) r
        (by omega) (by omega) htrace hG hprev
      simpa only [heqn, heqD] using h
    · by_cases hthree : n = 3
      · subst n
        by_cases hfive : D = 5
        · subst D
          exact quintic_three_of_quartic (fun p => hprevious 3 p (by omega))
        · obtain ⟨k, hk, hdegree⟩ := four_fractional_degree_parameter D hD hfive hintegral
          subst D
          exact four_fractional_induction_step k hk (fun p => hsecond 3 p (by omega))
      · have heqDegree : D - 3 + 3 = D := by omega
        have hfrac : ¬ ∃ r : ℕ, E (n - 1 + 1) (D - 3 + 3) = (r : ℚ) := by
          simpa only [heqn, heqDegree] using hintegral
        have hbound : n - 1 + 2 ≤ (D - 3 + 3) * (D - 3 + 3 - 1) + 1 := by
          rw [heqDegree]
          omega
        have htop : ∀ p, IdealGenerationAt K (n - 1) (D - 3 + 3) p := by
          rw [heqDegree]
          exact ih (n - 1) (by omega) (by omega) (by omega)
        have hprev : ∀ p, IdealGenerationAt K (n - 1) (D - 3 + 2) p := by
          rw [show D - 3 + 2 = D - 1 by omega]
          exact fun p => hprevious _ p (by omega)
        have hsec : ∀ p, IdealGenerationAt K (n - 1 + 1) (D - 3 + 1) p := by
          rw [heqn, show D - 3 + 1 = D - 2 by omega]
          exact fun p => hsecond n p (by omega)
        have h := higher_fractional_induction_step (n - 1) (D - 3)
          (by omega) (by omega) hbound hfrac htop hprev hsec
        simpa only [heqn, heqDegree] using h

/-- Proposition 6.1 in projective-dimension indexing. -/
theorem one_hyperplane_induction (D : ℕ) (hD : 4 ≤ D)
    (hprevious : ∀ n p, 1 ≤ n → IdealGenerationAt K n (D - 1) p)
    (hsecond : ∀ n p, 1 ≤ n → IdealGenerationAt K n (D - 2) p)
    (n : ℕ) (hn : 1 ≤ n) (hu : n ≤ D * (D - 1)) :
    ∀ p, IdealGenerationAt K n D p := by
  by_cases hf : D = 4
  · subst D
    exact quartic_range_of_lower_degrees hsecond hprevious n hn (by omega)
  · exact higher_one_hyperplane_range D (by omega) hprevious hsecond n hn hu

end IdealGeneration
