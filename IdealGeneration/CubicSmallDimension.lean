module

public import IdealGeneration.FractionalHyperplaneTransfer
public import IdealGeneration.IntegralHyperplane
public import IdealGeneration.InductionNumerics
public import IdealGeneration.QuarticRange

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The low-dimensional cubic cases

The fractional edges in four and six variables have a one-dimensional
linear residual ideal. The integral edges in five and seven variables use
quadratic injection on the appropriate side of the critical value.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K]

/-- A rank-one linear residual ideal gives a generic injective multiplication map. -/
theorem scalarInjectionAt_linear_rankOne (n : ℕ) (hn : 1 ≤ n) : ScalarInjectionAt K n 1 1 := by
  obtain ⟨Δ, hΔ, hgood⟩ := generic_pointHilbertFunction (K := K) hn n
  have hcount : N (n + 1) 1 - 1 = n := by simp
  unfold ScalarInjectionAt
  rw [hcount]
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost⟩ := hgood a ha
  have hscalar : pointHilbertFunction K a 1 = n := by
    have h := hpost 1
    rw [← N_chart n 1, N_one_degree, min_eq_right (Nat.le_succ n)] at h
    exact h
  have hdim : finrank K (pointDegreePiece K a 1) = 1 := by
    rw [pointDegreePiece_finrank a (by simpa only [N_one_degree, min_eq_right (Nat.le_succ n)] using hscalar),
      N_one_degree]
    omega
  exact ⟨pointEvaluation_surjective_of_hilbert_eq a hscalar,
    pointMultiplication_injective_of_finrank_one a hdim, hdim⟩

/-- The two small fractional cubic edges use only a rank-one linear residual. -/
theorem cubic_fractional_small (m : ℕ) (hm : m = 2 ∨ m = 4)
    (hquadratic : ∀ p, IdealGenerationAt K m 2 p)
    (htrace : ∀ p, IdealGenerationAt K m 3 p) :
    ∀ p, IdealGenerationAt K (m + 1) 3 p := by
  apply fractional_hyperplane_transfer m 0 (by rcases hm with rfl | rfl <;> omega)
  · intro h
    have hdvd := (E_integral_iff (m + 1) 3).mp h
    rcases hm with rfl | rfl <;> norm_num [N, Nat.choose] at hdvd
  · rcases hm with rfl | rfl <;> norm_num [N, Nat.choose]
  · rcases hm with rfl | rfl <;>
      norm_num [fractionalResidualI, fractionalTraceRows, fractionalTraceDefect,
        fractionalTraceRemainder, ambientResidue, N, Nat.choose]
  · rw [lowerCritical_successor_trace (m + 1) 3 (by rcases hm with rfl | rfl <;> omega)]
    rcases hm with rfl | rfl <;>
      norm_num [fractionalResidualS, fractionalTraceRows, fractionalTraceDefect,
        fractionalTraceRemainder, ambientComplementaryResidue, ambientResidue, N, Nat.choose]
  · rw [lowerCritical_successor_trace (m + 1) 3 (by rcases hm with rfl | rfl <;> omega)]
    rcases hm with rfl | rfl <;>
      norm_num [fractionalTraceRows, fractionalTraceDefect, N, Nat.choose]
  · have hr : fractionalResidualSCount (m + 2) 3 = 1 := by
      rcases hm with rfl | rfl <;>
        norm_num [fractionalResidualSCount, fractionalTraceRows, fractionalTraceDefect,
          upperCritical, E, N, Nat.choose]
    change ScalarInjectionAt K (m + 1) 1 (fractionalResidualSCount (m + 2) 3)
    rw [hr]
    exact scalarInjectionAt_linear_rankOne (m + 1) (by omega)
  · exact htrace
  · exact hquadratic

/-- The five-variable cubic edge has an integral trace and four quadratic residual equations. -/
theorem cubic_five_variables
    (hquadratic : ∀ p, IdealGenerationAt K 4 2 p)
    (htrace : ∀ p, IdealGenerationAt K 3 3 p) :
    ∀ p, IdealGenerationAt K 4 3 p := by
  apply integral_hyperplane_transfer 3 2 5 (by decide)
  · norm_num [E, N, Nat.choose]
  · exact htrace _
  · have hc : ⌈hyperplaneResidualRatio 5 3⌉₊ = 4 := by
      apply (Nat.ceil_eq_iff (by decide : (4 : ℕ) ≠ 0)).2
      norm_num [hyperplaneResidualRatio, N, Nat.choose]
    change ScalarInjectionAt K 4 2 ⌈hyperplaneResidualRatio 5 3⌉₊
    rw [hc]
    exact scalarInjectionAt_of_idealGenerationAt (by decide) 4
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquadratic _)

/-- The seven-variable cubic edge has an integral trace and seven quadratic residual equations. -/
theorem cubic_seven_variables
    (hquadratic : ∀ p, IdealGenerationAt K 6 2 p)
    (htrace : ∀ p, IdealGenerationAt K 5 3 p) :
    ∀ p, IdealGenerationAt K 6 3 p := by
  apply integral_hyperplane_transfer 5 2 14 (by decide)
  · norm_num [E, N, Nat.choose]
  · exact htrace _
  · have hc : ⌈hyperplaneResidualRatio 7 3⌉₊ = 7 := by
      apply (Nat.ceil_eq_iff (by decide : (7 : ℕ) ≠ 0)).2
      norm_num [hyperplaneResidualRatio, N, Nat.choose]
    change ScalarInjectionAt K 6 2 ⌈hyperplaneResidualRatio 7 3⌉₊
    rw [hc]
    exact scalarInjectionAt_of_idealGenerationAt (by decide) 7
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquadratic _)

/-- Cubic ideal generation through seven variables follows from the two needed quadratic cases. -/
theorem cubic_small_dimension_of_quadratic
    (hquadratic₄ : ∀ p, IdealGenerationAt K 4 2 p)
    (hquadratic₆ : ∀ p, IdealGenerationAt K 6 2 p)
    (n : ℕ) (hn : 1 ≤ n) (hle : n ≤ 6) :
    ∀ p, IdealGenerationAt K n 3 p := by
  have h₃ : ∀ p, IdealGenerationAt K 3 3 p :=
    cubic_fractional_small 2 (Or.inl rfl)
      (idealGenerationAt_projectivePlane 2 (by decide))
      (idealGenerationAt_projectivePlane 3 (by decide))
  have h₄ := cubic_five_variables hquadratic₄ h₃
  have h₅ := cubic_fractional_small 4 (Or.inr rfl) hquadratic₄ h₄
  have h₆ := cubic_seven_variables hquadratic₆ h₅
  interval_cases n
  · exact idealGenerationAt_projectiveLine_all 3 (by decide)
  · exact idealGenerationAt_projectivePlane 3 (by decide)
  · exact h₃
  · exact h₄
  · exact h₅
  · exact h₆

/-- The eight-variable cubic edge has an integral trace. -/
theorem cubic_eight_variables
    (hquadratic : ∀ p, IdealGenerationAt K 7 2 p)
    (htrace : ∀ p, IdealGenerationAt K 6 3 p) :
    ∀ p, IdealGenerationAt K 7 3 p := by
  apply integral_hyperplane_transfer 6 2 21 (by decide)
  · norm_num [E, N, Nat.choose]
  · exact htrace _
  · have hc : ⌈hyperplaneResidualRatio 8 3⌉₊ = 9 := by
      apply (Nat.ceil_eq_iff (by decide : (9 : ℕ) ≠ 0)).2
      norm_num [hyperplaneResidualRatio, N, Nat.choose]
    change ScalarInjectionAt K 7 2 ⌈hyperplaneResidualRatio 8 3⌉₊
    rw [hc]
    exact scalarInjectionAt_of_idealGenerationAt (by decide) 9
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquadratic _)

/-- The nine-variable cubic edge has an integral trace. -/
theorem cubic_nine_variables
    (hquadratic : ∀ p, IdealGenerationAt K 8 2 p)
    (htrace : ∀ p, IdealGenerationAt K 7 3 p) :
    ∀ p, IdealGenerationAt K 8 3 p := by
  apply integral_hyperplane_transfer 7 2 30 (by decide)
  · norm_num [E, N, Nat.choose]
  · exact htrace _
  · have hc : ⌈hyperplaneResidualRatio 9 3⌉₊ = 12 := by
      apply (Nat.ceil_eq_iff (by decide : (12 : ℕ) ≠ 0)).2
      norm_num [hyperplaneResidualRatio, N, Nat.choose]
    change ScalarInjectionAt K 8 2 ⌈hyperplaneResidualRatio 9 3⌉₊
    rw [hc]
    exact scalarInjectionAt_of_idealGenerationAt (by decide) 12
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquadratic _)

/-- The eleven-variable cubic edge has an integral trace. -/
theorem cubic_eleven_variables
    (hquadratic : ∀ p, IdealGenerationAt K 10 2 p)
    (htrace : ∀ p, IdealGenerationAt K 9 3 p) :
    ∀ p, IdealGenerationAt K 10 3 p := by
  apply integral_hyperplane_transfer 9 2 55 (by decide)
  · norm_num [E, N, Nat.choose]
  · exact htrace _
  · have hc : ⌈hyperplaneResidualRatio 11 3⌉₊ = 17 := by
      apply (Nat.ceil_eq_iff (by decide : (17 : ℕ) ≠ 0)).2
      norm_num [hyperplaneResidualRatio, N, Nat.choose]
    change ScalarInjectionAt K 10 2 ⌈hyperplaneResidualRatio 11 3⌉₊
    rw [hc]
    exact scalarInjectionAt_of_idealGenerationAt (by decide) 17
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquadratic _)

/-- The cubic cases through nine variables follow from quadratic ideal generation. -/
theorem cubic_through_nine_variables_of_quadratic
    (hquadratic : ∀ n, 1 ≤ n → n ≤ 8 → ∀ p, IdealGenerationAt K n 2 p)
    (n : ℕ) (hn : 1 ≤ n) (hle : n ≤ 8) :
    ∀ p, IdealGenerationAt K n 3 p := by
  have hsmall := cubic_small_dimension_of_quadratic
    (hquadratic 4 (by decide) (by decide)) (hquadratic 6 (by decide) (by decide))
  have h₇ := cubic_eight_variables (hquadratic 7 (by decide) (by decide))
    (hsmall 6 (by decide) (by decide))
  have h₈ := cubic_nine_variables (hquadratic 8 (by decide) (by decide)) h₇
  by_cases h : n ≤ 6
  · exact hsmall n hn h
  · interval_cases n
    · exact h₇
    · exact h₈

end IdealGeneration
