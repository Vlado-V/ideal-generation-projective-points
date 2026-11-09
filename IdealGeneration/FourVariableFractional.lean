module

public import IdealGeneration.FourVariableFractionalParameters
public import IdealGeneration.HigherFractionalBounds

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The four-variable odd-degree fractional step in Proposition 6.1. -/

namespace IdealGeneration

/-- The preceding critical value in the four-variable odd-degree step. -/
theorem four_fractional_previous_critical (k : ℕ) (hk : 1 ≤ k) :
    E 4 (2 * k + 1 - 2) = ((2 : ℚ) * k + 1) * (k + 1) / 3 := by
  rw [E_successor_trace_ratio 4 (2 * k + 1 - 2) (by decide)]
  norm_num only [Nat.reduceSub]
  rw [show 2 * k + 1 - 2 + 1 = 2 * k by omega, four_fractional_N_lower]
  push_cast
  ring

/-- There are at least two selected scalar rows for every odd degree at least seven. -/
theorem four_fractional_rows_lower (k : ℕ) (hk : 3 ≤ k) :
    2 ≤ fractionalTraceRows 4 (2 * k + 1) := by
  rw [four_fractional_rows k (by omega)]
  have hmul : 9 ≤ k * k := Nat.mul_le_mul hk hk
  have hquad : 4 ≤ 2 * k * k + k := by nlinarith
  omega

/-- The injective residual is a positive integral dimension. -/
theorem four_fractional_residual_ge_one (k : ℕ) (hk : 3 ≤ k) :
    1 ≤ fractionalResidualI 4 (2 * k + 1) := by
  rw [four_fractional_residualI k (by omega)]
  have ha : (ambientResidue 4 (2 * k + 1) : ℚ) ≤ 1 := by
    rcases four_fractional_residue_cases k with h | h <;> simp [h]
  have hkq : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hmul : (9 : ℚ) ≤ (k : ℚ) * k := by exact_mod_cast Nat.mul_le_mul hk hk
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 3)).2
  nlinarith

/-- The surjective residual is strictly below the preceding critical value. -/
theorem four_fractional_residual_lt (k : ℕ) (hk : 3 ≤ k) :
    fractionalResidualS 4 (2 * k + 1) < E 4 (2 * k + 1 - 2) := by
  rw [four_fractional_residualS k (by omega),
    four_fractional_previous_critical k (by omega)]
  have ha : (ambientComplementaryResidue 4 (2 * k + 1) : ℚ) ≤ 2 := by
    rcases four_fractional_complement_cases k with h | h <;> simp [h]
  have hkq : (3 : ℚ) ≤ k := by exact_mod_cast hk
  apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 3)
  nlinarith

/-- The first trace and selected rows cover the surjective residual conditions. -/
theorem four_fractional_scalar_budget (k : ℕ) (hk : 3 ≤ k) :
    3 * fractionalResidualS 4 (2 * k + 1) ≤
      (lowerCritical 3 (2 * k + 1) : ℚ) + fractionalTraceRows 4 (2 * k + 1) := by
  have hbal := fractionalResidualS_row_balance 4 (2 * k + 1) (by decide)
  rw [four_fractional_remainder k (by omega)] at hbal
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one] at hbal
  have ha : (ambientComplementaryResidue 4 (2 * k + 1) : ℚ) ≤ 2 := by
    rcases four_fractional_complement_cases k with h | h <;> simp [h]
  have htrace : (4 : ℚ) ≤ lowerCritical 3 (2 * k + 1) := by
    rw [four_fractional_tau]
    exact_mod_cast (show 4 ≤ k + 1 by omega)
  linarith

/-- Both residual formulas are integers for the four-variable step. -/
theorem four_fractional_residuals_integral (k : ℕ) (hk : 3 ≤ k) :
    (∃ r : ℤ, fractionalResidualI 4 (2 * k + 1) = r) ∧
      ∃ r : ℤ, fractionalResidualS 4 (2 * k + 1) = r :=
  fractionalResiduals_integral 4 (2 * k + 1) (by decide)
    (four_fractional_defect_nonnegative k (by omega))

/-- The three auxiliary ideal dimensions are `k+2`, `k+1`, and `k`. -/
theorem four_fractional_auxiliary_dimension (k : ℕ) (hk : 1 ≤ k) :
    N 3 (2 * k) = lowerCritical 3 (2 * k + 1) +
      fractionalTraceRows 4 (2 * k + 1) + (k + 2) := by
  rw [four_fractional_N_lower, four_fractional_tau, four_fractional_rows k hk]
  have hpoly : (2 * k + 1) * (k + 1) = 2 * k * k + 3 * k + 1 := by ring
  rw [hpoly]
  have hmul : 1 ≤ k * k := Nat.mul_le_mul hk hk
  have hquad : 2 ≤ 2 * k * k + k := by nlinarith
  omega

/-- All three auxiliary counts lie in the preceding ternary scalar cell. -/
theorem four_fractional_auxiliary_cells (k : ℕ) (hk : 3 ≤ k) :
    ∀ j : ℕ, j ≤ 2 →
      N 3 (2 * k + 1 - 2) ≤
          lowerCritical 3 (2 * k + 1) + fractionalTraceRows 4 (2 * k + 1) + j ∧
        lowerCritical 3 (2 * k + 1) + fractionalTraceRows 4 (2 * k + 1) + j <
          N 3 (2 * k + 1 - 1) := by
  have hdim := four_fractional_auxiliary_dimension k (by omega)
  have hwidth := N_three_cell_width (2 * k) (by omega)
  rw [show 2 * k + 1 - 2 = 2 * k - 1 by omega,
    show 2 * k + 1 - 1 = 2 * k by omega]
  intro j hj
  constructor <;> omega

/-- Both residual dimensions are positive, ordered, and in the preceding
scalar cell for every four-variable odd degree at least seven. -/
theorem four_fractional_residual_bounds (k : ℕ) (hk : 3 ≤ k) :
    1 ≤ fractionalResidualI 4 (2 * k + 1) ∧
      fractionalResidualI 4 (2 * k + 1) ≤ fractionalResidualS 4 (2 * k + 1) ∧
      fractionalResidualS 4 (2 * k + 1) < E 4 (2 * k + 1 - 2) ∧
      E 4 (2 * k + 1 - 2) ≤ (N 3 (2 * k + 1 - 2) : ℚ) := by
  exact ⟨four_fractional_residual_ge_one k hk, fractionalResidualI_le_S 4 (2 * k + 1),
    four_fractional_residual_lt k hk,
    critical_le_trace_component 4 (2 * k + 1 - 2) (by decide) (by omega)⟩

end IdealGeneration
