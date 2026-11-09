module

public import IdealGeneration.FractionalHyperplaneCounts
public import IdealGeneration.HigherFractionalBounds
public import IdealGeneration.FourVariableFractional

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Natural-number residual counts for fractional hyperplane steps

The rational residual inequalities identify the existing natural counts and
place them in the preceding scalar-postulation cell.
-/

namespace IdealGeneration

/-- Positive rational residuals below the preceding critical value give
positive, ordered natural counts in the required scalar cell. -/
theorem fractionalResidual_counts_spec (n d : ℕ) (hn : 3 ≤ n) (hd : 3 ≤ d)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hpos : 0 < fractionalResidualI n d)
    (hlt : fractionalResidualS n d < E n (d - 2)) :
    (fractionalResidualICount n d : ℚ) = fractionalResidualI n d ∧
      (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d ∧
      1 ≤ fractionalResidualICount n d ∧
      fractionalResidualICount n d ≤ fractionalResidualSCount n d ∧
      fractionalResidualSCount n d ≤ N n (d - 2) - N n (d - 3) ∧
      (fractionalResidualSCount n d : ℚ) ≤ E n (d - 2) := by
  have horder := fractionalResidualI_le_S n d
  have hI := fractionalResidualICount_cast n d hn hdef hpos.le
  have hS := fractionalResidualSCount_cast n d hn hdef (hpos.le.trans horder)
  have hIpositive : (0 : ℚ) < fractionalResidualICount n d := by
    rw [hI]
    exact hpos
  have hIpositiveNat : 0 < fractionalResidualICount n d := by
    exact_mod_cast hIpositive
  have horderQ : (fractionalResidualICount n d : ℚ) ≤ fractionalResidualSCount n d := by
    rw [hI, hS]
    exact horder
  have horderNat : fractionalResidualICount n d ≤ fractionalResidualSCount n d := by
    exact_mod_cast horderQ
  have hwidth := E_le_cell_width n (d - 2) (by omega) (by omega)
  rw [show d - 2 - 1 = d - 3 by omega] at hwidth
  have hmono : N n (d - 3) ≤ N n (d - 2) :=
    N_mono_degree n (by omega) (by omega)
  have hcellQ : (fractionalResidualSCount n d : ℚ) ≤
      ((N n (d - 2) - N n (d - 3) : ℕ) : ℚ) := by
    rw [hS, Nat.cast_sub hmono]
    exact hlt.le.trans hwidth
  have hcell : fractionalResidualSCount n d ≤ N n (d - 2) - N n (d - 3) := by
    exact_mod_cast hcellQ
  refine ⟨hI, hS, by omega, horderNat, hcell, ?_⟩
  rw [hS]
  exact hlt.le

/-- The higher-variable fractional range supplies every natural residual
count requirement for the lower-degree induction. -/
theorem higherFractional_residual_counts_spec (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1) :
    (fractionalResidualICount n d : ℚ) = fractionalResidualI n d ∧
      (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d ∧
      1 ≤ fractionalResidualICount n d ∧
      fractionalResidualICount n d ≤ fractionalResidualSCount n d ∧
      fractionalResidualSCount n d ≤ N n (d - 2) - N n (d - 3) ∧
      (fractionalResidualSCount n d : ℚ) ≤ E n (d - 2) := by
  have hb := higherFractional_residual_bounds n d hn hd hu hfrac
  exact fractionalResidual_counts_spec n d (by omega) (by omega)
    (higherFractional_defect_nonnegative n d (by omega) (by omega) hu)
    hb.1 hb.2.2.1

/-- Odd four-variable fractional steps have the same positive natural
residual counts and preceding-degree scalar-cell bound. -/
theorem four_fractional_residual_counts_spec (k : ℕ) (hk : 3 ≤ k) :
    (fractionalResidualICount 4 (2 * k + 1) : ℚ) = fractionalResidualI 4 (2 * k + 1) ∧
      (fractionalResidualSCount 4 (2 * k + 1) : ℚ) = fractionalResidualS 4 (2 * k + 1) ∧
      1 ≤ fractionalResidualICount 4 (2 * k + 1) ∧
      fractionalResidualICount 4 (2 * k + 1) ≤ fractionalResidualSCount 4 (2 * k + 1) ∧
      fractionalResidualSCount 4 (2 * k + 1) ≤
        N 4 (2 * k + 1 - 2) - N 4 (2 * k + 1 - 3) ∧
      (fractionalResidualSCount 4 (2 * k + 1) : ℚ) ≤ E 4 (2 * k + 1 - 2) := by
  have hb := four_fractional_residual_bounds k hk
  exact fractionalResidual_counts_spec 4 (2 * k + 1) (by decide) (by omega)
    (four_fractional_defect_nonnegative k (by omega)) (by linarith [hb.1]) hb.2.2.1

end IdealGeneration
