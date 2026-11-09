module

public import IdealGeneration.TwoNormalFractionalNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Count budgets for the common marked rank conditions -/

namespace IdealGeneration.TwoNormalFractional
set_option maxHeartbeats 1000000

/-- The number of trace rows dominates each slice code dimension, and the
residual pair has at least as many parameters as the two scalar groups. -/
theorem fractional_marked_budgets (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    m * (N (m + 1) (D - 1) - sliceCount m D) ≤ tracePointCount m D ∧
      2 * sliceCount m D ≤ m * residualCount m D r +
        (N (m + 2) (D - 1) - offSlicePointCount m D r) := by
  have hm₁ : 1 ≤ m := by omega
  have hcasts := actualPointCounts_cast m D r hD hm hr
  have hb : sliceCount m D ≤ N (m + 1) (D - 1) :=
    (sliceCount_margins m D hD hm).2.1.le.trans
      (TwoNormalIntegral.middle_lt_sliceWidth m D hD).le
  have hq : offSlicePointCount m D r ≤ N (m + 2) (D - 2) := by
    exact_mod_cast (show (offSlicePointCount m D r : ℚ) ≤ N (m + 2) (D - 2) by
      rw [hcasts.2.2.1]
      exact (offSlicePointCountQ_bounds m D r hD hm hr).2.le)
  have hPascal : N (m + 2) (D - 1) = N (m + 1) (D - 1) + N (m + 2) (D - 2) := by
    exact (TwoNormalIntegral.scalar_count_decomposition m D (by omega)).2
  have hres : N (m + 2) (D - 1) - offSlicePointCount m D r =
      N (m + 1) (D - 1) + residualCount m D r := by
    change N (m + 2) (D - 1) - offSlicePointCount m D r =
      N (m + 1) (D - 1) + (N (m + 2) (D - 2) - offSlicePointCount m D r)
    omega
  constructor
  · have h := slice_cokernel_identity m D hm₁ (by omega)
    have hpos := (sliceCokernel_bounds m D hm₁).1
    exact_mod_cast (show ((m * (N (m + 1) (D - 1) - sliceCount m D) : ℕ) : ℚ) ≤
      tracePointCount m D by
        rw [Nat.cast_mul, Nat.cast_sub hb, hcasts.1]
        linarith)
  · rw [hres, show m * residualCount m D r + (N (m + 1) (D - 1) + residualCount m D r) =
      N (m + 1) (D - 1) + (m + 1) * residualCount m D r by ring]
    have h := normalKernelDimension_pos m D r hm₁ (by omega) hr
    unfold normalKernelDimension at h
    rw [← hcasts.2.2.2] at h
    exact_mod_cast (show ((2 * sliceCount m D : ℕ) : ℚ) ≤
      ((N (m + 1) (D - 1) + (m + 1) * residualCount m D r : ℕ) : ℚ) by
      push_cast
      linarith)

end IdealGeneration.TwoNormalFractional
