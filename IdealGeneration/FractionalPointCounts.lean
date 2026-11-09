module

public import IdealGeneration.FractionalHyperplaneCounts
public import IdealGeneration.HigherFractionalBoundsAux
public import IdealGeneration.PlaneArithmetic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Point-count identities through both fractional hyperplane specializations. -/

namespace IdealGeneration

/-- A nonintegral critical value has consecutive lower and upper counts. -/
theorem fractional_critical_gap (n d : ℕ)
    (hnot : ¬ ∃ r : ℕ, E n d = (r : ℚ)) :
    upperCritical n d = lowerCritical n d + 1 := by
  have hnonneg : 0 ≤ E n d := by unfold E; positivity
  have hlower : (lowerCritical n d : ℚ) ≤ E n d := Nat.floor_le hnonneg
  have hupper : E n d ≤ (upperCritical n d : ℚ) := Nat.le_ceil (E n d)
  have hne : upperCritical n d ≠ lowerCritical n d := by
    intro heq
    apply hnot
    refine ⟨lowerCritical n d, ?_⟩
    rw [heq] at hupper
    exact le_antisymm hupper hlower
  have horder : lowerCritical n d ≤ upperCritical n d := Nat.floor_le_ceil (E n d)
  have hstep := upperCritical_le_lowerCritical_add_one n d
  omega

/-- Apart from the quintic exception, a nonintegral four-variable trace
in degree at least five is an odd degree `2k+1` with `k≥3`. -/
theorem four_fractional_degree_parameter (d : ℕ) (hd : 5 ≤ d) (hne : d ≠ 5)
    (hnot : ¬ ∃ r : ℕ, E 3 d = (r : ℚ)) :
    ∃ k : ℕ, 3 ≤ k ∧ d = 2 * k + 1 := by
  have hodd : d % 2 = 1 := by
    by_contra ho
    have heven : d % 2 = 0 := by omega
    have hd' : d = 2 * (d / 2) := by omega
    apply hnot
    refine ⟨d / 2 + 1, ?_⟩
    rw [E_three]
    have hq : (d : ℚ) = 2 * (d / 2 : ℕ) := by exact_mod_cast hd'
    rw [hq]
    push_cast
    ring
  refine ⟨d / 2, ?_, ?_⟩ <;> omega

/-- The trace floor is at most either ambient critical count. -/
theorem fractional_trace_floor_le_critical (n d : ℕ) :
    lowerCritical (n - 1) d ≤ lowerCritical n d ∧
      lowerCritical (n - 1) d ≤ upperCritical n d := by
  have hl : lowerCritical (n - 1) d ≤ lowerCritical n d :=
    Nat.floor_mono (E_mono_variables d (Nat.sub_le n 1))
  exact ⟨hl, hl.trans (Nat.floor_le_ceil (E n d))⟩

/-- The selected trace and residual points have exactly the required
ambient count. The off-hyperplane count also fits the degree-`d−1`
scalar component used to interpolate after the outer specialization. -/
theorem fractional_point_count_balance (n d r ρ : ℕ)
    (hn : 3 ≤ n) (hd : 2 ≤ d)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hρ : ρ = r + fractionalTraceRows n d + 1 - N (n - 1) (d - 1))
    (hpos : 1 ≤ ρ) (hbound : ρ ≤ N n (d - 2))
    (hτ : lowerCritical (n - 1) d ≤ r) :
    let q₀ := N (n - 1) d - upperCritical (n - 1) d
    let τ := lowerCritical (n - 1) d
    let q₁ := fractionalTraceRows n d
    let z := N n (d - 2) - ρ
    let p := N n d - r
    q₀ + 1 + τ = N (n - 1) d ∧
      z + q₁ + 1 = p - N (n - 1) d ∧
      z + q₁ + 1 + τ = p - q₀ - 1 ∧
      z + q₁ + 1 + τ ≤ N n (d - 1) ∧
      q₀ + 1 + (z + q₁ + 1 + τ) = p := by
  dsimp
  have htraceUpper : upperCritical (n - 1) d ≤ N (n - 1) d :=
    (upperCritical_mem_cell (n - 1) d (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have hpascal := N_pascal n d (by omega) (by omega)
  have hprev := N_pascal n (d - 1) (by omega) (by omega)
  rw [show d - 1 - 1 = d - 2 by omega] at hprev
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- A rational scalar-row budget transfers to the actual surjective count. -/
theorem fractional_scalar_budget_nat (n d : ℕ)
    (hcast : (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d)
    (hbudget : ((n - 1 : ℕ) : ℚ) * fractionalResidualS n d ≤
      (lowerCritical (n - 1) d : ℚ) + fractionalTraceRows n d) :
    (n - 1) * fractionalResidualSCount n d ≤
      lowerCritical (n - 1) d + fractionalTraceRows n d := by
  have hq : ((n - 1 : ℕ) : ℚ) * fractionalResidualSCount n d ≤
      (lowerCritical (n - 1) d : ℚ) + fractionalTraceRows n d := by
    rwa [hcast]
  exact_mod_cast hq

/-- The subtraction in the selected-row dimension is exact for a positive
residual ideal dimension. -/
theorem fractional_selected_count_cast (n d r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r) :
    (((n - 1) * r - (n - 1 - fractionalTraceRemainder n d) : ℕ) : ℚ) =
      ((n - 1 : ℕ) : ℚ) * r - (((n - 1 : ℕ) : ℚ) - fractionalTraceRemainder n d) := by
  have hb := fractionalTraceRemainder_lt n d hn
  have hb' : fractionalTraceRemainder n d ≤ n - 1 := by omega
  have hprod : n - 1 ≤ (n - 1) * r := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n - 1) hr
  have hle : n - 1 - fractionalTraceRemainder n d ≤ (n - 1) * r :=
    (Nat.sub_le _ _).trans hprod
  rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_sub hb']

/-- The selected-row dimensions differ from the prescribed count by the
ordinary and complementary ambient residues, respectively. -/
theorem fractional_inner_row_count_balance (n d : ℕ) (hn : 3 ≤ n)
    (hpos : 1 ≤ fractionalResidualICount n d)
    (horder : fractionalResidualICount n d ≤ fractionalResidualSCount n d)
    (hI : (fractionalResidualICount n d : ℚ) = fractionalResidualI n d)
    (hS : (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d) :
    (n - 1) * fractionalResidualICount n d - (n - 1 - fractionalTraceRemainder n d) +
        ambientResidue n d = fractionalTraceRows n d ∧
      (n - 1) * fractionalResidualSCount n d - (n - 1 - fractionalTraceRemainder n d) =
        fractionalTraceRows n d + ambientComplementaryResidue n d := by
  have hi := fractionalResidualI_row_balance n d (by omega)
  have hs := fractionalResidualS_row_balance n d (by omega)
  rw [← hI] at hi
  rw [← hS] at hs
  constructor
  · have hq : ((((n - 1) * fractionalResidualICount n d -
        (n - 1 - fractionalTraceRemainder n d) : ℕ) : ℚ) + ambientResidue n d) =
        fractionalTraceRows n d := by
      rw [fractional_selected_count_cast n d _ hn hpos]
      linarith
    exact_mod_cast hq
  · have hq : (((n - 1) * fractionalResidualSCount n d -
        (n - 1 - fractionalTraceRemainder n d) : ℕ) : ℚ) =
        (fractionalTraceRows n d : ℚ) + ambientComplementaryResidue n d := by
      rw [fractional_selected_count_cast n d _ hn (hpos.trans horder)]
      exact hs
    exact_mod_cast hq

/-- The inner selected scalar rows are sufficient on the injective side
and independent on the surjective side. -/
theorem fractional_inner_rows_bounds (n d : ℕ) (hn : 3 ≤ n)
    (hpos : 1 ≤ fractionalResidualICount n d)
    (horder : fractionalResidualICount n d ≤ fractionalResidualSCount n d)
    (hI : (fractionalResidualICount n d : ℚ) = fractionalResidualI n d)
    (hS : (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d) :
    (n - 1) * fractionalResidualICount n d - (n - 1 - fractionalTraceRemainder n d) ≤
        fractionalTraceRows n d ∧
      fractionalTraceRows n d ≤
        (n - 1) * fractionalResidualSCount n d - (n - 1 - fractionalTraceRemainder n d) := by
  obtain ⟨hi, hs⟩ := fractional_inner_row_count_balance n d hn hpos horder hI hS
  constructor <;> omega

end IdealGeneration
