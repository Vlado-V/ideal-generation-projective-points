module

public import IdealGeneration.FractionalTraceNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Trace dimension counts in the two-level hyperplane construction

The formulas here identify the natural-number kernel dimensions used by
interpolation, including the truncation at zero after one further point.
-/

namespace IdealGeneration

/-- The first partial trace has dimension strictly below the trace-fiber rank. -/
theorem fractionalTopTraceDimension_lt (n d : ℕ) (hn : 3 ≤ n) :
    fractionalTopTraceDimension n d < n - 2 := by
  unfold fractionalTopTraceDimension ambientComplementaryResidue
  have hs : n - 1 - 1 = n - 2 := by omega
  rw [hs]
  exact Nat.mod_lt _ (by omega)

/-- The first trace count and its remaining dimension reconstruct the Euler source. -/
theorem fractional_top_dimension_balance (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    (n - 1) * N (n - 1) d = N (n - 1) (d + 1) +
      (n - 2) * (N (n - 1) d - upperCritical (n - 1) d) +
      fractionalTopTraceDimension n d := by
  have hcrit := upperCritical_residue_identity (n - 1) d (by omega)
  have hs : n - 1 - 1 = n - 2 := by omega
  rw [hs] at hcrit
  change (n - 2) * upperCritical (n - 1) d =
    N (n - 2) (d + 1) + fractionalTopTraceDimension n d at hcrit
  have hpascal := N_pascal (n - 1) (d + 1) (by omega) (by omega)
  rw [hs, Nat.add_sub_cancel] at hpascal
  have hupper : upperCritical (n - 1) d ≤ N (n - 1) d :=
    (upperCritical_mem_cell (n - 1) d (by omega) hd).2.trans (Nat.sub_le _ _)
  have hsum : N (n - 1) d - upperCritical (n - 1) d +
      upperCritical (n - 1) d = N (n - 1) d := Nat.sub_add_cancel hupper
  have hcoef : n - 1 = (n - 2) + 1 := by omega
  have hmult := congrArg (fun x : ℕ => (n - 2) * x) hsum
  rw [Nat.mul_add] at hmult
  have hc := congrArg (fun x : ℕ => x * N (n - 1) d) hcoef
  rw [Nat.add_mul, Nat.one_mul] at hc
  rw [hc]
  omega

/-- The initial critical trace has the stated `b₀`-dimensional kernel. -/
theorem fractional_top_expected_dimension (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    ((n - 1) * N (n - 1) d - N (n - 1) (d + 1)) -
      (n - 2) * (N (n - 1) d - upperCritical (n - 1) d) =
      fractionalTopTraceDimension n d := by
  have h := fractional_top_dimension_balance n d hn hd
  omega

/-- One further point kills the initial critical trace kernel. -/
theorem fractional_top_after_one (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    ((n - 1) * N (n - 1) d - N (n - 1) (d + 1)) -
      (n - 2) * (N (n - 1) d - upperCritical (n - 1) d + 1) = 0 := by
  have h := fractional_top_dimension_balance n d hn hd
  have hb := fractionalTopTraceDimension_lt n d hn
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The initial trace source fits into the condition space after its extra point. -/
theorem fractional_top_condition_bound (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    (n - 1) * N (n - 1) d - N (n - 1) (d + 1) ≤
      (n - 2) * (N (n - 1) d - upperCritical (n - 1) d + 1) := by
  have h := fractional_top_after_one n d hn hd
  exact Nat.sub_eq_zero_iff_le.mp h

/-- The rational defect identity gives an exact natural-number source decomposition. -/
theorem fractional_inner_dimension_balance (n d : ℕ) (hn : 3 ≤ n)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    (n - 1) * N (n - 1) (d - 1) = N (n - 1) d +
      (n - 2) * (lowerCritical (n - 1) d + fractionalTraceRows n d) +
      (n - 2 - fractionalTopTraceDimension n d) + fractionalTraceRemainder n d := by
  have h := fractionalTrace_dimension_identity n d hn hfrac hdef
  have hrows : ((n - 2 : ℕ) : ℚ) * fractionalTraceRows n d +
      fractionalTraceRemainder n d = (fractionalTraceDefect n d : ℚ) := by
    exact_mod_cast fractionalTrace_division n d
  have hb := fractionalTopTraceDimension_lt n d hn
  have hpartial : ((n - 2 - fractionalTopTraceDimension n d : ℕ) : ℚ) =
      ((n - 2 : ℕ) : ℚ) - fractionalTopTraceDimension n d := by
    rw [Nat.cast_sub (by omega)]
  have hq : (((n - 1) * N (n - 1) (d - 1) : ℕ) : ℚ) =
      ((N (n - 1) d +
        (n - 2) * (lowerCritical (n - 1) d + fractionalTraceRows n d) +
        (n - 2 - fractionalTopTraceDimension n d) + fractionalTraceRemainder n d : ℕ) : ℚ) := by
    push_cast
    rw [hpartial]
    nlinarith [h, hrows]
  exact_mod_cast hq

/-- The lower trace and partial condition leave exactly the remainder `b₁`. -/
theorem fractional_inner_expected_dimension (n d : ℕ) (hn : 3 ≤ n)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    ((n - 1) * N (n - 1) (d - 1) - N (n - 1) d) -
      (n - 2) * (lowerCritical (n - 1) d + fractionalTraceRows n d) -
      (n - 2 - fractionalTopTraceDimension n d) = fractionalTraceRemainder n d := by
  have h := fractional_inner_dimension_balance n d hn hfrac hdef
  omega

/-- The lower trace conditions are independent at their stated expected dimension. -/
theorem fractional_inner_condition_bound (n d : ℕ) (hn : 3 ≤ n)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    (n - 2) * (lowerCritical (n - 1) d + fractionalTraceRows n d) +
      (n - 2 - fractionalTopTraceDimension n d) ≤
      (n - 1) * N (n - 1) (d - 1) - N (n - 1) d := by
  have h := fractional_inner_dimension_balance n d hn hfrac hdef
  omega

/-- One more lower-level trace point kills the remaining partial-trace kernel. -/
theorem fractional_inner_after_one (n d : ℕ) (hn : 3 ≤ n)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    ((n - 1) * N (n - 1) (d - 1) - N (n - 1) d) -
      (n - 2) * (lowerCritical (n - 1) d + fractionalTraceRows n d + 1) -
      (n - 2 - fractionalTopTraceDimension n d) = 0 := by
  have h := fractional_inner_dimension_balance n d hn hfrac hdef
  have hb := fractionalTraceRemainder_lt n d hn
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The injective residual ideal dimension as an actual natural-number count. -/
noncomputable def fractionalResidualICount (n d : ℕ) : ℕ :=
  lowerCritical n d + fractionalTraceRows n d + 1 - N (n - 1) (d - 1)

/-- The surjective residual ideal dimension as an actual natural-number count. -/
noncomputable def fractionalResidualSCount (n d : ℕ) : ℕ :=
  upperCritical n d + fractionalTraceRows n d + 1 - N (n - 1) (d - 1)

/-- Nonnegativity identifies the natural injective count with the rational formula. -/
theorem fractionalResidualICount_cast (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hnonneg : 0 ≤ fractionalResidualI n d) :
    (fractionalResidualICount n d : ℚ) = fractionalResidualI n d := by
  have heq := fractionalResidualI_eq n d hn hdef
  have hleq : (N (n - 1) (d - 1) : ℚ) ≤
      ((lowerCritical n d + fractionalTraceRows n d + 1 : ℕ) : ℚ) := by
    push_cast
    linarith
  have hle : N (n - 1) (d - 1) ≤ lowerCritical n d + fractionalTraceRows n d + 1 := by
    exact_mod_cast hleq
  unfold fractionalResidualICount
  rw [Nat.cast_sub hle]
  push_cast
  linarith

/-- Nonnegativity identifies the natural surjective count with the rational formula. -/
theorem fractionalResidualSCount_cast (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hnonneg : 0 ≤ fractionalResidualS n d) :
    (fractionalResidualSCount n d : ℚ) = fractionalResidualS n d := by
  have heq := fractionalResidualS_eq n d hn hdef
  have hleq : (N (n - 1) (d - 1) : ℚ) ≤
      ((upperCritical n d + fractionalTraceRows n d + 1 : ℕ) : ℚ) := by
    push_cast
    linarith
  have hle : N (n - 1) (d - 1) ≤ upperCritical n d + fractionalTraceRows n d + 1 := by
    exact_mod_cast hleq
  unfold fractionalResidualSCount
  rw [Nat.cast_sub hle]
  push_cast
  linarith

/-- The lower bound on the rational injective dimension gives a positive actual count. -/
theorem fractionalResidualICount_pos (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hpos : 1 ≤ fractionalResidualI n d) : 1 ≤ fractionalResidualICount n d := by
  have heq := fractionalResidualICount_cast n d hn hdef (by linarith)
  have hq : (1 : ℚ) ≤ fractionalResidualICount n d := by rw [heq]; exact hpos
  exact_mod_cast hq

/-- The lower bound on the rational surjective dimension gives a positive actual count. -/
theorem fractionalResidualSCount_pos (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hpos : 1 ≤ fractionalResidualS n d) : 1 ≤ fractionalResidualSCount n d := by
  have heq := fractionalResidualSCount_cast n d hn hdef (by linarith)
  have hq : (1 : ℚ) ≤ fractionalResidualSCount n d := by rw [heq]; exact hpos
  exact_mod_cast hq

end IdealGeneration
