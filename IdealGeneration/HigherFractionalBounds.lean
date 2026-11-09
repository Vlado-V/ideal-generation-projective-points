module

public import IdealGeneration.FractionalTraceNumerics
public import IdealGeneration.InductionNumerics
public import IdealGeneration.HigherIntegral
public import IdealGeneration.HigherFractionalBoundsAux

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Arithmetic for fractional trace edges in Proposition 6.1. -/

namespace IdealGeneration

/-- Two degree recurrences compare the trace dimensions two degrees apart. -/
theorem N_two_degree_recurrence (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    d * (d + 1) * N (n - 1) (d + 1) =
      (n + d - 2) * (n + d - 1) * N (n - 1) (d - 1) := by
  have h₀ := N_degree_recurrence (n - 1) (d - 1) (by omega)
  have h₁ := N_degree_recurrence (n - 1) d (by omega)
  rw [Nat.sub_add_cancel hd] at h₀
  have ha : n - 1 + (d - 1) = n + d - 2 := by omega
  have hb : n - 1 + d = n + d - 1 := by omega
  rw [ha] at h₀
  rw [hb] at h₁
  calc
    d * (d + 1) * N (n - 1) (d + 1) = d * ((d + 1) * N (n - 1) (d + 1)) := by ring
    _ = d * ((n + d - 1) * N (n - 1) d) := by rw [h₁]
    _ = (n + d - 1) * (d * N (n - 1) d) := by ring
    _ = (n + d - 1) * ((n + d - 2) * N (n - 1) (d - 1)) := by rw [h₀]
    _ = _ := by ring

/-- The factorization underlying equation (6.1). -/
theorem higherFractional_factorization (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hu : n ≤ d * (d - 1) + 1) :
    d * (d + 1) * (n - 1) = (n + d - 2) * (n + d - 1) +
      (n - 2) * (d * (d - 1) + 1 - n) := by
  zify
  simp only [Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub hd,
    Nat.cast_sub hu, Nat.cast_sub (show 2 ≤ n + d by omega),
    Nat.cast_sub (show 1 ≤ n + d by omega), Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The unsigned defect is nonnegative throughout the one-hyperplane range. -/
theorem higherFractional_defect_nonnegative (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hu : n ≤ d * (d - 1) + 1) :
    N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1) := by
  have hf := higherFractional_factorization n d hn hd hu
  have hr := N_two_degree_recurrence n d hn hd
  have hbalance : d * (d + 1) * ((n - 1) * N (n - 1) (d - 1)) =
      d * (d + 1) * N (n - 1) (d + 1) +
        (n - 2) * (d * (d - 1) + 1 - n) * N (n - 1) (d - 1) := by
    calc
      _ = (d * (d + 1) * (n - 1)) * N (n - 1) (d - 1) := by ring
      _ = _ := by rw [hf]; rw [add_mul, ← hr]
  have hmul : d * (d + 1) * N (n - 1) (d + 1) ≤
      d * (d + 1) * ((n - 1) * N (n - 1) (d - 1)) := by omega
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Equation (6.1), with its positive denominator cleared. -/
theorem higherFractional_defect_identity (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hu : n ≤ d * (d - 1) + 1) :
    d * (d + 1) * fractionalTraceDefect n d =
      N (n - 1) (d - 1) * (n - 2) * (d * (d - 1) + 1 - n) := by
  have hf := higherFractional_factorization n d hn hd hu
  have hr := N_two_degree_recurrence n d hn hd
  have hdef := higherFractional_defect_nonnegative n d hn hd hu
  unfold fractionalTraceDefect
  rw [Nat.mul_sub_left_distrib]
  have hbalance : d * (d + 1) * ((n - 1) * N (n - 1) (d - 1)) =
      d * (d + 1) * N (n - 1) (d + 1) +
        N (n - 1) (d - 1) * (n - 2) * (d * (d - 1) + 1 - n) := by
    calc
      _ = (d * (d + 1) * (n - 1)) * N (n - 1) (d - 1) := by ring
      _ = _ := by rw [hf]; rw [add_mul, ← hr]; ring
  omega

/-- A fractional trace cannot occur at the upper endpoint. -/
theorem higherFractional_endpoint_gap (n d : ℕ) (hd : 2 ≤ d)
    (hu : n ≤ d * (d - 1) + 1)
    (hfrac : ¬ ∃ r : ℕ, E (n - 1) d = (r : ℚ)) :
    1 ≤ d * (d - 1) + 1 - n := by
  have hne : n ≠ d * (d - 1) + 1 := by
    intro hn
    subst n
    simpa only [Nat.add_sub_cancel] using
      hfrac (induction_endpoint_trace_integral d hd)
  omega


/-- The trace dimension divided by the number of tangential components is
exactly the preceding ambient critical value. -/
theorem higherFractional_trace_critical_identity (n d : ℕ)
    (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (N (n - 1) (d - 1) : ℚ) = ((n - 1 : ℕ) : ℚ) * E n (d - 2) := by
  rw [E_successor_trace_ratio n (d - 2) hn,
    show d - 2 + 1 = d - 1 by omega]
  have hn0 : ((n - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  field_simp

/-- The selected row count satisfies the upper bound obtained from (6.1). -/
theorem higherFractional_rows_product_upper (n d : ℕ)
    (hn : 3 ≤ n) (hd : 1 ≤ d) (hu : n ≤ d * (d - 1) + 1) :
    d * (d + 1) * fractionalTraceRows n d ≤
      N (n - 1) (d - 1) * (d * (d - 1) + 1 - n) := by
  have hi := higherFractional_defect_identity n d (by omega) hd hu
  have hdiv := fractionalTrace_division n d
  have hbound : (n - 2) * fractionalTraceRows n d ≤ fractionalTraceDefect n d := by omega
  have hmul := Nat.mul_le_mul_left (d * (d + 1)) hbound
  rw [hi] at hmul
  have hmul' : (n - 2) * (d * (d + 1) * fractionalTraceRows n d) ≤
      (n - 2) * (N (n - 1) (d - 1) * (d * (d - 1) + 1 - n)) := by
    nlinarith [hmul]
  exact Nat.le_of_mul_le_mul_left hmul' (by omega)

/-- A quartic scalar component already dominates the required product
once there are at least eight variables in the ambient problem. -/
theorem higherFractional_quartic_product_lower (n : ℕ) (hn : 8 ≤ n) :
    (n - 3) * (n - 2) * (n - 2) ≤ N (n - 1) 4 := by
  have hf := twentyfour_N_quartic (n - 1)
  rw [show n - 1 + 1 = n by omega,
    show n - 1 + 2 = n + 1 by omega,
    show n - 1 + 3 = n + 2 by omega] at hf
  have hfq : 24 * (N (n - 1) 4 : ℚ) =
      ((n : ℚ) - 1) * n * (n + 1) * (n + 2) := by
    have h : 24 * (N (n - 1) 4 : ℚ) =
        ((n - 1 : ℕ) : ℚ) * n * (n + 1) * (n + 2) := by exact_mod_cast hf
    simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using h
  have hnq : (8 : ℚ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ ((n : ℚ) - 8) ^ 4 + 10 * ((n : ℚ) - 8) ^ 3 +
      23 * ((n : ℚ) - 8) ^ 2 + 110 * ((n : ℚ) - 8) + 720 := by positivity
  have hq : ((n : ℚ) - 3) * (n - 2) * (n - 2) ≤ N (n - 1) 4 := by
    nlinarith [hp, hfq]
  have hcast : (((n - 3) * (n - 2) * (n - 2) : ℕ) : ℚ) ≤ N (n - 1) 4 := by
    simpa only [Nat.cast_mul, Nat.cast_sub (show 3 ≤ n by omega),
      Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat] using hq
  exact_mod_cast hcast

/-- The first inequality in (6.2) for every fractional edge. -/
theorem higherFractional_trace_product_lower (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hgap : 1 ≤ d * (d - 1) + 1 - n) :
    d * (d + 1) * (n - 2) ≤
      N (n - 1) (d - 1) * (d * (d - 1) + 1 - n) := by
  by_cases hsmall : n ≤ d + 2
  · have hbase : d * (d + 1) ≤ N (n - 1) (d - 1) := by
      have h := N_integral_rounding_margin (n - 1) (d - 1) (by omega) (by omega)
      simpa only [show d - 1 + 1 = d by omega,
        show d - 1 + 2 = d + 1 by omega] using h
    have hfour : d * 4 ≤ d * (d - 1) :=
      Nat.mul_le_mul_left d (by omega)
    have hc : n - 2 ≤ d * (d - 1) + 1 - n := by omega
    exact Nat.mul_le_mul hbase hc
  · have hnlarge : d + 3 ≤ n := by omega
    have hdegree : N (n - 1) 4 ≤ N (n - 1) (d - 1) :=
      N_mono_degree (n - 1) (by omega) (by omega)
    have hcoef : d * (d + 1) ≤ (n - 3) * (n - 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc
      d * (d + 1) * (n - 2) ≤ (n - 3) * (n - 2) * (n - 2) :=
        Nat.mul_le_mul_right _ hcoef
      _ ≤ N (n - 1) 4 := higherFractional_quartic_product_lower n (by omega)
      _ ≤ N (n - 1) (d - 1) := hdegree
      _ ≤ N (n - 1) (d - 1) * (d * (d - 1) + 1 - n) := by
        simpa using Nat.mul_le_mul_left (N (n - 1) (d - 1)) hgap

/-- A unit gap between the two trace critical counts excludes integral trace. -/
theorem higherFractional_not_integral (n d : ℕ)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1) :
    ¬ ∃ r : ℕ, E (n - 1) d = (r : ℚ) := by
  rintro ⟨r, hr⟩
  simp [upperCritical, lowerCritical, hr] at hfrac

/-- The row count in every fractional edge is at least the trace fiber dimension. -/
theorem higherFractional_rows_lower (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1) :
    n - 2 ≤ fractionalTraceRows n d := by
  have hgap := higherFractional_endpoint_gap n d (by omega) hu
    (higherFractional_not_integral n d hfrac)
  have hp := higherFractional_trace_product_lower n d hn hd hu hgap
  have hi := higherFractional_defect_identity n d (by omega) (by omega) hu
  have hmul := Nat.mul_le_mul_right (n - 2) hp
  have hmul' : d * (d + 1) * ((n - 2) * (n - 2)) ≤
      d * (d + 1) * fractionalTraceDefect n d := by
    rw [hi]
    nlinarith [hmul]
  have hsquare : (n - 2) * (n - 2) ≤ fractionalTraceDefect n d :=
    Nat.le_of_mul_le_mul_left hmul' (by positivity)
  unfold fractionalTraceRows
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hsquare

/-- The preceding critical dimension has the margin needed to absorb two rows. -/
theorem higherFractional_previous_critical_lower (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) :
    (d : ℚ) + 1 ≤ E n (d - 2) := by
  have hmono : E 5 (d - 2) ≤ E n (d - 2) := E_mono_variables (d - 2) hn
  have hfive : E 5 (d - 2) = (d : ℚ) * (d + 1) * (d + 2) / 24 := by
    rw [E_five_formula, Nat.cast_sub (show 2 ≤ d by omega)]
    norm_num
    ring
  have hdq : (5 : ℚ) ≤ d := by exact_mod_cast hd
  have hc : (24 : ℚ) ≤ (d : ℚ) * (d + 2) := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hc (show (0 : ℚ) ≤ (d : ℚ) + 1 by positivity)
  apply le_trans ?_ hmono
  rw [hfive]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 24)).2
  nlinarith

/-- The surjective residual lies strictly on the injective side of the
preceding-degree critical value. -/
theorem higherFractional_residual_lt (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1) :
    fractionalResidualS n d < E n (d - 2) := by
  let A : ℚ := (n - 1 : ℕ)
  let C : ℚ := (d * (d + 1) : ℕ)
  let c : ℚ := (d * (d - 1) + 1 - n : ℕ)
  let e : ℚ := E n (d - 2)
  have hA : 0 < A := by dsimp [A]; exact_mod_cast (show 0 < n - 1 by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : (N (n - 1) (d - 1) : ℚ) = A * e :=
    higherFractional_trace_critical_identity n d (by omega) (by omega)
  have hqupper : C * fractionalTraceRows n d ≤ A * e * c := by
    have h := higherFractional_rows_product_upper n d (by omega) (by omega) hu
    have hq : C * fractionalTraceRows n d ≤ (N (n - 1) (d - 1) : ℚ) * c := by
      dsimp [C, c]
      exact_mod_cast h
    rwa [hM] at hq
  have hdelta : C - c = 2 * (d : ℚ) + n - 1 := by
    dsimp [C, c]
    rw [Nat.cast_sub hu]
    push_cast
    rw [Nat.cast_sub (show 1 ≤ d by omega)]
    norm_num
    ring
  have hdeltaLower : 2 * (d : ℚ) ≤ C - c := by
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have heLower : (d : ℚ) + 1 ≤ e := higherFractional_previous_critical_lower n d hn hd
  have hdecay : 2 * C ≤ e * (C - c) := by
    have hp := mul_le_mul heLower hdeltaLower (show (0 : ℚ) ≤ 2 * (d : ℚ) by positivity)
      (show (0 : ℚ) ≤ e by linarith)
    calc
      2 * C = ((d : ℚ) + 1) * (2 * (d : ℚ)) := by
        dsimp [C]
        push_cast
        ring
      _ ≤ e * (C - c) := hp
  have hgap : A * e * c + 2 * A * C ≤ A * e * C := by
    have h := mul_le_mul_of_nonneg_left hdecay (le_of_lt hA)
    nlinarith [h]
  have hbal : A * fractionalResidualS n d < fractionalTraceRows n d + 2 * A := by
    have h := fractionalResidualS_row_balance n d (by omega)
    have ha : (ambientComplementaryResidue n d : ℚ) < A := by
      dsimp [A]
      exact_mod_cast (Nat.mod_lt (n - 1 - ambientResidue n d) (by omega : 0 < n - 1))
    have hb : (0 : ℚ) ≤ fractionalTraceRemainder n d := by positivity
    change A * fractionalResidualS n d - (A - fractionalTraceRemainder n d) =
      (fractionalTraceRows n d : ℚ) + ambientComplementaryResidue n d at h
    linarith
  have hmul := mul_lt_mul_of_pos_left hbal hC
  have hresult : (C * A) * fractionalResidualS n d < (C * A) * e := by
    nlinarith [hmul, hqupper, hgap]
  exact (mul_lt_mul_iff_right₀ (mul_pos hC hA)).mp hresult

/-- The ambient critical dimension fits into the scalar trace component. -/
theorem critical_le_trace_component (n e : ℕ) (hn : 2 ≤ n) (he : 1 ≤ e) :
    E n e ≤ (N (n - 1) e : ℚ) := by
  have hw := E_le_cell_width n e hn he
  rw [N_pascal n e (by omega) he, Nat.cast_add] at hw
  linarith

/-- Both residual dimensions are positive and belong to the required
preceding-degree scalar cell. -/
theorem higherFractional_residual_bounds (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1) :
    0 < fractionalResidualI n d ∧
      fractionalResidualI n d ≤ fractionalResidualS n d ∧
      fractionalResidualS n d < E n (d - 2) ∧
      E n (d - 2) ≤ (N (n - 1) (d - 2) : ℚ) := by
  exact ⟨fractionalResidualI_pos n d (by omega) (higherFractional_rows_lower n d hn hd hu hfrac),
    fractionalResidualI_le_S n d, higherFractional_residual_lt n d hn hd hu,
    critical_le_trace_component n (d - 2) (by omega) (by omega)⟩

/-- The first trace and the selected scalar rows cover the surjective residual. -/
theorem higherFractional_scalar_budget (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) :
    ((n - 1 : ℕ) : ℚ) * fractionalResidualS n d ≤
      (lowerCritical (n - 1) d : ℚ) + fractionalTraceRows n d :=
  fractionalResidualS_scalar_budget n d (lowerCritical (n - 1) d) (by omega)
    (higherFractional_trace_rows_lower n d hn hd)

/-- Both residual dimensions in the higher fractional range are integers. -/
theorem higherFractional_residuals_integral (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1) :
    (∃ r : ℤ, fractionalResidualI n d = r) ∧
      ∃ r : ℤ, fractionalResidualS n d = r :=
  fractionalResiduals_integral n d (by omega)
    (higherFractional_defect_nonnegative n d (by omega) (by omega) hu)

/-- The three auxiliary counts satisfy their scalar cells throughout the
higher fractional range. -/
theorem higherFractional_auxiliary_cells (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1) :
    ∀ j : ℕ, j ≤ 2 →
      N (n - 1) (d - 2) ≤ lowerCritical (n - 1) d + fractionalTraceRows n d + j ∧
        lowerCritical (n - 1) d + fractionalTraceRows n d + j < N (n - 1) (d - 1) :=
  higherFractional_auxiliary_point_cell n d hn hd hfrac
    (higherFractional_defect_nonnegative n d (by omega) (by omega) hu)

end IdealGeneration
