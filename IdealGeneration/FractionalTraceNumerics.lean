module

public import IdealGeneration.IntegralTraceNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Arithmetic for the two-level fractional hyperplane transfer. -/

namespace IdealGeneration

/-- The ambient critical value expressed using the next trace degree. -/
theorem E_successor_trace_ratio (n d : ℕ) (hn : 2 ≤ n) :
    E n d = (N (n - 1) (d + 1) : ℚ) / (n - 1 : ℕ) := by
  have h : ((n - 1 : ℕ) : ℚ) * N n d =
      ((d : ℚ) + 1) * N (n - 1) (d + 1) := by
    exact_mod_cast N_cross_hyperplane n (d + 1) hn (by omega)
  have hn0 : ((n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  unfold E
  apply (div_eq_div_iff (by positivity) hn0).2
  nlinarith [h]

/-- Euclidean division computes the lower critical count without rational rounding. -/
theorem lowerCritical_successor_trace (n d : ℕ) (hn : 2 ≤ n) :
    lowerCritical n d = N (n - 1) (d + 1) / (n - 1) := by
  unfold lowerCritical
  rw [E_successor_trace_ratio n d hn]
  exact Rat.natFloor_natCast_div_natCast _ _

/-- The complementary residue measures the extra amount in ceiling division. -/
theorem mul_natCeil_div (a b : ℕ) (hb : 0 < b) :
    b * ⌈(a : ℚ) / b⌉₊ = a + (b - a % b) % b := by
  have hdiv := Nat.mod_add_div a b
  have hmod := Nat.mod_lt a hb
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  by_cases hz : a % b = 0
  · have heq : (a : ℚ) / b = (a / b : ℕ) := by
      apply (div_eq_iff (ne_of_gt hbq)).2
      have h : a = b * (a / b) := by omega
      exact_mod_cast h.trans (Nat.mul_comm _ _)
    rw [heq, Nat.ceil_natCast, hz]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    omega
  · have hpos : 0 < a % b := by omega
    have hq : (a % b : ℚ) + (b : ℚ) * (a / b : ℕ) = a := by
      exact_mod_cast hdiv
    have hl : (a / b : ℕ) < (a : ℚ) / b := by
      apply (lt_div_iff₀ hbq).2
      have hp : (0 : ℚ) < a % b := by exact_mod_cast hpos
      nlinarith
    have hu : (a : ℚ) / b ≤ ((a / b : ℕ) + 1 : ℕ) := by
      apply (div_le_iff₀ hbq).2
      have hm : (a % b : ℚ) < b := by exact_mod_cast hmod
      push_cast
      nlinarith
    have hc : ⌈(a : ℚ) / b⌉₊ = a / b + 1 := by
      apply (Nat.ceil_eq_iff (Nat.succ_ne_zero (a / b))).2
      simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using And.intro hl hu
    rw [hc, Nat.mod_eq_of_lt (by omega : b - a % b < b)]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- The least residue of the next trace dimension. -/
def ambientResidue (n d : ℕ) : ℕ := N (n - 1) (d + 1) % (n - 1)

/-- The least residue of the negative next trace dimension. -/
def ambientComplementaryResidue (n d : ℕ) : ℕ :=
  (n - 1 - ambientResidue n d) % (n - 1)

/-- The lower critical dimension and its residue reconstruct the trace dimension. -/
theorem lowerCritical_residue_identity (n d : ℕ) (hn : 2 ≤ n) :
    (n - 1) * lowerCritical n d + ambientResidue n d = N (n - 1) (d + 1) := by
  rw [lowerCritical_successor_trace n d hn]
  exact Nat.div_add_mod _ _

/-- The upper critical dimension adds the complementary residue. -/
theorem upperCritical_residue_identity (n d : ℕ) (hn : 2 ≤ n) :
    (n - 1) * upperCritical n d =
      N (n - 1) (d + 1) + ambientComplementaryResidue n d := by
  unfold upperCritical
  rw [E_successor_trace_ratio n d hn]
  exact mul_natCeil_div _ _ (by omega)

/-- The dimension remaining after the fixed partial trace in Proposition 3.8. -/
def fractionalTraceDefect (n d : ℕ) : ℕ :=
  (n - 1) * N (n - 1) (d - 1) - N (n - 1) (d + 1)

/-- The number of scalar rows selected in the lower-level transfer. -/
def fractionalTraceRows (n d : ℕ) : ℕ := fractionalTraceDefect n d / (n - 2)

/-- The dimension of the lower-level trace image. -/
def fractionalTraceRemainder (n d : ℕ) : ℕ := fractionalTraceDefect n d % (n - 2)

/-- The dimension of the first fractional trace kernel. -/
def fractionalTopTraceDimension (n d : ℕ) : ℕ :=
  ambientComplementaryResidue (n - 1) d

/-- Euclidean division splits the lower-level trace dimension. -/
theorem fractionalTrace_division (n d : ℕ) :
    (n - 2) * fractionalTraceRows n d + fractionalTraceRemainder n d =
      fractionalTraceDefect n d := by
  exact Nat.div_add_mod _ _

theorem fractionalTraceRemainder_lt (n d : ℕ) (hn : 3 ≤ n) :
    fractionalTraceRemainder n d < n - 2 := Nat.mod_lt _ (by omega)

/-- The injective residual dimension in Proposition 3.8. -/
def fractionalResidualI (n d : ℕ) : ℚ :=
  ((fractionalTraceRows n d : ℚ) + (n - 1 : ℕ) - ambientResidue n d -
    fractionalTraceRemainder n d) / (n - 1 : ℕ)

/-- The surjective residual dimension in Proposition 3.8. -/
def fractionalResidualS (n d : ℕ) : ℚ :=
  ((fractionalTraceRows n d : ℚ) + (n - 1 : ℕ) + ambientComplementaryResidue n d -
    fractionalTraceRemainder n d) / (n - 1 : ℕ)

/-- The injective residual formula is an integer difference of actual dimensions. -/
theorem fractionalResidualI_eq (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    fractionalResidualI n d = (lowerCritical n d : ℚ) +
      fractionalTraceRows n d + 1 - N (n - 1) (d - 1) := by
  have hcrit : ((n - 1 : ℕ) : ℚ) * lowerCritical n d + ambientResidue n d =
      N (n - 1) (d + 1) := by
    exact_mod_cast lowerCritical_residue_identity n d (by omega)
  have hrows : ((n - 2 : ℕ) : ℚ) * fractionalTraceRows n d +
      fractionalTraceRemainder n d =
      ((n - 1 : ℕ) : ℚ) * N (n - 1) (d - 1) - N (n - 1) (d + 1) := by
    have h := fractionalTrace_division n d
    unfold fractionalTraceDefect at h
    exact_mod_cast h
  have hn0 : ((n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hcast : ((n - 2 : ℕ) : ℚ) = ((n - 1 : ℕ) : ℚ) - 1 := by
    have h : n - 2 + 1 = n - 1 := by omega
    have hq : ((n - 2 : ℕ) : ℚ) + 1 = ((n - 1 : ℕ) : ℚ) := by exact_mod_cast h
    linarith
  unfold fractionalResidualI
  apply (div_eq_iff hn0).2
  rw [hcast] at hrows
  nlinarith [hcrit, hrows]

/-- The surjective residual formula is an integer difference of actual dimensions. -/
theorem fractionalResidualS_eq (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    fractionalResidualS n d = (upperCritical n d : ℚ) +
      fractionalTraceRows n d + 1 - N (n - 1) (d - 1) := by
  have hcrit : ((n - 1 : ℕ) : ℚ) * upperCritical n d =
      N (n - 1) (d + 1) + (ambientComplementaryResidue n d : ℚ) := by
    exact_mod_cast upperCritical_residue_identity n d (by omega)
  have hrows : ((n - 2 : ℕ) : ℚ) * fractionalTraceRows n d +
      fractionalTraceRemainder n d =
      ((n - 1 : ℕ) : ℚ) * N (n - 1) (d - 1) - N (n - 1) (d + 1) := by
    have h := fractionalTrace_division n d
    unfold fractionalTraceDefect at h
    exact_mod_cast h
  have hn0 : ((n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hcast : ((n - 2 : ℕ) : ℚ) = ((n - 1 : ℕ) : ℚ) - 1 := by
    have h : n - 2 + 1 = n - 1 := by omega
    have hq : ((n - 2 : ℕ) : ℚ) + 1 = ((n - 1 : ℕ) : ℚ) := by exact_mod_cast h
    linarith
  unfold fractionalResidualS
  apply (div_eq_iff hn0).2
  rw [hcast] at hrows
  nlinarith [hcrit, hrows]

/-- Both residual formulas are integral. -/
theorem fractionalResiduals_integral (n d : ℕ) (hn : 3 ≤ n)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    (∃ r : ℤ, fractionalResidualI n d = r) ∧
      ∃ r : ℤ, fractionalResidualS n d = r := by
  constructor
  · refine ⟨(lowerCritical n d : ℤ) + fractionalTraceRows n d + 1 -
      N (n - 1) (d - 1), ?_⟩
    simpa using fractionalResidualI_eq n d hn hdef
  · refine ⟨(upperCritical n d : ℤ) + fractionalTraceRows n d + 1 -
      N (n - 1) (d - 1), ?_⟩
    simpa using fractionalResidualS_eq n d hn hdef

/-- The two residual dimensions are in the expected order. -/
theorem fractionalResidualI_le_S (n d : ℕ) :
    fractionalResidualI n d ≤ fractionalResidualS n d := by
  unfold fractionalResidualI fractionalResidualS
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hI : (0 : ℚ) ≤ ambientResidue n d := by positivity
  have hS : (0 : ℚ) ≤ ambientComplementaryResidue n d := by positivity
  linarith

/-- The injective residual accounts for exactly the selected rows and the negative residue. -/
theorem fractionalResidualI_row_balance (n d : ℕ) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℚ) * fractionalResidualI n d -
      (((n - 1 : ℕ) : ℚ) - fractionalTraceRemainder n d) =
      (fractionalTraceRows n d : ℚ) - ambientResidue n d := by
  have hne : ((n - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  unfold fractionalResidualI
  field_simp
  ring

/-- The surjective residual accounts for exactly the selected rows and the positive residue. -/
theorem fractionalResidualS_row_balance (n d : ℕ) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℚ) * fractionalResidualS n d -
      (((n - 1 : ℕ) : ℚ) - fractionalTraceRemainder n d) =
      (fractionalTraceRows n d : ℚ) + ambientComplementaryResidue n d := by
  have hne : ((n - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  unfold fractionalResidualS
  field_simp
  ring

/-- Sufficient selected rows make the injective residual strictly positive. -/
theorem fractionalResidualI_pos (n d : ℕ) (hn : 3 ≤ n)
    (hrows : n - 2 ≤ fractionalTraceRows n d) :
    0 < fractionalResidualI n d := by
  have ha : ambientResidue n d < n - 1 := Nat.mod_lt _ (by omega)
  have hb := fractionalTraceRemainder_lt n d hn
  have hnat : ambientResidue n d + fractionalTraceRemainder n d + 2 ≤
      fractionalTraceRows n d + (n - 1) := by omega
  have hq : (ambientResidue n d : ℚ) + fractionalTraceRemainder n d + 2 ≤
      (fractionalTraceRows n d : ℚ) + (n - 1 : ℕ) := by exact_mod_cast hnat
  unfold fractionalResidualI
  apply div_pos (by linarith)
  exact_mod_cast (show 0 < n - 1 by omega)

/-- The coarse trace lower bound supplies the complete scalar-row budget. -/
theorem fractionalResidualS_scalar_budget (n d τ : ℕ) (hn : 3 ≤ n)
    (hτ : 2 * n - 3 ≤ τ) :
    ((n - 1 : ℕ) : ℚ) * fractionalResidualS n d ≤
      τ + (fractionalTraceRows n d : ℚ) := by
  have ha : ambientComplementaryResidue n d < n - 1 := Nat.mod_lt _ (by omega)
  have hnat : (n - 1) + ambientComplementaryResidue n d ≤ τ := by omega
  have hq : ((n - 1 : ℕ) : ℚ) + ambientComplementaryResidue n d ≤ τ := by
    exact_mod_cast hnat
  have hbalance := fractionalResidualS_row_balance n d (by omega)
  have hb : (0 : ℚ) ≤ fractionalTraceRemainder n d := by positivity
  linarith

/-- The first trace kernel has the expected fractional dimension. -/
theorem fractionalTopTraceDimension_eq (n d : ℕ) (hn : 3 ≤ n) :
    (fractionalTopTraceDimension n d : ℚ) =
      ((n - 2 : ℕ) : ℚ) * ((upperCritical (n - 1) d : ℚ) - E (n - 1) d) := by
  have hc : ((n - 2 : ℕ) : ℚ) * upperCritical (n - 1) d =
      (N (n - 2) (d + 1) : ℚ) + fractionalTopTraceDimension n d := by
    have h := upperCritical_residue_identity (n - 1) d (by omega)
    have hs : n - 1 - 1 = n - 2 := by omega
    simpa only [hs, fractionalTopTraceDimension, Nat.cast_add, Nat.cast_mul] using
      congrArg (fun x : ℕ => (x : ℚ)) h
  have he : E (n - 1) d = (N (n - 2) (d + 1) : ℚ) / (n - 2 : ℕ) := by
    simpa only [show n - 1 - 1 = n - 2 by omega] using
      E_successor_trace_ratio (n - 1) d (by omega)
  have hn0 : ((n - 2 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show n - 2 ≠ 0 by omega)
  rw [he]
  field_simp
  nlinarith [hc]

/-- Removing the first trace and its partial fiber leaves exactly the defect dimension. -/
theorem fractionalTrace_dimension_identity (n d : ℕ) (hn : 3 ≤ n)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    ((n - 1 : ℕ) : ℚ) * N (n - 1) (d - 1) - N (n - 1) d -
      ((n - 2 : ℕ) : ℚ) * lowerCritical (n - 1) d -
      (((n - 2 : ℕ) : ℚ) - fractionalTopTraceDimension n d) =
      fractionalTraceDefect n d := by
  have hc := upperCritical_residue_identity (n - 1) d (by omega)
  have hs : n - 1 - 1 = n - 2 := by omega
  rw [hs, hfrac] at hc
  have hq : ((n - 2 : ℕ) : ℚ) * ((lowerCritical (n - 1) d : ℚ) + 1) =
      (N (n - 2) (d + 1) : ℚ) + fractionalTopTraceDimension n d := by
    exact_mod_cast hc
  have hp : (N (n - 1) (d + 1) : ℚ) =
      (N (n - 2) (d + 1) : ℚ) + N (n - 1) d := by
    have h := N_pascal (n - 1) (d + 1) (by omega) (by omega)
    simpa only [hs, Nat.add_sub_cancel, Nat.cast_add] using congrArg (fun x : ℕ => (x : ℚ)) h
  have hd : (fractionalTraceDefect n d : ℚ) =
      ((n - 1 : ℕ) : ℚ) * N (n - 1) (d - 1) - N (n - 1) (d + 1) := by
    simp only [fractionalTraceDefect, Nat.cast_sub hdef, Nat.cast_mul]
  rw [hd]
  nlinarith [hq, hp]

/-- The three auxiliary counts lie just above the lower-degree critical ideal dimension. -/
theorem fractionalTrace_auxiliary_difference (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    (N (n - 1) (d - 1) : ℚ) - lowerCritical (n - 1) d -
      fractionalTraceRows n d - E (n - 1) (d - 1) =
      1 + ((fractionalTraceRemainder n d : ℚ) - fractionalTopTraceDimension n d) /
        (n - 2 : ℕ) := by
  have ht := fractionalTrace_dimension_identity n d hn hfrac hdef
  have hr : ((n - 2 : ℕ) : ℚ) * fractionalTraceRows n d +
      fractionalTraceRemainder n d = fractionalTraceDefect n d := by
    exact_mod_cast fractionalTrace_division n d
  have hp : (N (n - 1) d : ℚ) - N (n - 1) (d - 1) =
      ((n - 2 : ℕ) : ℚ) * E (n - 1) (d - 1) := by
    have h := N_step_difference (n - 1) (d - 1) (by omega)
    have hs : d - 1 + 1 = d := by omega
    have hnq : ((n - 1 : ℕ) : ℚ) - 1 = ((n - 2 : ℕ) : ℚ) := by
      have heq : ((n - 2 : ℕ) : ℚ) + 1 = ((n - 1 : ℕ) : ℚ) := by
        exact_mod_cast (show n - 2 + 1 = n - 1 by omega)
      linarith
    simpa only [hs, hnq] using h
  have hnq : ((n - 1 : ℕ) : ℚ) = ((n - 2 : ℕ) : ℚ) + 1 := by
    exact_mod_cast (show n - 1 = n - 2 + 1 by omega)
  have hn0 : ((n - 2 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show n - 2 ≠ 0 by omega)
  have hresult : (N (n - 1) (d - 1) : ℚ) - lowerCritical (n - 1) d -
      fractionalTraceRows n d - E (n - 1) (d - 1) - 1 =
      ((fractionalTraceRemainder n d : ℚ) - fractionalTopTraceDimension n d) /
        (n - 2 : ℕ) := by
    apply (eq_div_iff hn0).2
    rw [hnq] at ht
    nlinarith [ht, hr, hp]
  linarith

/-- The two exceptional fractional edges in degree four have the stated small parameters. -/
theorem fractional_quartic_seven :
    lowerCritical 6 4 = 25 ∧ fractionalTraceDefect 7 4 = 84 ∧
      fractionalTraceRows 7 4 = 16 ∧ fractionalTraceRemainder 7 4 = 4 ∧
      fractionalResidualI 7 4 = 3 ∧ fractionalResidualS 7 4 = 3 := by
  rw [lowerCritical_successor_trace 6 4 (by decide)]
  norm_num [N, fractionalTraceDefect, fractionalTraceRows,
    fractionalTraceRemainder, fractionalResidualI, fractionalResidualS,
    ambientResidue, ambientComplementaryResidue, Nat.choose]

theorem fractional_quartic_twelve :
    lowerCritical 11 4 = 200 ∧ fractionalTraceDefect 12 4 = 143 ∧
      fractionalTraceRows 12 4 = 14 ∧ fractionalTraceRemainder 12 4 = 3 ∧
      fractionalResidualI 12 4 = 2 ∧ fractionalResidualS 12 4 = 2 := by
  rw [lowerCritical_successor_trace 11 4 (by decide)]
  norm_num [N, fractionalTraceDefect, fractionalTraceRows,
    fractionalTraceRemainder, fractionalResidualI, fractionalResidualS,
    ambientResidue, ambientComplementaryResidue, Nat.choose]

end IdealGeneration
