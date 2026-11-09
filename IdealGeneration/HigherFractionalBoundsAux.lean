module

public import IdealGeneration.FractionalTraceNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Lower trace and auxiliary-cell bounds used in Proposition 6.1. -/

namespace IdealGeneration

/-- Twenty-four times the scalar dimension in five variables. -/
theorem twentyfour_N_five (e : ℕ) :
    24 * N 5 e = (e + 1) * (e + 2) * (e + 3) * (e + 4) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose e 4
  have hs : N 5 e = (e + 4).choose 4 := by
    unfold N
    rw [show 5 + e - 1 = e + 4 by omega]
    have hc := Nat.choose_symm (show e ≤ e + 4 by omega)
    simpa using hc.symm
  rw [hs]
  norm_num [Nat.factorial, Nat.ascFactorial] at h
  nlinarith [h]

/-- The quartic monomial count as a product of four successive integers. -/
theorem twentyfour_N_quartic (n : ℕ) :
    24 * N n 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose' n 4
  unfold N
  rw [show n + 4 - 1 = n + 3 by omega]
  norm_num [Nat.factorial, Nat.ascFactorial] at h
  nlinarith [h]

/-- The critical value in five variables is a cubic polynomial. -/
theorem E_five_formula (e : ℕ) :
    E 5 e = ((e : ℚ) + 2) * (e + 3) * (e + 4) / 24 := by
  have h : 24 * (N 5 e : ℚ) =
      ((e : ℚ) + 1) * (e + 2) * (e + 3) * (e + 4) := by
    exact_mod_cast twentyfour_N_five e
  unfold E
  apply (div_eq_iff (by positivity : (e : ℚ) + 1 ≠ 0)).2
  field_simp
  nlinarith [h]

/-- Scalar dimensions increase with degree in a positive number of variables. -/
theorem N_mono_degree (n : ℕ) (hn : 1 ≤ n) : Monotone (N n) := by
  apply monotone_nat_of_le_succ
  intro d
  simpa using N_pred_le n (d + 1) hn (by omega)

/-- The critical value increases with the number of variables. -/
theorem E_mono_variables (d : ℕ) : Monotone (fun n => E n d) := by
  intro n m hnm
  unfold E
  exact div_le_div_of_nonneg_right (by exact_mod_cast N_mono_variables d hnm) (by positivity)

/-- The critical value increases with degree for at least two variables. -/
theorem E_mono_degree (n : ℕ) (hn : 2 ≤ n) : Monotone (E n) := by
  apply monotone_nat_of_le_succ
  intro d
  have hrec : ((d : ℚ) + 1) * N n (d + 1) = ((n : ℚ) + d) * N n d := by
    exact_mod_cast N_degree_recurrence n d (by omega)
  have hcoef : (d : ℚ) + 2 ≤ (n : ℚ) + d := by exact_mod_cast (show d + 2 ≤ n + d by omega)
  have hprod := mul_le_mul_of_nonneg_right hcoef (show (0 : ℚ) ≤ N n d by positivity)
  unfold E
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith [hrec, hprod]

/-- The quartic critical value supplies two scalar rows per added variable. -/
theorem quartic_critical_linear_lower (m : ℕ) (hm : 4 ≤ m) :
    (2 * m - 1 : ℕ) ≤ E m 4 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [E, N, Nat.choose]
  | succ m hm ih =>
      have hp := N_pascal (m + 1) 4 (by omega) (by omega)
      have hN : 10 ≤ N (m + 1) 3 := by
        have h := N_mono_variables 3 (show 3 ≤ m + 1 by omega)
        norm_num [N] at h ⊢
        exact h
      have hmcast : ((2 * (m + 1) - 1 : ℕ) : ℚ) = (2 * m - 1 : ℕ) + 2 := by
        exact_mod_cast (show 2 * (m + 1) - 1 = (2 * m - 1) + 2 by omega)
      have hpq : (N (m + 1) 4 : ℚ) = (N m 4 : ℚ) + N (m + 1) 3 := by
        exact_mod_cast (by simpa only [Nat.add_sub_cancel] using hp)
      have hNq : (10 : ℚ) ≤ N (m + 1) 3 := by exact_mod_cast hN
      rw [hmcast]
      unfold E at ih ⊢
      norm_num only [Nat.cast_ofNat] at ih ⊢
      rw [hpq]
      linarith

/-- The first trace supplies the complete scalar-row budget. -/
theorem higherFractional_trace_rows_lower (n d : ℕ) (hn : 5 ≤ n) (hd : 5 ≤ d) :
    2 * n - 3 ≤ lowerCritical (n - 1) d := by
  apply (le_E_iff_le_lowerCritical _ _ _).mp
  have hbase := quartic_critical_linear_lower (n - 1) (by omega)
  have hdeg := E_mono_degree (n - 1) (by omega) (show 4 ≤ d by omega)
  have hcount : 2 * (n - 1) - 1 = 2 * n - 3 := by omega
  rw [hcount] at hbase
  exact hbase.trans hdeg

/-- The lower auxiliary critical value stays above the three discarded rows. -/
theorem higherFractional_auxiliary_critical_lower (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) : 7 ≤ E (n - 1) (d - 1) := by
  have hnmono := E_mono_variables 4 (show 4 ≤ n - 1 by omega)
  have hdmono := E_mono_degree (n - 1) (by omega) (show 4 ≤ d - 1 by omega)
  change E 4 4 ≤ E (n - 1) 4 at hnmono
  have hbase : E 4 4 = 7 := by norm_num [E, N, Nat.choose]
  rw [hbase] at hnmono
  exact hnmono.trans hdmono

/-- A cross-variable identity for a fixed scalar degree. -/
theorem N_variable_ratio (m e : ℕ) (hm : 2 ≤ m) (he : 1 ≤ e) :
    (m - 1) * N m e = (m + e - 1) * N (m - 1) e := by
  have hc := N_cross_hyperplane m e hm he
  have hp := N_pascal m e (by omega) he
  have hs : m + e - 1 = (m - 1) + e := by omega
  rw [hp, hs]
  nlinarith [hc]

/-- Half the next scalar width already bounds the auxiliary critical value. -/
theorem higherFractional_auxiliary_critical_upper (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) :
    E (n - 1) (d - 1) ≤ (N (n - 2) (d - 1) : ℚ) / 2 := by
  have hr := N_variable_ratio (n - 1) (d - 1) (by omega) (by omega)
  have hnsub : n - 1 - 1 = n - 2 := by omega
  have hsum : n - 1 + (d - 1) - 1 = n + d - 3 := by omega
  rw [hnsub, hsum] at hr
  have hcoeff : 2 * (n + d - 3) ≤ d * (n - 2) := by
    have hmul := Nat.mul_le_mul (show 1 ≤ n - 4 by omega) (show 3 ≤ d - 2 by omega)
    have hn4 : n - 4 + 4 = n := by omega
    have hn2 : n - 2 + 2 = n := by omega
    have hd2 : d - 2 + 2 = d := by omega
    have hnd : n + d - 3 + 3 = n + d := by omega
    nlinarith
  have hprod := Nat.mul_le_mul_right (N (n - 2) (d - 1)) hcoeff
  have hbound : 2 * N (n - 1) (d - 1) ≤ d * N (n - 2) (d - 1) := by
    have hfactor : 0 < n - 2 := by omega
    apply (Nat.mul_le_mul_left_iff hfactor).mp
    nlinarith [hr, hprod]
  have hboundq : 2 * (N (n - 1) (d - 1) : ℚ) ≤ d * (N (n - 2) (d - 1) : ℚ) := by
    exact_mod_cast hbound
  unfold E
  have hdq : ((d - 1 : ℕ) : ℚ) + 1 = d := by
    exact_mod_cast (show d - 1 + 1 = d by omega)
  rw [hdq]
  rw [div_le_div_iff₀ (by exact_mod_cast (show 0 < d by omega)) (by norm_num)]
  simpa only [mul_comm] using hboundq

/-- The auxiliary scalar component has room for all three adjacent counts. -/
theorem higherFractional_auxiliary_scalar_lower (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d) : 15 ≤ N (n - 2) (d - 1) := by
  have hnmono := N_mono_variables 4 (show 3 ≤ n - 2 by omega)
  have hdmono := N_mono_degree (n - 2) (by omega) (show 4 ≤ d - 1 by omega)
  change N 3 4 ≤ N (n - 2) 4 at hnmono
  have hbase : N 3 4 = 15 := by norm_num [N, Nat.choose]
  rw [hbase] at hnmono
  exact hnmono.trans hdmono

/-- The auxiliary ideal dimension lies strictly between the critical value
and that value plus two. -/
theorem higherFractional_auxiliary_residual_bounds (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    E (n - 1) (d - 1) < (N (n - 1) (d - 1) : ℚ) -
        lowerCritical (n - 1) d - fractionalTraceRows n d ∧
      (N (n - 1) (d - 1) : ℚ) - lowerCritical (n - 1) d -
        fractionalTraceRows n d < E (n - 1) (d - 1) + 2 := by
  have hidentity := fractionalTrace_auxiliary_difference n d (by omega) (by omega) hfrac hdef
  have hb1 := fractionalTraceRemainder_lt n d (by omega)
  have hb0 : fractionalTopTraceDimension n d < n - 2 := by
    unfold fractionalTopTraceDimension ambientComplementaryResidue
    rw [show n - 1 - 1 = n - 2 by omega]
    exact Nat.mod_lt _ (by omega)
  have hb0q : (fractionalTopTraceDimension n d : ℚ) < (n - 2 : ℕ) := by exact_mod_cast hb0
  have hb1q : (fractionalTraceRemainder n d : ℚ) < (n - 2 : ℕ) := by exact_mod_cast hb1
  have hz0 : (0 : ℚ) ≤ fractionalTopTraceDimension n d := by positivity
  have hz1 : (0 : ℚ) ≤ fractionalTraceRemainder n d := by positivity
  have hden : (0 : ℚ) < (n - 2 : ℕ) := by exact_mod_cast (show 0 < n - 2 by omega)
  have hlo : (-1 : ℚ) < ((fractionalTraceRemainder n d : ℚ) -
      fractionalTopTraceDimension n d) / (n - 2 : ℕ) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hhi : ((fractionalTraceRemainder n d : ℚ) -
      fractionalTopTraceDimension n d) / (n - 2 : ℕ) < 1 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  constructor <;> linarith

/-- All three auxiliary point counts belong to the preceding-degree scalar cell. -/
theorem higherFractional_auxiliary_point_cell (n d : ℕ)
    (hn : 5 ≤ n) (hd : 5 ≤ d)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1)) :
    ∀ j : ℕ, j ≤ 2 →
      N (n - 1) (d - 2) ≤ lowerCritical (n - 1) d + fractionalTraceRows n d + j ∧
        lowerCritical (n - 1) d + fractionalTraceRows n d + j < N (n - 1) (d - 1) := by
  obtain ⟨hlo, hhi⟩ := higherFractional_auxiliary_residual_bounds n d hn hd hfrac hdef
  have hElower := higherFractional_auxiliary_critical_lower n d hn hd
  have hEupper := higherFractional_auxiliary_critical_upper n d hn hd
  have hsmall : (15 : ℚ) ≤ N (n - 2) (d - 1) := by
    exact_mod_cast higherFractional_auxiliary_scalar_lower n d hn hd
  have hpascal : (N (n - 1) (d - 1) : ℚ) =
      (N (n - 2) (d - 1) : ℚ) + N (n - 1) (d - 2) := by
    have h := N_pascal (n - 1) (d - 1) (by omega) (by omega)
    have hnsub : n - 1 - 1 = n - 2 := by omega
    have hdsub : d - 1 - 1 = d - 2 := by omega
    rw [hnsub, hdsub] at h
    exact_mod_cast h
  have hbase : N (n - 1) (d - 2) ≤ lowerCritical (n - 1) d + fractionalTraceRows n d := by
    have hq : (N (n - 1) (d - 2) : ℚ) ≤
        (lowerCritical (n - 1) d : ℚ) + fractionalTraceRows n d := by linarith
    exact_mod_cast hq
  have htop : lowerCritical (n - 1) d + fractionalTraceRows n d + 2 <
      N (n - 1) (d - 1) := by
    have hq : (lowerCritical (n - 1) d : ℚ) + fractionalTraceRows n d + 2 <
        N (n - 1) (d - 1) := by linarith
    exact_mod_cast hq
  intro j hj
  constructor <;> omega

end IdealGeneration
