module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimension arithmetic for ideal generation

The dimension counts and rational critical value in Section 2 of
*Ideal generation for general reduced projective points*.
-/

namespace IdealGeneration

/-- The number of degree-`d` monomials in `n` variables. -/
def N (n d : ℕ) : ℕ := (n + d - 1).choose d

/-- The critical degree-`d` ideal dimension. -/
def E (n d : ℕ) : ℚ := (N n d : ℚ) / (d + 1)

theorem N_eq_multichoose (n d : ℕ) : N n d = n.multichoose d := by
  exact (Nat.multichoose_eq n d).symm

@[simp] theorem N_zero_degree (n : ℕ) : N n 0 = 1 := by
  simp [N]

@[simp] theorem N_one_variable (d : ℕ) : N 1 d = 1 := by
  simp [N]

@[simp] theorem N_one_degree (n : ℕ) : N n 1 = n := by
  simp [N]

theorem N_pos {n d : ℕ} (hn : 1 ≤ n) : 0 < N n d := by
  apply Nat.choose_pos
  omega

/-- The degree recurrence `(d+1) N_{d+1}(n) = (n+d) N_d(n)`. -/
theorem N_degree_recurrence (n d : ℕ) (hn : 1 ≤ n) :
    (d + 1) * N n (d + 1) = (n + d) * N n d := by
  have h := Nat.add_one_mul_choose_eq (n + d - 1) d
  have ha : n + d - 1 + 1 = n + d := by omega
  have hb : n + (d + 1) - 1 = n + d := by omega
  simpa only [N, hb, ha, Nat.mul_comm] using h.symm

/-- Pascal's identity in the number of variables. -/
theorem N_pascal (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    N n d = N (n - 1) d + N n (d - 1) := by
  simp only [N_eq_multichoose]
  have h := Nat.multichoose_succ_succ (n - 1) (d - 1)
  simpa only [Nat.sub_add_cancel hn, Nat.sub_add_cancel hd] using h

/-- Successive homogeneous components grow in dimension. -/
theorem N_pred_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    N n (d - 1) ≤ N n d := by
  rw [N_pascal n d hn hd]
  omega

/-- The difference of consecutive scalar dimensions. -/
theorem N_step_difference (n d : ℕ) (hn : 1 ≤ n) :
    (N n (d + 1) : ℚ) - N n d = ((n : ℚ) - 1) * E n d := by
  have h : ((d : ℚ) + 1) * N n (d + 1) = ((n : ℚ) + d) * N n d := by
    exact_mod_cast N_degree_recurrence n d hn
  have hd : (d : ℚ) + 1 ≠ 0 := by positivity
  unfold E
  field_simp
  nlinarith [h]

/-- Equation (2.4), with `r` the degree-`d` ideal dimension. -/
theorem multiplication_dimension_difference (n d : ℕ) (hn : 1 ≤ n) (r : ℚ) :
    (n : ℚ) * r - ((N n (d + 1) : ℚ) - N n d + r) =
      ((n : ℚ) - 1) * (r - E n d) := by
  rw [N_step_difference n d hn]
  ring

/-- Equation (2.4), with the number of points explicitly displayed. -/
theorem multiplication_dimension_difference_points
    (n d p : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * ((N n d : ℚ) - p) - ((N n (d + 1) : ℚ) - p) =
      ((n : ℚ) - 1) * ((N n d : ℚ) - p - E n d) := by
  have h := multiplication_dimension_difference n d hn ((N n d : ℚ) - p)
  convert h using 1
  ring

/-- The critical ideal dimension is in the scalar-postulation cell. -/
theorem E_le_cell_width (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    E n d ≤ (N n d : ℚ) - N n (d - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hrec := N_degree_recurrence n (d - 1) hn1
  have heq : d - 1 + 1 = d := by omega
  rw [heq] at hrec
  have hfactor : d + 1 ≤ n + (d - 1) := by omega
  have hprod := Nat.mul_le_mul_right (N n (d - 1)) hfactor
  have hbound : (d + 1) * N n (d - 1) ≤ d * N n d := by
    nlinarith [hrec]
  have hboundq : ((d : ℚ) + 1) * N n (d - 1) ≤ (d : ℚ) * N n d := by
    exact_mod_cast hbound
  have hdq : (0 : ℚ) < d + 1 := by positivity
  unfold E
  rw [div_le_iff₀ hdq]
  nlinarith [hboundq]

/-- Increasing the number of variables increases the monomial count. -/
theorem N_mono_variables (d : ℕ) : Monotone (fun n => N n d) := by
  intro a b hab
  exact Nat.choose_le_choose d (by omega)

@[simp] theorem N_two_variables (d : ℕ) : N 2 d = d + 1 := by
  simp [N, Nat.add_comm]

/-- For at least two variables the critical value is at least one. -/
theorem one_le_E (n d : ℕ) (hn : 2 ≤ n) : 1 ≤ E n d := by
  have h := N_mono_variables d hn
  change N 2 d ≤ N n d at h
  rw [N_two_variables] at h
  have hq : (d : ℚ) + 1 ≤ N n d := by exact_mod_cast h
  unfold E
  rw [le_div_iff₀ (by positivity)]
  simpa using hq

/-- The two critical integer dimensions. -/
noncomputable def lowerCritical (n d : ℕ) : ℕ := ⌊E n d⌋₊
noncomputable def upperCritical (n d : ℕ) : ℕ := ⌈E n d⌉₊

/-- The floor critical value lies in the allowed ideal-dimension cell. -/
theorem lowerCritical_mem_cell (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    1 ≤ lowerCritical n d ∧ lowerCritical n d ≤ N n d - N n (d - 1) := by
  have hE := one_le_E n d hn
  have hwidth := E_le_cell_width n d hn hd
  have hpred := N_pred_le n d (by omega) hd
  constructor
  · exact Nat.le_floor hE
  · apply Nat.floor_le_of_le
    rw [Nat.cast_sub hpred]
    exact hwidth

/-- The ceiling critical value lies in the allowed ideal-dimension cell. -/
theorem upperCritical_mem_cell (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    1 ≤ upperCritical n d ∧ upperCritical n d ≤ N n d - N n (d - 1) := by
  have hE := one_le_E n d hn
  have hwidth := E_le_cell_width n d hn hd
  have hpred := N_pred_le n d (by omega) hd
  constructor
  · have hle : lowerCritical n d ≤ upperCritical n d := Nat.floor_le_ceil _
    exact le_trans (lowerCritical_mem_cell n d hn hd).1 hle
  · apply Nat.ceil_le.mpr
    rw [Nat.cast_sub hpred]
    exact hwidth

/-- The source dimension is at most the target precisely below the critical value. -/
theorem source_le_target_iff (n d : ℕ) (hn : 2 ≤ n) (r : ℚ) :
    (n : ℚ) * r ≤ (N n (d + 1) : ℚ) - N n d + r ↔ r ≤ E n d := by
  have hnq : (0 : ℚ) < n - 1 := by
    have h : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have h := multiplication_dimension_difference n d (by omega) r
  constructor
  · intro hle
    have hp : ((n : ℚ) - 1) * (r - E n d) ≤ 0 := by linarith
    by_contra hnot
    have hpos : 0 < r - E n d := by linarith
    have := mul_pos hnq hpos
    linarith
  · intro hle
    have hp : ((n : ℚ) - 1) * (r - E n d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hnq) (sub_nonpos.mpr hle)
    linarith

/-- The target dimension is at most the source precisely above the critical value. -/
theorem target_le_source_iff (n d : ℕ) (hn : 2 ≤ n) (r : ℚ) :
    (N n (d + 1) : ℚ) - N n d + r ≤ (n : ℚ) * r ↔ E n d ≤ r := by
  have hnq : (0 : ℚ) < n - 1 := by
    have h : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have h := multiplication_dimension_difference n d (by omega) r
  constructor
  · intro hle
    have hp : 0 ≤ ((n : ℚ) - 1) * (r - E n d) := by linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hnq).mp hp)
  · intro hle
    have hp : 0 ≤ ((n : ℚ) - 1) * (r - E n d) :=
      mul_nonneg (le_of_lt hnq) (sub_nonneg.mpr hle)
    linarith

/-- Natural ideal dimensions below the rational threshold are exactly those
at most the floor critical count. -/
theorem le_E_iff_le_lowerCritical (n d r : ℕ) :
    (r : ℚ) ≤ E n d ↔ r ≤ lowerCritical n d := by
  have hE : 0 ≤ E n d := by unfold E; positivity
  exact (Nat.le_floor_iff hE).symm

/-- Natural ideal dimensions above the rational threshold are exactly those
at least the ceiling critical count. -/
theorem E_le_iff_upperCritical_le (n d r : ℕ) :
    E n d ≤ (r : ℚ) ↔ upperCritical n d ≤ r := by
  exact Nat.ceil_le.symm

/-- The two critical counts differ by at most one. -/
theorem upperCritical_le_lowerCritical_add_one (n d : ℕ) :
    upperCritical n d ≤ lowerCritical n d + 1 := by
  exact Nat.ceil_le_floor_add_one _

/-- Every natural ideal dimension belongs to one of the two monotonicity ranges. -/
theorem critical_ranges_cover (n d r : ℕ) :
    r ≤ lowerCritical n d ∨ upperCritical n d ≤ r := by
  have h := upperCritical_le_lowerCritical_add_one n d
  omega

/-- The numerical number of new generators when multiplication has maximal rank. -/
theorem next_generator_count_formula (n d p : ℕ) (hn : 1 ≤ n) :
    max 0 ((N n (d + 1) : ℚ) - p - (n : ℚ) * ((N n d : ℚ) - p)) =
      max 0 (((n : ℚ) - 1) * (E n d - ((N n d : ℚ) - p))) := by
  congr 1
  have h := multiplication_dimension_difference_points n d p hn
  linarith

/-- The initial-degree point-count interval is equivalent to the ideal-dimension cell. -/
theorem initial_degree_cell_iff (n d p : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (N n (d - 1) ≤ p ∧ p < N n d) ↔
      (1 ≤ N n d - p ∧ N n d - p ≤ N n d - N n (d - 1)) := by
  have h := N_pred_le n d hn hd
  omega

end IdealGeneration
