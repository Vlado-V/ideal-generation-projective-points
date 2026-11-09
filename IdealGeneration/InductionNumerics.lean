module

public import IdealGeneration.Numerics
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Divisibility at the endpoint of the one-hyperplane induction range. -/

namespace IdealGeneration

/-- Integrality of a critical value is exactly divisibility of the monomial count. -/
theorem E_integral_iff (n d : ℕ) :
    (∃ r : ℕ, E n d = (r : ℚ)) ↔ d + 1 ∣ N n d := by
  constructor
  · rintro ⟨r, hr⟩
    have hq : (N n d : ℚ) = (d + 1 : ℕ) * (r : ℚ) := by
      have h := (div_eq_iff (show (d : ℚ) + 1 ≠ 0 by positivity)).mp hr
      simpa only [E, Nat.cast_add, Nat.cast_one, mul_comm] using h
    exact ⟨r, by exact_mod_cast hq⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    unfold E
    rw [hr, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_div_cancel_left₀ (r : ℚ) (by positivity)

/-- At the upper endpoint of Proposition 6.1 the trace monomial count is divisible. -/
theorem induction_endpoint_divisibility (d : ℕ) (hd : 2 ≤ d) :
    d + 1 ∣ N (d * (d - 1)) d := by
  have hm : 1 ≤ d * (d - 1) := by
    have h : 1 ≤ d - 1 := by omega
    nlinarith
  have hr := N_degree_recurrence (d * (d - 1)) (d - 1) hm
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at hr
  have hfactor : d * (d - 1) + (d - 1) = (d + 1) * (d - 1) := by ring
  rw [hfactor] at hr
  have hprod : d + 1 ∣ d * N (d * (d - 1)) d := by
    rw [hr]
    exact dvd_mul_of_dvd_left (dvd_mul_right (d + 1) (d - 1)) _
  have hc : Nat.Coprime (d + 1) d := by
    have h : Nat.Coprime (1 + d) d :=
      Nat.coprime_add_self_left.mpr (by simp)
    simpa only [Nat.add_comm] using h
  exact hc.dvd_of_dvd_mul_left hprod

/-- The upper endpoint has integral same-degree trace critical value. -/
theorem induction_endpoint_trace_integral (d : ℕ) (hd : 2 ≤ d) :
    ∃ r : ℕ, E (d * (d - 1)) d = (r : ℚ) :=
  (E_integral_iff _ _).mpr (induction_endpoint_divisibility d hd)

/-- The only fractional quartic edges in the one-hyperplane range are seven and twelve variables. -/
theorem quartic_trace_integral_of_not_exception (n : ℕ)
    (hl : 4 ≤ n) (hu : n ≤ 13) (hseven : n ≠ 7) (htwelve : n ≠ 12) :
    ∃ r : ℕ, E (n - 1) 4 = (r : ℚ) := by
  apply (E_integral_iff _ _).mpr
  interval_cases n <;> norm_num [N, Nat.choose] at *

end IdealGeneration
