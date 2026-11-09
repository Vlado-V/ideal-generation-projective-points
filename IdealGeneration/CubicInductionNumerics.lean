module

public import IdealGeneration.InductionNumerics
public import IdealGeneration.IntegralTraceNumerics
public import Mathlib.Data.Nat.ModEq

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Counts for the cubic induction

The cubic critical value is integral in five residue classes modulo eight.
The one-hyperplane residual count lies on the injective side of the
quadratic critical value.
-/

namespace IdealGeneration

/-- The closed quadratic monomial count, including zero variables. -/
theorem twice_N_quadratic (n : ℕ) : 2 * N n 2 = n * (n + 1) := by
  by_cases hn : 1 ≤ n
  · have h := N_degree_recurrence n 1 hn
    simpa only [N_one_degree, Nat.reduceAdd, Nat.mul_comm] using h
  · have hn₀ : n = 0 := by omega
    subst n
    norm_num [N, Nat.choose]

/-- The closed cubic monomial count, including zero variables. -/
theorem six_mul_N_cubic (m : ℕ) : 6 * N m 3 = m * (m + 1) * (m + 2) := by
  by_cases hm : 1 ≤ m
  · have h : 3 * N m 3 = (m + 2) * N m 2 := N_degree_recurrence m 2 hm
    calc
      6 * N m 3 = 2 * (3 * N m 3) := by ring
      _ = 2 * ((m + 2) * N m 2) := by rw [h]
      _ = (2 * N m 2) * (m + 2) := by ring
      _ = _ := by rw [twice_N_quadratic]
  · have hm₀ : m = 0 := by omega
    subst m
    norm_num [N, Nat.choose]

/-- The cubic trace critical value is integral exactly in the residue
classes used by the ordinary hyperplane and two-normal steps. -/
theorem cubic_E_integral_iff_mod_eight (m : ℕ) :
    (∃ r : ℕ, E m 3 = (r : ℚ)) ↔ m % 8 ≠ 1 ∧ m % 8 ≠ 3 ∧ m % 8 ≠ 5 := by
  have h₄ : 4 ∣ N m 3 ↔ 24 ∣ m * (m + 1) * (m + 2) := by
    rw [← six_mul_N_cubic]
    change 4 ∣ N m 3 ↔ 6 * 4 ∣ 6 * N m 3
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 6)).symm
  have h₃ : 3 ∣ m * (m + 1) * (m + 2) := by
    rw [← six_mul_N_cubic]
    exact (by decide : 3 ∣ 6).trans (dvd_mul_right 6 _)
  have h₈ : 24 ∣ m * (m + 1) * (m + 2) ↔ 8 ∣ m * (m + 1) * (m + 2) := by
    constructor
    · exact fun h => (by decide : 8 ∣ 24).trans h
    · exact fun h => (by decide : Nat.Coprime 3 8).mul_dvd_of_dvd_of_dvd h₃ h
  rw [E_integral_iff]
  change 4 ∣ N m 3 ↔ _
  rw [h₄, h₈, Nat.dvd_iff_mod_eq_zero]
  set a := m % 8
  have ha : a < 8 := Nat.mod_lt _ (by decide)
  have hmod : a ≡ m [MOD 8] := Nat.mod_modEq _ _
  have hprod := (hmod.mul (hmod.add_right 1)).mul (hmod.add_right 2)
  change (a * (a + 1) * (a + 2)) % 8 = (m * (m + 1) * (m + 2)) % 8 at hprod
  rw [← hprod]
  interval_cases a <;> decide

/-- The rounded cubic residual count is at most the quadratic critical value. -/
theorem ceil_cubic_hyperplaneResidualRatio_le_E (n : ℕ) (hn : 5 ≤ n) :
    (⌈hyperplaneResidualRatio n 3⌉₊ : ℚ) ≤ E n 2 := by
  have h₀ : 12 ≤ N n 2 :=
    (show 12 ≤ N 5 2 by decide).trans (N_mono_variables 2 hn)
  have hN : (12 : ℚ) ≤ N n 2 := by exact_mod_cast h₀
  have hgap : hyperplaneResidualRatio n 3 + 1 ≤ E n 2 := by
    norm_num [hyperplaneResidualRatio, E]
    linarith
  exact (Nat.ceil_lt_add_one (hyperplaneResidualRatio_nonneg n 3)).le.trans hgap

/-- Two added variables increase the cubic monomial count by the square of
the new number of variables. -/
theorem cubic_N_add_two (m : ℕ) : N (m + 2) 3 = N m 3 + (m + 2) ^ 2 := by
  have h₁ : N (m + 2) 3 = N (m + 1) 3 + N (m + 2) 2 :=
    N_pascal (m + 2) 3 (by omega) (by decide)
  have h₂ : N (m + 1) 3 = N m 3 + N (m + 1) 2 :=
    N_pascal (m + 1) 3 (by omega) (by decide)
  have hsum : N (m + 1) 2 + N (m + 2) 2 = (m + 2) ^ 2 := by
    nlinarith only [twice_N_quadratic (m + 1), twice_N_quadratic (m + 2)]
  omega

/-- Three-fourths of the cubic scalar count leaves exactly the critical
dimension in the point ideal. -/
theorem E_cubic_eq_of_three_fourths (m q : ℕ) (h : 4 * q = 3 * N m 3) :
    E m 3 = ((N m 3 - q : ℕ) : ℚ) := by
  have hq : q ≤ N m 3 := by omega
  have hQ : (4 : ℚ) * q = 3 * N m 3 := by exact_mod_cast h
  rw [Nat.cast_sub hq]
  norm_num [E]
  linarith

end IdealGeneration
