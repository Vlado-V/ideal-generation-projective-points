module

public import IdealGeneration.Numerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Numerical parameters for integral hyperplane transfer

These identities are the arithmetic in Corollary 3.2. If the trace critical
value is integral, adding the floor or ceiling residual ratio gives exactly
the corresponding ambient critical value.
-/

namespace IdealGeneration

/-- The residual ratio used by one-hyperplane specialization. -/
def hyperplaneResidualRatio (n d : ℕ) : ℚ := (N n (d - 1) : ℚ) / (d + 1)

/-- Adjacent binomial coefficients give the cross-degree identity. -/
theorem N_cross_hyperplane (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (n - 1) * N n (d - 1) = d * N (n - 1) d := by
  have h := Nat.choose_succ_right_eq (n + d - 2) (d - 1)
  have hpred : d - 1 + 1 = d := by omega
  have hdiff : n + d - 2 - (d - 1) = n - 1 := by omega
  rw [hpred, hdiff] at h
  have hleft : N n (d - 1) = (n + d - 2).choose (d - 1) := by
    unfold N
    congr 1
    omega
  have hright : N (n - 1) d = (n + d - 2).choose d := by
    unfold N
    congr 1
    omega
  rw [hleft, hright]
  simpa only [Nat.mul_comm] using h.symm

/-- Pascal's identity splits the ambient critical value into trace and residual parts. -/
theorem E_hyperplane_split (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    E n d = E (n - 1) d + hyperplaneResidualRatio n d := by
  unfold E hyperplaneResidualRatio
  rw [N_pascal n d (by omega) hd, Nat.cast_add, add_div]

/-- The residual and trace dimensions saturate the scalar-row budget. -/
theorem hyperplane_residual_balance (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ((n - 1 : ℕ) : ℚ) * hyperplaneResidualRatio n d + E (n - 1) d = N (n - 1) d := by
  have hcross : ((n - 1 : ℕ) : ℚ) * N n (d - 1) = (d : ℚ) * N (n - 1) d := by
    exact_mod_cast N_cross_hyperplane n d hn hd
  have hden : (d : ℚ) + 1 ≠ 0 := by positivity
  unfold hyperplaneResidualRatio E
  field_simp
  nlinarith [hcross]

/-- The residual ratio is nonnegative. -/
theorem hyperplaneResidualRatio_nonneg (n d : ℕ) :
    0 ≤ hyperplaneResidualRatio n d := by
  unfold hyperplaneResidualRatio
  positivity

/-- The residual ratio is positive in a positive number of variables. -/
theorem hyperplaneResidualRatio_pos (n d : ℕ) (hn : 1 ≤ n) :
    0 < hyperplaneResidualRatio n d := by
  unfold hyperplaneResidualRatio
  exact div_pos (by exact_mod_cast N_pos (d := d - 1) hn) (by positivity)

/-- An integral trace shifts the floor critical count by the floor residual ratio. -/
theorem lowerCritical_integral_trace (n d r₂ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    lowerCritical n d = r₂ + ⌊hyperplaneResidualRatio n d⌋₊ := by
  unfold lowerCritical
  rw [E_hyperplane_split n d hn hd, htrace, add_comm,
    Nat.floor_add_natCast (hyperplaneResidualRatio_nonneg n d)]
  omega

/-- An integral trace shifts the ceiling critical count by the ceiling residual ratio. -/
theorem upperCritical_integral_trace (n d r₂ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    upperCritical n d = r₂ + ⌈hyperplaneResidualRatio n d⌉₊ := by
  unfold upperCritical
  rw [E_hyperplane_split n d hn hd, htrace, add_comm,
    Nat.ceil_add_natCast (hyperplaneResidualRatio_nonneg n d)]
  omega

/-- The floor residual count satisfies the injective scalar-row budget. -/
theorem integral_trace_floor_budget (n d r₂ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    (n - 1) * ⌊hyperplaneResidualRatio n d⌋₊ + r₂ ≤ N (n - 1) d := by
  have hfloor := Nat.floor_le (hyperplaneResidualRatio_nonneg n d)
  have hbalance := hyperplane_residual_balance n d hn hd
  rw [htrace] at hbalance
  have hcoef : (0 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by positivity
  have hq : ((n - 1 : ℕ) : ℚ) * (⌊hyperplaneResidualRatio n d⌋₊ : ℚ) + r₂ ≤
      (N (n - 1) d : ℚ) := by nlinarith
  exact_mod_cast hq

/-- The ceiling residual count satisfies the surjective scalar-row budget. -/
theorem integral_trace_ceil_budget (n d r₂ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    N (n - 1) d ≤ (n - 1) * ⌈hyperplaneResidualRatio n d⌉₊ + r₂ := by
  have hceil := Nat.le_ceil (hyperplaneResidualRatio n d)
  have hbalance := hyperplane_residual_balance n d hn hd
  rw [htrace] at hbalance
  have hcoef : (0 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by positivity
  have hq : (N (n - 1) d : ℚ) ≤
      ((n - 1 : ℕ) : ℚ) * (⌈hyperplaneResidualRatio n d⌉₊ : ℚ) + r₂ := by nlinarith
  exact_mod_cast hq

/-- The surjective residual count is positive, as required by Lemma 3.1. -/
theorem integral_trace_ceil_pos (n d : ℕ) (hn : 1 ≤ n) :
    1 ≤ ⌈hyperplaneResidualRatio n d⌉₊ := by
  exact Nat.ceil_pos.mpr (hyperplaneResidualRatio_pos n d hn)


/-- Both trace critical counts agree with the given integral value. -/
theorem integral_trace_critical_values (n d r₂ : ℕ)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    lowerCritical (n - 1) d = r₂ ∧ upperCritical (n - 1) d = r₂ := by
  simp [lowerCritical, upperCritical, htrace]

/-- The integral trace value belongs to the degree-`d` point-count cell. -/
theorem integral_trace_mem_cell (n d r₂ : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d)
    (htrace : E (n - 1) d = (r₂ : ℚ)) :
    1 ≤ r₂ ∧ r₂ ≤ N (n - 1) d - N (n - 1) (d - 1) := by
  have h := lowerCritical_mem_cell (n - 1) d (by omega) hd
  rw [(integral_trace_critical_values n d r₂ htrace).1] at h
  exact h

end IdealGeneration
