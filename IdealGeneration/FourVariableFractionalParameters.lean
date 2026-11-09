module

public import IdealGeneration.FractionalTraceNumerics
public import IdealGeneration.PlaneArithmetic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Explicit parameters of the four-variable fractional step in odd degree. -/

namespace IdealGeneration

/-- The lower ternary critical count in odd degree. -/
theorem four_fractional_tau (k : ℕ) :
    lowerCritical 3 (2 * k + 1) = k + 1 := by
  rw [lowerCritical_three]
  omega

/-- The upper ternary critical count in odd degree. -/
theorem four_fractional_upper_trace (k : ℕ) :
    upperCritical 3 (2 * k + 1) = k + 2 := by
  rw [upperCritical_three]
  omega

/-- Every odd degree gives a fractional ternary trace. -/
theorem four_fractional_trace (k : ℕ) :
    upperCritical 3 (2 * k + 1) = lowerCritical 3 (2 * k + 1) + 1 := by
  rw [four_fractional_tau, four_fractional_upper_trace]

/-- The first fractional trace fiber is one-dimensional. -/
theorem four_fractional_top_dimension (k : ℕ) :
    fractionalTopTraceDimension 4 (2 * k + 1) = 1 := by
  unfold fractionalTopTraceDimension ambientComplementaryResidue ambientResidue
  norm_num only [Nat.reduceSub, N_two_variables]
  omega

/-- The ternary scalar count in the lower even degree. -/
theorem four_fractional_N_lower (k : ℕ) :
    N 3 (2 * k) = (2 * k + 1) * (k + 1) := by
  have h := twice_N_three (2 * k)
  nlinarith

/-- The ternary scalar count in the upper even degree. -/
theorem four_fractional_N_upper (k : ℕ) :
    N 3 (2 * k + 2) = (2 * k + 3) * (k + 2) := by
  have h := twice_N_three (2 * k + 2)
  nlinarith

/-- The lower-level fractional defect in odd degree. -/
theorem four_fractional_defect (k : ℕ) (hk : 1 ≤ k) :
    fractionalTraceDefect 4 (2 * k + 1) = 4 * k * k + 2 * k - 3 := by
  unfold fractionalTraceDefect
  norm_num only [Nat.reduceSub]
  rw [show 2 * k + 1 - 1 = 2 * k by omega,
    show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    four_fractional_N_lower, four_fractional_N_upper]
  have hlo : (2 * k + 3) * (k + 2) ≤ 3 * ((2 * k + 1) * (k + 1)) := by nlinarith
  have hquad : 3 ≤ 4 * k * k + 2 * k := by nlinarith
  have hpoly : 3 * ((2 * k + 1) * (k + 1)) + 3 =
      (2 * k + 3) * (k + 2) + (4 * k * k + 2 * k) := by ring
  omega

/-- The selected scalar-row count in odd degree. -/
theorem four_fractional_rows (k : ℕ) (hk : 1 ≤ k) :
    fractionalTraceRows 4 (2 * k + 1) = 2 * k * k + k - 2 := by
  unfold fractionalTraceRows
  rw [four_fractional_defect k hk]
  norm_num only [Nat.reduceSub]
  have hquad : 2 ≤ 2 * k * k + k := by nlinarith
  have hpoly : 4 * k * k + 2 * k = 2 * (2 * k * k + k) := by ring
  omega

/-- The remaining lower-level fiber is one-dimensional. -/
theorem four_fractional_remainder (k : ℕ) (hk : 1 ≤ k) :
    fractionalTraceRemainder 4 (2 * k + 1) = 1 := by
  unfold fractionalTraceRemainder
  rw [four_fractional_defect k hk]
  norm_num only [Nat.reduceSub]
  have hquad : 3 ≤ 4 * k * k + 2 * k := by nlinarith
  have hpoly : 4 * k * k + 2 * k = 2 * (2 * k * k + k) := by ring
  omega

/-- The defect is nonnegative before taking natural subtraction. -/
theorem four_fractional_defect_nonnegative (k : ℕ) (hk : 1 ≤ k) :
    N (4 - 1) (2 * k + 1 + 1) ≤
      (4 - 1) * N (4 - 1) (2 * k + 1 - 1) := by
  norm_num only [Nat.reduceSub]
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    show 2 * k + 1 - 1 = 2 * k by omega,
    four_fractional_N_lower, four_fractional_N_upper]
  nlinarith

/-- The ambient residue takes only the two values shown in the paper. -/
theorem four_fractional_residue_cases (k : ℕ) :
    ambientResidue 4 (2 * k + 1) = 0 ∨ ambientResidue 4 (2 * k + 1) = 1 := by
  unfold ambientResidue
  norm_num only [Nat.reduceSub]
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, four_fractional_N_upper]
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;>
    norm_num [Nat.mul_mod, Nat.add_mod, h]

/-- The complementary ambient residue is twice the ordinary one. -/
theorem four_fractional_complement (k : ℕ) :
    ambientComplementaryResidue 4 (2 * k + 1) = 2 * ambientResidue 4 (2 * k + 1) := by
  unfold ambientComplementaryResidue
  norm_num only [Nat.reduceSub]
  rcases four_fractional_residue_cases k with h | h <;> simp [h]

/-- The complementary residue is zero or two. -/
theorem four_fractional_complement_cases (k : ℕ) :
    ambientComplementaryResidue 4 (2 * k + 1) = 0 ∨
      ambientComplementaryResidue 4 (2 * k + 1) = 2 := by
  rw [four_fractional_complement]
  rcases four_fractional_residue_cases k with h | h <;> simp [h]

/-- The injective residual dimension in the four-variable odd-degree step. -/
theorem four_fractional_residualI (k : ℕ) (hk : 1 ≤ k) :
    fractionalResidualI 4 (2 * k + 1) =
      ((2 : ℚ) * k * k + k - ambientResidue 4 (2 * k + 1)) / 3 := by
  unfold fractionalResidualI
  rw [four_fractional_rows k hk, four_fractional_remainder k hk]
  have hquad : 2 ≤ 2 * k * k + k := by nlinarith
  norm_num only [Nat.reduceSub, Nat.cast_sub hquad, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The surjective residual dimension in the four-variable odd-degree step. -/
theorem four_fractional_residualS (k : ℕ) (hk : 1 ≤ k) :
    fractionalResidualS 4 (2 * k + 1) =
      ((2 : ℚ) * k * k + k + ambientComplementaryResidue 4 (2 * k + 1)) / 3 := by
  unfold fractionalResidualS
  rw [four_fractional_rows k hk, four_fractional_remainder k hk]
  have hquad : 2 ≤ 2 * k * k + k := by nlinarith
  norm_num only [Nat.reduceSub, Nat.cast_sub hquad, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

end IdealGeneration
