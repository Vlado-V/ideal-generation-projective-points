module

public import IdealGeneration.Numerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace IdealGeneration

/-- Twice the dimension of ternary degree-`d` forms. -/
theorem twice_N_three (d : ℕ) : 2 * N 3 d = (d + 1) * (d + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp := N_pascal 3 (d + 1) (by omega) (by omega)
    simp only [show 3 - 1 = 2 by decide, Nat.add_sub_cancel, N_two_variables] at hp
    rw [hp]
    nlinarith

/-- The plane critical value has a linear expression. -/
theorem E_three (d : ℕ) : E 3 d = ((d : ℚ) + 2) / 2 := by
  have h : (2 : ℚ) * N 3 d = ((d : ℚ) + 1) * (d + 2) := by
    exact_mod_cast twice_N_three d
  unfold E
  have hd : (d : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The two plane critical ideal dimensions. -/
theorem lowerCritical_three (d : ℕ) : lowerCritical 3 d = (d + 2) / 2 := by
  unfold lowerCritical
  rw [E_three]
  rw [show ((d : ℚ) + 2) / 2 = ((d + 2 : ℕ) : ℚ) / (2 : ℕ) by norm_cast]
  exact Rat.natFloor_natCast_div_natCast _ _

theorem upperCritical_three (d : ℕ) : upperCritical 3 d = (d + 3) / 2 := by
  unfold upperCritical
  rw [E_three]
  let c := (d + 3) / 2
  have hc : c ≠ 0 := by dsimp [c]; omega
  apply (Nat.ceil_eq_iff hc).mpr
  constructor
  · have h : 2 * (c - 1) < d + 2 := by dsimp [c]; omega
    have hq : (2 : ℚ) * (c - 1 : ℕ) < (d : ℚ) + 2 := by exact_mod_cast h
    nlinarith
  · have h : d + 2 ≤ 2 * c := by dsimp [c]; omega
    have hq : (d : ℚ) + 2 ≤ (2 : ℚ) * c := by exact_mod_cast h
    nlinarith

/-- The lower critical count is one plus the lower residual count. -/
theorem lowerCritical_three_split (d : ℕ) : lowerCritical 3 d = d / 2 + 1 := by
  rw [lowerCritical_three]
  omega

/-- The upper critical count is one plus the upper residual count. -/
theorem upperCritical_three_split (d : ℕ) : upperCritical 3 d = (d + 1) / 2 + 1 := by
  rw [upperCritical_three]
  omega

/-- The width of the ternary initial-degree cell. -/
theorem N_three_cell_width (d : ℕ) (hd : 1 ≤ d) :
    N 3 d - N 3 (d - 1) = d + 1 := by
  have h := N_pascal 3 d (by omega) hd
  simp only [show 3 - 1 = 2 by decide, N_two_variables] at h
  omega

/-- Both residual counts lie in the preceding-degree cell. -/
theorem plane_residual_cell (d : ℕ) (hd : 2 ≤ d) :
    1 ≤ d / 2 ∧ 1 ≤ (d + 1) / 2 ∧
      d / 2 ≤ N 3 (d - 1) - N 3 (d - 2) ∧
      (d + 1) / 2 ≤ N 3 (d - 1) - N 3 (d - 2) := by
  have h := N_three_cell_width (d - 1) (by omega)
  have he : d - 1 - 1 = d - 2 := by omega
  rw [he] at h
  omega

/-- Both preceding-degree residual dimensions are on the injective side. -/
theorem plane_residual_below_critical (d : ℕ) (hd : 2 ≤ d) :
    (d / 2 : ℕ) ≤ E 3 (d - 1) ∧ ((d + 1) / 2 : ℕ) ≤ E 3 (d - 1) := by
  rw [E_three]
  have hcast : ((d - 1 : ℕ) : ℚ) = (d : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcast]
  have hl : 2 * (d / 2) ≤ d := by omega
  have hu : 2 * ((d + 1) / 2) ≤ d + 1 := by omega
  have hlq : (2 : ℚ) * (d / 2 : ℕ) ≤ d := by exact_mod_cast hl
  have huq : (2 : ℚ) * ((d + 1) / 2 : ℕ) ≤ (d : ℚ) + 1 := by exact_mod_cast hu
  constructor <;> nlinarith

/-- The scalar row budgets in the two plane transfers. -/
theorem plane_residual_budgets (d : ℕ) :
    2 * (d / 2) + 1 ≤ d + 1 ∧ d + 1 ≤ 2 * ((d + 1) / 2) + 1 := by
  omega

end IdealGeneration
