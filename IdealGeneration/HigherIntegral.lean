module

public import IdealGeneration.IntegralHyperplane
public import IdealGeneration.PlaneArithmetic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The residual numerical margin for the integral-trace step in degree at least four. -/

namespace IdealGeneration

/-- Six times the dimension of forms in four variables. -/
theorem six_N_four (d : ℕ) : 6 * N 4 d = (d + 1) * (d + 2) * (d + 3) := by
  induction d with
  | zero => norm_num [N]
  | succ d ih =>
    have hp := N_pascal 4 (d + 1) (by omega) (by omega)
    simp only [show 4 - 1 = 3 by decide, Nat.add_sub_cancel] at hp
    have ht := twice_N_three (d + 1)
    rw [hp]
    nlinarith

/-- At least four variables provide the integer rounding margin for degree at least three. -/
theorem N_integral_rounding_margin (n d : ℕ) (hn : 4 ≤ n) (hd : 3 ≤ d) :
    (d + 1) * (d + 2) ≤ N n d := by
  have hf := six_N_four d
  have hp := Nat.mul_le_mul_left ((d + 1) * (d + 2)) (show 6 ≤ d + 3 by omega)
  have hfour : (d + 1) * (d + 2) ≤ N 4 d := by nlinarith
  exact hfour.trans (N_mono_variables d hn)

/-- The ceiling residual requested by Corollary 3.2 lies below the preceding-degree critical value. -/
theorem ceil_hyperplaneResidualRatio_le_E (n d : ℕ) (hn : 4 ≤ n) (hd : 3 ≤ d) :
    (⌈hyperplaneResidualRatio n (d + 1)⌉₊ : ℚ) ≤ E n d := by
  have hN : ((d : ℚ) + 1) * (d + 2) ≤ N n d := by
    exact_mod_cast N_integral_rounding_margin n d hn hd
  have hgap : hyperplaneResidualRatio n (d + 1) + 1 ≤ E n d := by
    simp only [hyperplaneResidualRatio, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, E]
    calc
      (N n d : ℚ) / ((d : ℚ) + 1 + 1) + 1 =
          ((N n d : ℚ) + (d + 2)) / (d + 2) := by field_simp; ring
      _ ≤ (N n d : ℚ) / (d + 1) :=
        (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
  exact (Nat.ceil_lt_add_one (hyperplaneResidualRatio_nonneg n (d + 1))).le.trans hgap

/-- The ceiling residual also lies in the preceding initial-degree cell. -/
theorem ceil_hyperplaneResidualRatio_mem_cell (n d : ℕ) (hn : 4 ≤ n) (hd : 3 ≤ d) :
    1 ≤ ⌈hyperplaneResidualRatio n (d + 1)⌉₊ ∧
      ⌈hyperplaneResidualRatio n (d + 1)⌉₊ ≤ N n d - N n (d - 1) := by
  refine ⟨integral_trace_ceil_pos n (d + 1) (by omega), ?_⟩
  have hceil := ceil_hyperplaneResidualRatio_le_E n d hn hd
  have hwidth := E_le_cell_width n d (by omega) (by omega)
  have hpred := N_pred_le n d (by omega) (by omega)
  have hq : (⌈hyperplaneResidualRatio n (d + 1)⌉₊ : ℚ) ≤
      ((N n d - N n (d - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_sub hpred]
    exact hceil.trans hwidth
  exact_mod_cast hq

/-- Degree at least four needs only preceding-degree maximal rank in the integral-trace case. -/
theorem integral_hyperplane_transfer_of_maximal_rank
    {K : Type*} [Field K] [CharZero K]
    (m d r₂ : ℕ) (hm : 2 ≤ m) (hd : 3 ≤ d)
    (htrace : E (m + 1) (d + 1) = (r₂ : ℚ))
    (hG : IdealGenerationAt K m (d + 1) (N (m + 1) (d + 1) - r₂))
    (hprevious : IdealGenerationAt K (m + 1) d
      (N (m + 2) d - ⌈hyperplaneResidualRatio (m + 2) (d + 1)⌉₊)) :
    ∀ p, IdealGenerationAt K (m + 1) (d + 1) p := by
  have hcell := ceil_hyperplaneResidualRatio_mem_cell (m + 2) d (by omega) hd
  have hbound : ⌈hyperplaneResidualRatio (m + 2) (d + 1)⌉₊ ≤ N (m + 2) d := by omega
  apply integral_hyperplane_transfer m d r₂ (by omega) htrace hG
  exact scalarInjectionAt_of_idealGenerationAt (by omega) _ hbound
    (ceil_hyperplaneResidualRatio_le_E (m + 2) d (by omega) hd) hprevious

end IdealGeneration
