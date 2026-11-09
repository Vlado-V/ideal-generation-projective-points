module

public import IdealGeneration.TwoNormalIntegral
public import IdealGeneration.HigherFractionalBoundsAux

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Numerical margins for the integral two-normal transfer in Proposition 4.5. -/

namespace IdealGeneration.TwoNormalIntegral

set_option maxHeartbeats 1500000

private theorem dimension_lower_bounds (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : 3 * D ≤ m ∧ 12 ≤ m := by
  have hmul := Nat.mul_le_mul_left D (show 3 ≤ D - 1 by omega)
  constructor <;> nlinarith

/-- The lower scalar slice dimension fits at least `D` times into the middle dimension. -/
theorem degree_times_lower_le_middle (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : D * N (m + 1) (D - 2) ≤ N m (D - 1) := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hc := N_cross_hyperplane (m + 1) (D - 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, show D - 1 - 1 = D - 2 by omega] at hc
  have hprod := Nat.mul_le_mul_right (N (m + 1) (D - 2)) hm
  apply Nat.le_of_mul_le_mul_left (c := D - 1) _ (by omega)
  nlinarith [hc, hprod]

private theorem slice_pascal (m D : ℕ) (hD : 4 ≤ D) :
    N (m + 1) (D - 1) = N m (D - 1) + N (m + 1) (D - 2) := by
  simpa only [Nat.add_sub_cancel, show D - 1 - 1 = D - 2 by omega] using
    N_pascal (m + 1) (D - 1) (by omega) (by omega)

/-- The chosen ceiling count lies on the injective side of the middle slice. -/
theorem sliceCount_le_middle (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : sliceCount m D ≤ N m (D - 1) := by
  have hlow := degree_times_lower_le_middle m D hD hm
  have hp := slice_pascal m D hD
  have hn : D * N (m + 1) (D - 1) ≤ (D + 1) * N m (D - 1) := by
    nlinarith
  unfold sliceCount
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < D + 1)).2
  exact_mod_cast (show D * N (m + 1) (D - 1) ≤ N m (D - 1) * (D + 1) by
    simpa only [Nat.mul_comm] using hn)

/-- In fact the slice count dominates `D` times the lower-degree dimension. -/
theorem degree_times_lower_le_sliceCount (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : D * N (m + 1) (D - 2) ≤ sliceCount m D := by
  have hlow := degree_times_lower_le_middle m D hD hm
  have hp := slice_pascal m D hD
  have hn : (D + 1) * N (m + 1) (D - 2) ≤ N (m + 1) (D - 1) := by nlinarith
  have hq : ((D + 1 : ℕ) : ℚ) * N (m + 1) (D - 2) ≤ N (m + 1) (D - 1) := by
    exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hq (show (0 : ℚ) ≤ D by positivity)
  have htarget : ((D * N (m + 1) (D - 2) : ℕ) : ℚ) ≤
      (D : ℚ) * N (m + 1) (D - 1) / (D + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < D + 1)).2
    push_cast
    push_cast at hmul
    nlinarith
  have hceil := Nat.le_ceil ((D : ℚ) * N (m + 1) (D - 1) / (D + 1))
  change _ ≤ (sliceCount m D : ℚ) at hceil
  exact_mod_cast htarget.trans hceil

/-- The lower-degree slice has no more points than the selected slice count. -/
theorem lower_le_sliceCount (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : N (m + 1) (D - 2) ≤ sliceCount m D := by
  have h := degree_times_lower_le_sliceCount m D hD hm
  nlinarith

/-- The middle scalar dimension is strictly below the slice width. -/
theorem middle_lt_sliceWidth (m D : ℕ) (hD : 4 ≤ D) :
    N m (D - 1) < N (m + 1) (D - 1) := by
  rw [slice_pascal m D hD]
  have h := N_pos (d := D - 2) (show 1 ≤ m + 1 by omega)
  omega

/-- The number of unfilled slice rows is strictly less than `L / D`. -/
theorem sliceCount_gap_lt (m D : ℕ) (hD : 4 ≤ D) :
    (N (m + 1) (D - 1) : ℚ) - sliceCount m D <
      (N (m + 1) (D - 1) : ℚ) / D := by
  have hc := Nat.le_ceil ((D : ℚ) * N (m + 1) (D - 1) / (D + 1))
  change _ ≤ (sliceCount m D : ℚ) at hc
  have hL : (0 : ℚ) < N (m + 1) (D - 1) := by
    exact_mod_cast N_pos (d := D - 1) (show 1 ≤ m + 1 by omega)
  have hDq : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  have hgap : (N (m + 1) (D - 1) : ℚ) / (D + 1) <
      (N (m + 1) (D - 1) : ℚ) / D := by
    rw [div_lt_div_iff₀ (by positivity) hDq]
    nlinarith
  have hid : (N (m + 1) (D - 1) : ℚ) -
      (D : ℚ) * N (m + 1) (D - 1) / (D + 1) =
      (N (m + 1) (D - 1) : ℚ) / (D + 1) := by
    field_simp
    ring
  linarith

/-- The four slice-count margins used in the first injection of Proposition 4.5. -/
theorem sliceCount_margins (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    N (m + 1) (D - 2) ≤ sliceCount m D ∧
      sliceCount m D ≤ N m (D - 1) ∧
      N m (D - 1) < N (m + 1) (D - 1) ∧
      (N (m + 1) (D - 1) : ℚ) - sliceCount m D <
        (N (m + 1) (D - 1) : ℚ) / D :=
  ⟨lower_le_sliceCount m D hD hm, sliceCount_le_middle m D hD hm,
    middle_lt_sliceWidth m D hD, sliceCount_gap_lt m D hD⟩

end IdealGeneration.TwoNormalIntegral

namespace IdealGeneration.TwoNormalIntegral

set_option maxHeartbeats 2000000

private theorem twice_N_quadratic (m : ℕ) (hm : 1 ≤ m) :
    2 * N m 2 = m * (m + 1) := by
  have h := N_degree_recurrence m 1 hm
  simpa only [N_one_degree, Nat.reduceAdd, Nat.mul_comm] using h

private theorem two_variable_count_ratio (m D : ℕ) (hm : 1 ≤ m) (hD : 4 ≤ D) :
    m * (m + 1) * N (m + 2) (D - 2) =
      (m + D - 2) * (m + D - 1) * N m (D - 2) := by
  have h₀ := N_variable_ratio (m + 1) (D - 2) (by omega) (by omega)
  have h₁ := N_variable_ratio (m + 2) (D - 2) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, show m + 1 + (D - 2) - 1 = m + D - 2 by omega] at h₀
  simp only [show m + 2 - 1 = m + 1 by omega,
    show m + 2 + (D - 2) - 1 = m + D - 1 by omega] at h₁
  calc
    _ = m * ((m + 1) * N (m + 2) (D - 2)) := by ring
    _ = m * ((m + D - 1) * N (m + 1) (D - 2)) := by rw [h₁]
    _ = (m + D - 1) * (m * N (m + 1) (D - 2)) := by ring
    _ = (m + D - 1) * ((m + D - 2) * N m (D - 2)) := by rw [h₀]
    _ = _ := by ring

/-- The binomial gap in (4.3) is at least five under the stated numerical hypotheses. -/
theorem residual_binomial_gap (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    5 ≤ (N m (D - 2) : ℚ) / (D - 1 : ℕ) -
      (N (m + 2) (D - 2) : ℚ) / (D + 1) := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hmpos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hDq : (4 : ℚ) ≤ D := by exact_mod_cast hD
  have hdminus : (0 : ℚ) < (D : ℚ) - 1 := by linarith
  have hdplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hmarg : (0 : ℚ) ≤ (m : ℚ) - D * ((D : ℚ) - 1) := by
    have h₀ : (D : ℚ) * ((D - 1 : ℕ) : ℚ) ≤ m := by exact_mod_cast hm
    have h : (D : ℚ) * ((D : ℚ) - 1) ≤ m := by
      simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using h₀
    linarith
  have hbase := N_mono_degree m (by omega) (show 2 ≤ D - 2 by omega)
  have hquad := twice_N_quadratic m (by omega)
  have hMe : (m : ℚ) * (m + 1) / 2 ≤ N m (D - 2) := by
    have hq : (m : ℚ) * (m + 1) ≤ 2 * N m (D - 2) := by
      exact_mod_cast (show m * (m + 1) ≤ 2 * N m (D - 2) by omega)
    linarith
  let T : ℚ := ((D : ℚ) + 1) * m * (m + 1) -
    ((D : ℚ) - 1) * (m + D - 2) * (m + D - 1)
  have hTidentity : T = (((D : ℚ) ^ 2 - 1) * (3 * D - 2)) +
      2 * ((m : ℚ) - D * (D - 1)) * (m + 2 * D - 1) := by
    dsimp [T]
    ring
  have hT : 10 * (((D : ℚ) - 1) * (D + 1)) ≤ T := by
    have hprod : (0 : ℚ) ≤
        2 * ((m : ℚ) - D * (D - 1)) * (m + 2 * D - 1) := by
      apply mul_nonneg (mul_nonneg (by norm_num) hmarg)
      have : (4 : ℚ) ≤ D := by exact_mod_cast hD
      linarith
    have hDq : (4 : ℚ) ≤ D := by exact_mod_cast hD
    have hpoly : 0 ≤ (((D : ℚ) ^ 2 - 1) * (3 * D - 12)) := by
      apply mul_nonneg <;> nlinarith
    nlinarith [hTidentity]
  have hprod := mul_le_mul hMe hT (by positivity :
      (0 : ℚ) ≤ 10 * (((D : ℚ) - 1) * (D + 1)))
    (show (0 : ℚ) ≤ N m (D - 2) by positivity)
  have hratio : (m : ℚ) * (m + 1) * N (m + 2) (D - 2) =
      (m + D - 2) * (m + D - 1) * (N m (D - 2) : ℚ) := by
    have h := two_variable_count_ratio m D (by omega) hD
    have hq : (m : ℚ) * (m + 1) * N (m + 2) (D - 2) =
        ((m + D - 2 : ℕ) : ℚ) * ((m + D - 1 : ℕ) : ℚ) * N m (D - 2) := by
      exact_mod_cast h
    simpa only [Nat.cast_sub (show 2 ≤ m + D by omega),
      Nat.cast_sub (show 1 ≤ m + D by omega), Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hq
  have hclear : (N m (D - 2) : ℚ) * T = (m : ℚ) * (m + 1) *
      (((D : ℚ) + 1) * N m (D - 2) - ((D : ℚ) - 1) * N (m + 2) (D - 2)) := by
    dsimp [T]
    calc
      _ = (m : ℚ) * (m + 1) * ((D : ℚ) + 1) * N m (D - 2) -
          ((D : ℚ) - 1) * ((m + D - 2) * (m + D - 1) * N m (D - 2)) := by ring
      _ = _ := by rw [← hratio]; ring
  have hbound : 5 * (((D : ℚ) - 1) * (D + 1)) ≤
      ((D : ℚ) + 1) * N m (D - 2) - ((D : ℚ) - 1) * N (m + 2) (D - 2) := by
    apply (mul_le_mul_iff_of_pos_left (mul_pos hmpos (show (0 : ℚ) < m + 1 by positivity))).mp
    rw [← hclear]
    nlinarith [hprod]
  have hdcast : ((D - 1 : ℕ) : ℚ) = (D : ℚ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one]
  rw [hdcast]
  have heq : (N m (D - 2) : ℚ) / ((D : ℚ) - 1) -
      (N (m + 2) (D - 2) : ℚ) / ((D : ℚ) + 1) =
      (((D : ℚ) + 1) * N m (D - 2) - ((D : ℚ) - 1) * N (m + 2) (D - 2)) /
        (((D : ℚ) - 1) * (D + 1)) := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ (mul_pos hdminus hdplus)).2 hbound

/-- The coarse residual interval follows from the floor/ceiling and slice rounding errors. -/
theorem residualDimension_rough_bounds (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < residualDimension m D r ∧
      residualDimension m D r < (N (m + 2) (D - 2) : ℚ) / (D + 1) + 3 := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hmono := N_mono_degree (m + 2) (by omega) (show 1 ≤ D - 2 by omega)
  rw [N_one_degree] at hmono
  have hC : (D : ℚ) + 1 < N (m + 2) (D - 2) := by
    exact_mod_cast (show D + 1 < N (m + 2) (D - 2) by omega)
  have hdiv : (1 : ℚ) < (N (m + 2) (D - 2) : ℚ) / (D + 1) := by
    exact (lt_div_iff₀ (by positivity)).2 (by simpa using hC)
  have hδ := criticalDeviation_bounds m D r hr
  have hθ := sliceRounding_bounds m D
  unfold residualDimension
  constructor <;> linarith

/-- The residual component lies strictly on its injective side. -/
theorem residualDimension_bounds (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < residualDimension m D r ∧
      residualDimension m D r < (N m (D - 2) : ℚ) / (D - 1 : ℕ) := by
  have hg := residualDimension_rough_bounds m D r hD hm hr
  have hgap := residual_binomial_gap m D hD hm
  constructor <;> linarith

/-- The ambient lower-degree scalar count dominates the degree-dependent quadratic bound. -/
private theorem ambient_lower_count_large (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    3 * ((D : ℚ) ^ 2 - 1) < N (m + 2) (D - 2) := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hvar := N_mono_variables 2 (show 3 * D + 2 ≤ m + 2 by omega)
  have hdeg := N_mono_degree (m + 2) (by omega) (show 2 ≤ D - 2 by omega)
  have hbase := twice_N_quadratic (3 * D + 2) (by omega)
  have hcount : (3 * D + 2) * (3 * D + 3) ≤ 2 * N (m + 2) (D - 2) := by
    nlinarith
  have hq : ((3 : ℚ) * D + 2) * (3 * D + 3) ≤ 2 * N (m + 2) (D - 2) := by
    exact_mod_cast hcount
  have hDq : (4 : ℚ) ≤ D := by exact_mod_cast hD
  nlinarith [sq_nonneg (D : ℚ)]

/-- The slice width is large enough for the rounding loss in (4.4). -/
theorem sliceWidth_rounding_margin (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    3 * ((m : ℚ) + 1) * (D + 1) < N (m + 1) (D - 1) := by
  have hC := ambient_lower_count_large m D hD hm
  have hcross : ((m : ℚ) + 1) * N (m + 2) (D - 2) =
      ((D : ℚ) - 1) * N (m + 1) (D - 1) := by
    have hbounds := dimension_lower_bounds m D hD hm
    have h := (cross_degree_counts m D (by omega) (by omega)).2
    have hq : ((m : ℚ) + 1) * N (m + 2) (D - 2) =
        ((D - 1 : ℕ) : ℚ) * N (m + 1) (D - 1) := by exact_mod_cast h
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hq
  have hmul := mul_lt_mul_of_pos_left hC (show (0 : ℚ) < m + 1 by positivity)
  apply (mul_lt_mul_iff_of_pos_left (show (0 : ℚ) < (D : ℚ) - 1 by
    have hDq : (4 : ℚ) ≤ D := by exact_mod_cast hD
    linarith)).mp
  nlinarith [hcross, hmul]

/-- The pure residual subspaces fit inside either set of slice evaluations. -/
theorem residualDimension_slice_margin (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    ((m : ℚ) + 1) * residualDimension m D r < sliceCount m D := by
  have hg := (residualDimension_rough_bounds m D r hD hm hr).2
  have hL := sliceWidth_rounding_margin m D hD hm
  have hcross : ((m : ℚ) + 1) * N (m + 2) (D - 2) =
      ((D : ℚ) - 1) * N (m + 1) (D - 1) := by
    have hbounds := dimension_lower_bounds m D hD hm
    have h := (cross_degree_counts m D (by omega) (by omega)).2
    have hq : ((m : ℚ) + 1) * N (m + 2) (D - 2) =
        ((D - 1 : ℕ) : ℚ) * N (m + 1) (D - 1) := by exact_mod_cast h
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hq
  have hDplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hg₁ := mul_lt_mul_of_pos_left hg hDplus
  have hcancel : ((D : ℚ) + 1) *
      ((N (m + 2) (D - 2) : ℚ) / (D + 1) + 3) =
      N (m + 2) (D - 2) + 3 * ((D : ℚ) + 1) := by
    field_simp
  rw [hcancel] at hg₁
  have hg₂ := mul_lt_mul_of_pos_left hg₁ (show (0 : ℚ) < m + 1 by positivity)
  have hb := Nat.le_ceil ((D : ℚ) * N (m + 1) (D - 1) / (D + 1))
  change _ ≤ (sliceCount m D : ℚ) at hb
  have hb₁ := (div_le_iff₀ hDplus).mp hb
  apply (mul_lt_mul_iff_of_pos_left hDplus).mp
  nlinarith [hg₂, hb₁, hcross, hL]

end IdealGeneration.TwoNormalIntegral

namespace IdealGeneration.TwoNormalIntegral

set_option maxHeartbeats 2000000

/-- The rational formula for the number of trace points. -/
def tracePointCountQ (m D : ℕ) : ℚ :=
  (D : ℚ) * N m D / (D + 1)

/-- The rational formula for the number of attached points. -/
def attachedPointCountQ (m D r : ℕ) : ℚ :=
  (D : ℚ) * (2 * N (m + 1) (D - 1) + N (m + 2) (D - 2)) / (D + 1) -
    criticalDeviation m D r

/-- The rational formula after removing the two sets of slice points. -/
def offSlicePointCountQ (m D r : ℕ) : ℚ :=
  attachedPointCountQ m D r - 2 * sliceCount m D

/-- The trace point count has the stronger margin in (4.5). -/
theorem degree_times_middle_le_tracePointCountQ (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    ((D - 1 : ℕ) : ℚ) * N m (D - 1) ≤ tracePointCountQ m D := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hrec := N_degree_recurrence m (D - 1) (by omega)
  rw [show D - 1 + 1 = D by omega] at hrec
  have hcoef : (D - 1) * (D + 1) ≤ m + (D - 1) := by nlinarith
  have hp := Nat.mul_le_mul_right (N m (D - 1)) hcoef
  have hnum : (D - 1) * N m (D - 1) * (D + 1) ≤ D * N m D := by nlinarith
  unfold tracePointCountQ
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < D + 1)).2
  exact_mod_cast hnum

/-- The trace points suffice for scalar evaluation in degree `D - 1`. -/
theorem middle_le_tracePointCountQ (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) : (N m (D - 1) : ℚ) ≤ tracePointCountQ m D := by
  have h := Nat.mul_le_mul_right (N m (D - 1)) (show 1 ≤ D - 1 by omega)
  have h₀ : (N m (D - 1) : ℚ) ≤ ((D - 1 : ℕ) : ℚ) * N m (D - 1) := by
    exact_mod_cast (show N m (D - 1) ≤ (D - 1) * N m (D - 1) by simpa using h)
  exact h₀.trans (degree_times_middle_le_tracePointCountQ m D hD hm)

private theorem degree_times_ambient_lower_lt_width (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) :
    D * N (m + 2) (D - 2) < N (m + 1) (D - 1) := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hc := (cross_degree_counts m D (by omega) (by omega)).2
  have hscaled := congrArg (fun z : ℕ => D * z) hc
  have hpos := N_pos (d := D - 1) (show 1 ≤ m + 1 by omega)
  have hmul := Nat.mul_lt_mul_of_pos_right (show D * (D - 1) < m + 1 by omega) hpos
  apply Nat.lt_of_mul_lt_mul_left (a := m + 1)
  nlinarith [hscaled, hmul]

/-- There are strictly more trace points than attached points. -/
theorem attachedPointCountQ_lt_tracePointCountQ (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    attachedPointCountQ m D r < tracePointCountQ m D := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hdplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hDF : (D : ℚ) * N m D = (m : ℚ) * N (m + 1) (D - 1) := by
    exact_mod_cast (cross_degree_counts m D (by omega) (by omega)).1
  have hDC : (D : ℚ) * N (m + 2) (D - 2) < N (m + 1) (D - 1) := by
    exact_mod_cast degree_times_ambient_lower_lt_width m D hD hm
  have hmcoef : 2 * (D : ℚ) + 2 ≤ m := by
    exact_mod_cast (show 2 * D + 2 ≤ m by omega)
  have hmprod := mul_le_mul_of_nonneg_right hmcoef
    (show (0 : ℚ) ≤ N (m + 1) (D - 1) by positivity)
  have hδ := mul_lt_mul_of_pos_left (criticalDeviation_bounds m D r hr).1 hdplus
  have hLwide := sliceWidth_rounding_margin m D hD hm
  have hcoef : (1 : ℚ) ≤ 3 * ((m : ℚ) + 1) := by
    have hnonneg : (0 : ℚ) ≤ m := by positivity
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt hdplus)
  have hL : (D : ℚ) + 1 < N (m + 1) (D - 1) := by
    exact (by simpa only [one_mul] using hmul :
      (D : ℚ) + 1 ≤ 3 * ((m : ℚ) + 1) * ((D : ℚ) + 1)).trans_lt hLwide
  apply (mul_lt_mul_iff_of_pos_left hdplus).mp
  simp only [attachedPointCountQ, tracePointCountQ, mul_sub, mul_div_cancel₀ _ hdplus.ne']
  nlinarith [hDF, hDC, hmprod, hδ, hL]

/-- Removing the two slice sets leaves the scalar dimension minus the residual ideal dimension. -/
theorem offSlicePointCountQ_eq (m D r : ℕ) :
    offSlicePointCountQ m D r = (N (m + 2) (D - 2) : ℚ) - residualDimension m D r := by
  unfold offSlicePointCountQ attachedPointCountQ residualDimension sliceRounding
  field_simp
  ring

/-- The off-slice count is positive and lies inside the required scalar cell. -/
theorem offSlicePointCountQ_bounds (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < offSlicePointCountQ m D r ∧
      offSlicePointCountQ m D r < N (m + 2) (D - 2) ∧
      (N (m + 2) (D - 2) : ℚ) - N m (D - 2) < offSlicePointCountQ m D r := by
  have hg := residualDimension_bounds m D r hD hm hr
  have hden : (1 : ℚ) ≤ ((D - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ D - 1 by omega)
  have hdiv : (N m (D - 2) : ℚ) / (D - 1 : ℕ) ≤ N m (D - 2) :=
    div_le_self (by positivity) hden
  have hmono : (N m (D - 2) : ℚ) ≤ N (m + 2) (D - 2) := by
    exact_mod_cast N_mono_variables (D - 2) (show m ≤ m + 2 by omega)
  rw [offSlicePointCountQ_eq]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The second residual interpolation count lies in its initial-degree cell. -/
theorem residual_initialDegreeCell (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    (N m (D - 3) : ℚ) < (N m (D - 2) : ℚ) - residualDimension m D r ∧
      (N m (D - 2) : ℚ) - residualDimension m D r < N m (D - 2) := by
  have hbounds := dimension_lower_bounds m D hD hm
  have hwidth := E_le_cell_width m (D - 2) (by omega) (by omega)
  unfold E at hwidth
  simp only [show D - 2 - 1 = D - 3 by omega] at hwidth
  have hden : ((D - 2 : ℕ) : ℚ) + 1 = ((D - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show D - 2 + 1 = D - 1 by omega)
  rw [hden] at hwidth
  have hg := residualDimension_bounds m D r hD hm hr
  constructor <;> linarith

/-- The actual natural point counts have the stated rational values when the trace is integral. -/
theorem actualPointCounts_cast (m D r r₂ : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D)
    (htrace : E m D = (r₂ : ℚ)) :
    let p₂ := N m D - r₂
    let p₁ := N (m + 2) D - r - p₂
    let q := p₁ - 2 * sliceCount m D
    let g := N (m + 2) (D - 2) - q
    (p₂ : ℚ) = tracePointCountQ m D ∧
      (p₁ : ℚ) = attachedPointCountQ m D r ∧
      (q : ℚ) = offSlicePointCountQ m D r ∧
      (g : ℚ) = residualDimension m D r := by
  let p₂ := N m D - r₂
  let p := N (m + 2) D - r
  let p₁ := p - p₂
  let q := p₁ - 2 * sliceCount m D
  let g := N (m + 2) (D - 2) - q
  change (p₂ : ℚ) = tracePointCountQ m D ∧
      (p₁ : ℚ) = attachedPointCountQ m D r ∧
      (q : ℚ) = offSlicePointCountQ m D r ∧
      (g : ℚ) = residualDimension m D r
  have hbounds := dimension_lower_bounds m D hD hm
  have hr₂ : r₂ ≤ N m D := by
    have h := (integral_trace_mem_cell (m + 1) D r₂ (by omega) (by omega)
      (by simpa only [Nat.add_sub_cancel] using htrace)).2
    simp only [Nat.add_sub_cancel] at h
    exact h.trans (Nat.sub_le _ _)
  have hrN : r ≤ N (m + 2) D := by
    rcases hr with h | h
    · rw [h]
      exact (lowerCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
    · rw [h]
      exact (upperCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have hp₂ : (p₂ : ℚ) = tracePointCountQ m D := by
    change ((N m D - r₂ : ℕ) : ℚ) = _
    rw [Nat.cast_sub hr₂, ← htrace]
    unfold E tracePointCountQ
    field_simp
    ring
  have hdecomp : (N (m + 2) D : ℚ) =
      (N m D : ℚ) + 2 * N (m + 1) (D - 1) + N (m + 2) (D - 2) := by
    exact_mod_cast (scalar_count_decomposition m D (by omega)).1
  have hdiff : (p : ℚ) - p₂ = attachedPointCountQ m D r := by
    change ((N (m + 2) D - r : ℕ) : ℚ) - ((N m D - r₂ : ℕ) : ℚ) = _
    rw [Nat.cast_sub hrN, Nat.cast_sub hr₂, ← htrace]
    unfold attachedPointCountQ criticalDeviation E
    rw [hdecomp]
    field_simp
    ring
  have hqbounds := offSlicePointCountQ_bounds m D r hD hm hr
  have hqpos := hqbounds.1
  unfold offSlicePointCountQ at hqpos
  have hb₀ : (0 : ℚ) ≤ sliceCount m D := by positivity
  have hpbound : p₂ ≤ p := by
    have h : (p₂ : ℚ) ≤ p := by linarith
    exact_mod_cast h
  have hp₁ : (p₁ : ℚ) = attachedPointCountQ m D r := by
    change ((p - p₂ : ℕ) : ℚ) = _
    rw [Nat.cast_sub hpbound, hdiff]
  have hqbound : 2 * sliceCount m D ≤ p₁ := by
    have h : 2 * (sliceCount m D : ℚ) ≤ p₁ := by rw [hp₁]; linarith
    exact_mod_cast h
  have hq : (q : ℚ) = offSlicePointCountQ m D r := by
    change ((p₁ - 2 * sliceCount m D : ℕ) : ℚ) = _
    simp only [Nat.cast_sub hqbound, Nat.cast_mul, Nat.cast_ofNat, hp₁, offSlicePointCountQ]
  have hgBound : q ≤ N (m + 2) (D - 2) := by
    have h : (q : ℚ) ≤ N (m + 2) (D - 2) := by
      rw [hq]
      exact le_of_lt hqbounds.2.1
    exact_mod_cast h
  have hg : (g : ℚ) = residualDimension m D r := by
    change ((N (m + 2) (D - 2) - q : ℕ) : ℚ) = _
    rw [Nat.cast_sub hgBound, hq, offSlicePointCountQ_eq]
    ring
  exact ⟨hp₂, hp₁, hq, hg⟩

end IdealGeneration.TwoNormalIntegral
