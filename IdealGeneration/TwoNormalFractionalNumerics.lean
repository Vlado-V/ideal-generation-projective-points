module

public import IdealGeneration.TwoNormalMargins
public import IdealGeneration.InductionNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Numerical parameters for the fractional two-normal transfer

The signed formulas are proved over the rationals before comparing with
natural point counts. This keeps every use of natural subtraction explicit.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional

set_option maxHeartbeats 1500000

open TwoNormalIntegral (cross_degree_counts scalar_count_decomposition criticalDeviation
  criticalDeviation_bounds)

private abbrev F (m D : ℕ) := N m D
private abbrev M (m D : ℕ) := N m (D - 1)
private abbrev L (m D : ℕ) := N (m + 1) (D - 1)
private abbrev C (m D : ℕ) := N (m + 2) (D - 2)
private abbrev R (m D : ℕ) := N (m + 1) (D - 2)
private abbrev Me (m D : ℕ) := N m (D - 2)

/-- The deviation of the upper trace critical count. -/
def traceDeviation (m D : ℕ) : ℚ := (upperCritical m D : ℚ) - E m D

/-- The unrounded number of slice points before allowing for trace deviation. -/
def sliceBaseline (m D : ℕ) : ℚ := (D : ℚ) * L m D / (D + 1)

/-- The paper's `b`, with the extra point on each slice. -/
def sliceCount (m D : ℕ) : ℕ := ⌈sliceBaseline m D + traceDeviation m D / m⌉₊ + 1

/-- The paper's `θ`. -/
def sliceRounding (m D : ℕ) : ℚ := (sliceCount m D : ℚ) - sliceBaseline m D

/-- The paper's `a`, the dimension of either slice cokernel. -/
def sliceCokernel (m D : ℕ) : ℚ := (m : ℚ) * sliceRounding m D - traceDeviation m D

/-- The dimension `κ` of the trace Euler kernel. -/
def traceKernel (m D : ℕ) : ℚ := ((m : ℚ) - 1) * traceDeviation m D

/-- The signed ambient Euler dimension difference `σ`. -/
def ambientDiscrepancy (m D r : ℕ) : ℚ := ((m : ℚ) + 1) * criticalDeviation m D r

/-- The degree-`D−2` residual ideal dimension `g`. -/
def residualDimension (m D r : ℕ) : ℚ :=
  (C m D : ℚ) / (D + 1) - traceDeviation m D + criticalDeviation m D r +
    2 * sliceRounding m D

/-- The rational trace count. -/
def tracePointCountQ (m D : ℕ) : ℚ :=
  TwoNormalIntegral.tracePointCountQ m D - traceDeviation m D

/-- The rational attached count before removing the two slice groups. -/
def attachedPointCountQ (m D r : ℕ) : ℚ :=
  TwoNormalIntegral.attachedPointCountQ m D r + traceDeviation m D

/-- The rational number of points off both slices. -/
def offSlicePointCountQ (m D r : ℕ) : ℚ := attachedPointCountQ m D r - 2 * sliceCount m D

/-- The normal kernel dimension before allowing trace extensions. -/
def normalKernelDimension (m D r : ℕ) : ℚ :=
  (L m D : ℚ) + ((m : ℚ) + 1) * residualDimension m D r - 2 * sliceCount m D

/-- The upper-critical trace discrepancy lies in the unit interval. -/
theorem traceDeviation_bounds (m D : ℕ) :
    0 ≤ traceDeviation m D ∧ traceDeviation m D < 1 := by
  have h₀ := Nat.le_ceil (E m D)
  have h₁ := Nat.ceil_lt_add_one (show 0 ≤ E m D by unfold E; positivity)
  unfold traceDeviation upperCritical
  constructor <;> linarith

/-- For a fractional trace the discrepancy is strictly positive. -/
theorem traceDeviation_pos (m D : ℕ) (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ)) :
    0 < traceDeviation m D := by
  refine lt_of_le_of_ne (traceDeviation_bounds m D).1 ?_
  intro he
  apply hf
  exact ⟨upperCritical m D, by unfold traceDeviation at he; linarith⟩

/-- The lower endpoint is integral, so a fractional trace lies strictly above it. -/
theorem fractional_dimension_strict (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m) (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ)) :
    D * (D - 1) < m := by
  refine lt_of_le_of_ne hm ?_
  intro he
  subst m
  exact hf (induction_endpoint_trace_integral D (by omega))

/-- Size consequences of the strict fractional threshold. -/
theorem fractional_dimension_bounds (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) : 13 ≤ m ∧ 2 * (D + 1) ≤ m := by
  have hmul := Nat.mul_le_mul_left D (show 3 ≤ D - 1 by omega)
  have h : D * 3 < m := hmul.trans_lt hm
  omega

/-- The two-sided estimate on `θ` in (5.2). -/
theorem sliceRounding_bounds (m D : ℕ) :
    1 + traceDeviation m D / m ≤ sliceRounding m D ∧
    sliceRounding m D < 2 + traceDeviation m D / m := by
  let x := sliceBaseline m D + traceDeviation m D / m
  have hx : 0 ≤ x := by
    dsimp [x]
    exact add_nonneg (by unfold sliceBaseline; positivity)
      (div_nonneg (traceDeviation_bounds m D).1 (by positivity))
  have h₀ := Nat.le_ceil x
  have h₁ := Nat.ceil_lt_add_one hx
  unfold sliceRounding sliceCount
  change 1 + traceDeviation m D / m ≤ ((⌈x⌉₊ + 1 : ℕ) : ℚ) - sliceBaseline m D ∧
    ((⌈x⌉₊ + 1 : ℕ) : ℚ) - sliceBaseline m D < 2 + traceDeviation m D / m
  push_cast
  dsimp [x] at h₀ h₁
  constructor <;> linarith

/-- The slice cokernel is at least `m` and strictly below `2m`. -/
theorem sliceCokernel_bounds (m D : ℕ) (hm : 1 ≤ m) :
    (m : ℚ) ≤ sliceCokernel m D ∧ sliceCokernel m D < 2 * (m : ℚ) := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hθ := sliceRounding_bounds m D
  have hl := mul_le_mul_of_nonneg_left hθ.1 hmQ.le
  have hu := mul_lt_mul_of_pos_left hθ.2 hmQ
  simp only [mul_add, mul_one, mul_div_cancel₀ _ hmQ.ne'] at hl hu
  unfold sliceCokernel
  constructor <;> linarith

/-- The scalar trace count and the unfilled slice dimensions differ by `a`. -/
theorem slice_cokernel_identity (m D : ℕ) (hm : 1 ≤ m) (hD : 2 ≤ D) :
    tracePointCountQ m D - (m : ℚ) * ((L m D : ℚ) - sliceCount m D) =
      sliceCokernel m D := by
  have hc : (D : ℚ) * F m D = (m : ℚ) * L m D := by
    exact_mod_cast (cross_degree_counts m D hm hD).1
  unfold tracePointCountQ TwoNormalIntegral.tracePointCountQ sliceCokernel
    sliceRounding sliceBaseline
  field_simp
  nlinarith

/-- The residual points and residual ideal dimensions sum to the scalar dimension. -/
theorem offSlicePointCountQ_eq (m D r : ℕ) :
    offSlicePointCountQ m D r = (C m D : ℚ) - residualDimension m D r := by
  unfold offSlicePointCountQ attachedPointCountQ TwoNormalIntegral.attachedPointCountQ
    residualDimension sliceRounding sliceBaseline
  field_simp
  ring

/-- The kernel dimension identity (5.3). -/
theorem normal_kernel_identity (m D r : ℕ) (hm : 1 ≤ m) (hD : 2 ≤ D) :
    normalKernelDimension m D r = 2 * sliceCokernel m D +
      ambientDiscrepancy m D r - traceKernel m D := by
  have hc₀ : ((m : ℚ) + 1) * C m D = ((D - 1 : ℕ) : ℚ) * L m D := by
    exact_mod_cast (cross_degree_counts m D hm hD).2
  have hc : ((m : ℚ) + 1) * C m D = ((D : ℚ) - 1) * L m D := by
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hc₀
  unfold normalKernelDimension residualDimension sliceCokernel ambientDiscrepancy
    traceKernel sliceRounding sliceBaseline
  field_simp
  nlinarith

/-- The extra point on each slice guarantees positivity in (5.3). -/
theorem normalKernelDimension_pos (m D r : ℕ) (hm : 1 ≤ m) (hD : 2 ≤ D)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < normalKernelDimension m D r := by
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hσ := mul_lt_mul_of_pos_left (criticalDeviation_bounds m D r hr).1
    (show (0 : ℚ) < (m : ℚ) + 1 by positivity)
  have hκ := mul_le_mul_of_nonneg_left (traceDeviation_bounds m D).2.le
    (sub_nonneg.mpr hmQ)
  rw [normal_kernel_identity m D r hm hD]
  unfold ambientDiscrepancy traceKernel
  linarith [(sliceCokernel_bounds m D hm).1]

/-- The crude residual interval used for the two preceding-degree tests. -/
theorem residualDimension_rough_bounds (m D r : ℕ) (hm : 2 ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < residualDimension m D r ∧
      residualDimension m D r < (C m D : ℚ) / (D + 1) + 5 := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hδ := traceDeviation_bounds m D
  have hθ := sliceRounding_bounds m D
  have hΔ := criticalDeviation_bounds m D r hr
  have hd : 0 ≤ traceDeviation m D / (m : ℚ) := div_nonneg hδ.1 (by positivity)
  have hhalf : traceDeviation m D / (m : ℚ) ≤ traceDeviation m D / 2 := by
    apply div_le_div_of_nonneg_left hδ.1 (by norm_num) hmQ
  have hC : (0 : ℚ) ≤ (C m D : ℚ) / (D + 1) := by positivity
  unfold residualDimension
  constructor <;> linarith

private theorem twice_quadratic (m : ℕ) (hm : 1 ≤ m) :
    2 * N m 2 = m * (m + 1) := by
  simpa only [N_one_degree, Nat.reduceAdd, Nat.mul_comm] using N_degree_recurrence m 1 hm

private theorem six_cubic (m : ℕ) (hm : 1 ≤ m) :
    6 * N m 3 = m * (m + 1) * (m + 2) := by
  have h := N_degree_recurrence m 2 hm
  have h₂ := twice_quadratic m hm
  norm_num at h
  nlinarith [congrArg (fun a : ℕ => 2 * a) h,
    congrArg (fun a : ℕ => (m + 2) * a) h₂]

private theorem residual_scalar_ratio (m D : ℕ) (hm : 1 ≤ m) (hD : 4 ≤ D) :
    (m : ℚ) * (m + 1) * C m D = (m + D - 2) * (m + D - 1) * Me m D := by
  have h₀ := N_variable_ratio (m + 1) (D - 2) (by omega) (by omega)
  have h₁ := N_variable_ratio (m + 2) (D - 2) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, show m + 1 + (D - 2) - 1 = m + D - 2 by omega] at h₀
  simp only [show m + 2 - 1 = m + 1 by omega,
    show m + 2 + (D - 2) - 1 = m + D - 1 by omega] at h₁
  have hN : m * (m + 1) * C m D = (m + D - 2) * (m + D - 1) * Me m D := by
    calc
      _ = m * ((m + 1) * C m D) := by ring
      _ = m * ((m + D - 1) * N (m + 1) (D - 2)) := by rw [h₁]
      _ = (m + D - 1) * (m * N (m + 1) (D - 2)) := by ring
      _ = (m + D - 1) * ((m + D - 2) * Me m D) := by rw [h₀]
      _ = _ := by ring
  have hQ : (m : ℚ) * (m + 1) * C m D =
      ((m + D - 2 : ℕ) : ℚ) * ((m + D - 1 : ℕ) : ℚ) * Me m D := by
    exact_mod_cast hN
  simpa only [Nat.cast_sub (show 2 ≤ m + D by omega),
    Nat.cast_sub (show 1 ≤ m + D by omega), Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hQ

/-- The binomial gap (5.5) is strictly bigger than six at a fractional trace. -/
theorem residual_binomial_gap (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) :
    6 < (Me m D : ℚ) / (D - 1 : ℕ) - (C m D : ℚ) / (D + 1) := by
  obtain ⟨hm13, _⟩ := fractional_dimension_bounds m D hD hm
  have hmQ : (13 : ℚ) ≤ m := by exact_mod_cast hm13
  have hDQ : (4 : ℚ) ≤ D := by exact_mod_cast hD
  have hden₁ : (0 : ℚ) < (D : ℚ) - 1 := by linarith
  have hden₂ : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  let den : ℚ := ((D : ℚ) - 1) * (D + 1)
  have hden : 0 < den := mul_pos hden₁ hden₂
  have hmarg : (0 : ℚ) ≤ (m : ℚ) - D * (D - 1) := by
    have hq : (D : ℚ) * ((D - 1 : ℕ) : ℚ) ≤ m := by exact_mod_cast hm.le
    rw [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] at hq
    linarith
  let T : ℚ := ((D : ℚ) + 1) * m * (m + 1) -
    ((D : ℚ) - 1) * (m + D - 2) * (m + D - 1)
  have hT : T = den * (3 * (D : ℚ) - 2) +
      2 * ((m : ℚ) - D * (D - 1)) * (m + 2 * D - 1) := by
    dsimp [T, den]
    ring
  have hlarge : 12 * den < T := by
    by_cases he : D = 4
    · subst D
      have hmul := mul_le_mul (show (1 : ℚ) ≤ m - 12 by linarith)
        (show (20 : ℚ) ≤ m + 7 by linarith) (by norm_num : (0 : ℚ) ≤ 20)
        (show (0 : ℚ) ≤ m - 12 by linarith)
      norm_num [den] at hT ⊢
      nlinarith
    · have hD5 : (5 : ℚ) ≤ D := by exact_mod_cast (show 5 ≤ D by omega)
      have hdenprod := mul_lt_mul_of_pos_left (show (12 : ℚ) < 3 * D - 2 by linarith) hden
      have hremain : 0 ≤ 2 * ((m : ℚ) - D * (D - 1)) * (m + 2 * D - 1) := by
        exact mul_nonneg (mul_nonneg (by norm_num) hmarg) (by linarith)
      linarith
  have hMb := N_mono_degree m (by omega) (show 2 ≤ D - 2 by omega)
  have hMe : (m : ℚ) * (m + 1) / 2 ≤ Me m D := by
    have hq : (m : ℚ) * (m + 1) ≤ 2 * Me m D := by
      exact_mod_cast (show m * (m + 1) ≤ 2 * Me m D by
        rw [← twice_quadratic m (by omega)]
        exact Nat.mul_le_mul_left 2 hMb)
    linarith
  have hmulpos : (0 : ℚ) < (m : ℚ) * (m + 1) := by positivity
  have hmult : (m : ℚ) * (m + 1) / 2 * (12 * den) < (Me m D : ℚ) * T := by
    exact (mul_lt_mul_of_pos_left hlarge (by positivity)).trans_le
      (mul_le_mul_of_nonneg_right hMe (by linarith [hden]))
  have hclear : (Me m D : ℚ) * T = (m : ℚ) * (m + 1) *
      (((D : ℚ) + 1) * Me m D - ((D : ℚ) - 1) * C m D) := by
    dsimp [T]
    calc
      _ = (m : ℚ) * (m + 1) * ((D : ℚ) + 1) * Me m D -
          ((D : ℚ) - 1) * ((m + D - 2) * (m + D - 1) * Me m D) := by ring
      _ = _ := by rw [← residual_scalar_ratio m D (by omega) hD]; ring
  have hnum : 6 * den < ((D : ℚ) + 1) * Me m D - ((D : ℚ) - 1) * C m D := by
    apply (mul_lt_mul_iff_of_pos_left hmulpos).mp
    rw [← hclear]
    nlinarith [hmult]
  rw [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one]
  have hfrac : (Me m D : ℚ) / ((D : ℚ) - 1) - (C m D : ℚ) / (D + 1) =
      (((D : ℚ) + 1) * Me m D - ((D : ℚ) - 1) * C m D) / den := by
    dsimp [den]
    field_simp
  rw [hfrac]
  exact (lt_div_iff₀ hden).mpr hnum

/-- The residual dimension and its one-point deletion both lie on the injective side. -/
theorem residualDimension_bounds (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    0 < residualDimension m D r ∧ residualDimension m D r + 1 <
      (Me m D : ℚ) / (D - 1 : ℕ) := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have h := residualDimension_rough_bounds m D r (by omega) hr
  have hg := residual_binomial_gap m D hD hm
  exact ⟨h.1, by linarith [h.2]⟩

private theorem sliceWidth_large (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) :
    6 * ((m : ℚ) + 1) * ((D : ℚ) + 1) < L m D := by
  obtain ⟨hm13, hhalf⟩ := fractional_dimension_bounds m D hD hm
  have hmQ : (13 : ℚ) ≤ m := by exact_mod_cast hm13
  have hhalfQ : 2 * ((D : ℚ) + 1) ≤ m := by exact_mod_cast hhalf
  have hc := N_mono_degree (m + 1) (by omega) (show 3 ≤ D - 1 by omega)
  have hL : ((m : ℚ) + 1) * (m + 2) * (m + 3) ≤ 6 * L m D := by
    exact_mod_cast (show (m + 1) * (m + 2) * (m + 3) ≤ 6 * L m D by
      have he := six_cubic (m + 1) (by omega)
      have hl : 6 * N (m + 1) 3 ≤ 6 * L m D := Nat.mul_le_mul_left 6 hc
      nlinarith)
  have hp : 36 * ((D : ℚ) + 1) < ((m : ℚ) + 2) * (m + 3) := by
    have hprod : (0 : ℚ) ≤ (m : ℚ) * (m - 13) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hs := mul_lt_mul_of_pos_left hp (show (0 : ℚ) < (m : ℚ) + 1 by positivity)
  nlinarith [hs, hL]

/-- The two pure-side residual spaces fit strictly inside their evaluation rows. -/
theorem residualDimension_slice_margin (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    ((m : ℚ) + 1) * (residualDimension m D r + 1) < sliceCount m D := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hg := (residualDimension_rough_bounds m D r (by omega) hr).2
  have hDplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hcross₀ : ((m : ℚ) + 1) * C m D = ((D - 1 : ℕ) : ℚ) * L m D := by
    exact_mod_cast (cross_degree_counts m D (by omega) (by omega)).2
  have hcross : ((m : ℚ) + 1) * C m D = ((D : ℚ) - 1) * L m D := by
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hcross₀
  have hmul := mul_lt_mul_of_pos_left
    (show residualDimension m D r + 1 < (C m D : ℚ) / (D + 1) + 6 by linarith)
    (show (0 : ℚ) < ((m : ℚ) + 1) * (D + 1) by positivity)
  have hcancel : ((m : ℚ) + 1) * (D + 1) * ((C m D : ℚ) / (D + 1) + 6) =
      ((m : ℚ) + 1) * C m D + 6 * ((m : ℚ) + 1) * (D + 1) := by
    field_simp
  rw [hcancel] at hmul
  have hb : sliceBaseline m D ≤ sliceCount m D := by
    have hd : (0 : ℚ) ≤ traceDeviation m D / m :=
      div_nonneg (traceDeviation_bounds m D).1 (by positivity)
    have h := (sliceRounding_bounds m D).1
    unfold sliceRounding at h
    linarith
  unfold sliceBaseline at hb
  have hb₁ := (div_le_iff₀ hDplus).mp hb
  apply (mul_lt_mul_iff_of_pos_left hDplus).mp
  nlinarith [hmul, hb₁, hcross, sliceWidth_large m D hD hm]

private theorem sliceBaseline_le_count (m D : ℕ) : sliceBaseline m D ≤ sliceCount m D := by
  have h := (sliceRounding_bounds m D).1
  have hd := div_nonneg (traceDeviation_bounds m D).1 (show (0 : ℚ) ≤ m by positivity)
  unfold sliceRounding at h
  linarith

private theorem middle_minus_baseline_gt_four (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) :
    4 < (M m D : ℚ) - sliceBaseline m D := by
  obtain ⟨hm13, hhalf⟩ := fractional_dimension_bounds m D hD hm
  have hmQ : (13 : ℚ) ≤ m := by exact_mod_cast hm13
  have hmpos : (0 : ℚ) < m := by positivity
  have hhalfQ : 2 * ((D : ℚ) + 1) ≤ m := by exact_mod_cast hhalf
  have hDplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hMmono := N_mono_degree m (by omega) (show 3 ≤ D - 1 by omega)
  have hMbound : (m : ℚ) * (m + 1) * (m + 2) ≤ 6 * M m D := by
    exact_mod_cast (show m * (m + 1) * (m + 2) ≤ 6 * M m D by
      rw [← six_cubic m (by omega)]
      exact Nat.mul_le_mul_left 6 hMmono)
  have hprod : 24 * ((D : ℚ) + 1) < ((m : ℚ) + 1) * (m + 2) := by
    have hpos : (0 : ℚ) ≤ (m : ℚ) * (m - 9) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hMlarge : 4 * (m : ℚ) * (D + 1) < M m D := by
    have hh := mul_lt_mul_of_pos_left hprod hmpos
    nlinarith [hMbound, hh]
  have hN := N_variable_ratio (m + 1) (D - 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, show m + 1 + (D - 1) - 1 = m + D - 1 by omega] at hN
  have hQ : (m : ℚ) * L m D = ((m + D - 1 : ℕ) : ℚ) * M m D := by exact_mod_cast hN
  have hratio : (m : ℚ) * L m D = (m + D - 1) * M m D := by
    simpa only [Nat.cast_sub (show 1 ≤ m + D by omega), Nat.cast_add, Nat.cast_one] using hQ
  have hmarg : (1 : ℚ) ≤ (m : ℚ) - D * (D - 1) := by
    have hq : (D : ℚ) * ((D - 1 : ℕ) : ℚ) + 1 ≤ m := by
      exact_mod_cast Nat.succ_le_of_lt hm
    rw [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] at hq
    linarith
  have hid : ((M m D : ℚ) - sliceBaseline m D) * ((m : ℚ) * (D + 1)) =
      (M m D : ℚ) * (m - D * (D - 1)) := by
    unfold sliceBaseline
    field_simp
    nlinarith [congrArg (fun x : ℚ => (D : ℚ) * x) hratio]
  have hmul := mul_le_mul_of_nonneg_left hmarg (show (0 : ℚ) ≤ M m D by positivity)
  apply (mul_lt_mul_iff_of_pos_right (mul_pos hmpos hDplus)).mp
  rw [hid]
  nlinarith [hMlarge, hmul]

/-- The fractional slice count satisfies the first two margins in (5.4). -/
theorem sliceCount_margins (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) :
    R m D ≤ sliceCount m D ∧ sliceCount m D < M m D ∧
    (L m D : ℚ) - sliceCount m D < (L m D : ℚ) / D := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hcomp : TwoNormalIntegral.sliceCount m D ≤ sliceCount m D := by
    apply Nat.ceil_le.mpr
    exact sliceBaseline_le_count m D
  have hcompQ : (TwoNormalIntegral.sliceCount m D : ℚ) ≤ sliceCount m D := by exact_mod_cast hcomp
  refine ⟨(TwoNormalIntegral.lower_le_sliceCount m D hD hm.le).trans hcomp, ?_, ?_⟩
  · have hδ := traceDeviation_bounds m D
    have hθ := (sliceRounding_bounds m D).2
    have hdiv := div_le_self hδ.1 hmQ
    have hbase := middle_minus_baseline_gt_four m D hD hm
    unfold sliceRounding at hθ
    exact_mod_cast (show (sliceCount m D : ℚ) < M m D by linarith)
  · have h := TwoNormalIntegral.sliceCount_gap_lt m D hD
    linarith

/-- There are at least two off-slice points, and fewer than the scalar dimension. -/
theorem offSlicePointCountQ_bounds (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    1 < offSlicePointCountQ m D r ∧ offSlicePointCountQ m D r < C m D := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hN := N_mono_degree (m + 2) (by omega) (show 1 ≤ D - 2 by omega)
  rw [N_one_degree] at hN
  have hC : (15 : ℚ) ≤ C m D := by
    exact_mod_cast (show 15 ≤ C m D by exact (show 15 ≤ m + 2 by omega).trans hN)
  have hDq : (5 : ℚ) ≤ (D : ℚ) + 1 := by exact_mod_cast (show 5 ≤ D + 1 by omega)
  have hdiv : (C m D : ℚ) / (D + 1) ≤ (C m D : ℚ) / 5 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hDq
  have h := residualDimension_rough_bounds m D r (by omega) hr
  rw [offSlicePointCountQ_eq]
  constructor <;> linarith [h.1, h.2]

/-- The trace count allows scalar interpolation in degree `D−1`. -/
theorem middle_le_tracePointCountQ (m D : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m) :
    (M m D : ℚ) ≤ tracePointCountQ m D := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hstrong := TwoNormalIntegral.degree_times_middle_le_tracePointCountQ m D hD hm.le
  have hM : (1 : ℚ) ≤ M m D := by
    exact_mod_cast (N_pos (n := m) (d := D - 1) (by omega))
  have hDq : (2 : ℚ) ≤ ((D - 1 : ℕ) : ℚ) := by exact_mod_cast (show 2 ≤ D - 1 by omega)
  have hprod := mul_le_mul_of_nonneg_right hDq (show (0 : ℚ) ≤ M m D by positivity)
  unfold tracePointCountQ
  linarith [(traceDeviation_bounds m D).2]

/-- In fact the trace count is larger than the attached count even before discarding a projection. -/
theorem attachedPointCountQ_lt_tracePointCountQ (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    attachedPointCountQ m D r < tracePointCountQ m D := by
  obtain ⟨hm13, hhalf⟩ := fractional_dimension_bounds m D hD hm
  have hmQ : (13 : ℚ) ≤ m := by exact_mod_cast hm13
  have hdplus : (0 : ℚ) < (D : ℚ) + 1 := by positivity
  have hLpos : (0 : ℚ) < L m D := by exact_mod_cast N_pos (n := m + 1) (d := D - 1) (by omega)
  have hDF : (D : ℚ) * F m D = (m : ℚ) * L m D := by
    exact_mod_cast (cross_degree_counts m D (by omega) (by omega)).1
  have hcross₀ : ((m : ℚ) + 1) * C m D = ((D - 1 : ℕ) : ℚ) * L m D := by
    exact_mod_cast (cross_degree_counts m D (by omega) (by omega)).2
  have hcross : ((m : ℚ) + 1) * C m D = ((D : ℚ) - 1) * L m D := by
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hcross₀
  have hmargin : (D : ℚ) * (D - 1) < (m : ℚ) + 1 := by
    have hq : (D : ℚ) * ((D - 1 : ℕ) : ℚ) < (m : ℚ) + 1 := by
      exact_mod_cast (show D * (D - 1) < m + 1 by omega)
    simpa only [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] using hq
  have hDC : (D : ℚ) * C m D < L m D := by
    apply (mul_lt_mul_iff_of_pos_left (show (0 : ℚ) < (m : ℚ) + 1 by positivity)).mp
    have hs := congrArg (fun x : ℚ => (D : ℚ) * x) hcross
    have hm := mul_lt_mul_of_pos_right hmargin hLpos
    nlinarith [hs, hm]
  have hhalfQ : 2 * ((D : ℚ) + 1) ≤ m := by exact_mod_cast hhalf
  have hmprod := mul_le_mul_of_nonneg_right hhalfQ hLpos.le
  have hnum : (L m D : ℚ) < (m : ℚ) * L m D - (D : ℚ) * (2 * L m D + C m D) := by
    nlinarith [hmprod, hDC]
  have hL : 3 * ((D : ℚ) + 1) < L m D := by
    have hm₀ := mul_le_mul_of_nonneg_right (show (3 : ℚ) ≤ 6 * ((m : ℚ) + 1) by linarith) hdplus.le
    exact hm₀.trans_lt (sliceWidth_large m D hD hm)
  have hdiv : (3 : ℚ) < ((m : ℚ) * L m D - (D : ℚ) * (2 * L m D + C m D)) / (D + 1) :=
    (lt_div_iff₀ hdplus).mpr (hL.trans hnum)
  have hid : tracePointCountQ m D - attachedPointCountQ m D r =
      ((m : ℚ) * L m D - (D : ℚ) * (2 * L m D + C m D)) / (D + 1) +
      criticalDeviation m D r - 2 * traceDeviation m D := by
    unfold tracePointCountQ attachedPointCountQ TwoNormalIntegral.tracePointCountQ
      TwoNormalIntegral.attachedPointCountQ
    rw [hDF]
    ring
  have hpos : 0 < tracePointCountQ m D - attachedPointCountQ m D r := by
    rw [hid]
    linarith [(criticalDeviation_bounds m D r hr).1, (traceDeviation_bounds m D).2]
  linarith

/-- The ordered trace uses the upper critical count. -/
def tracePointCount (m D : ℕ) : ℕ := F m D - upperCritical m D

/-- The total ambient point count. -/
def ambientPointCount (m D r : ℕ) : ℕ := N (m + 2) D - r

/-- The number of points away from the trace. -/
def attachedPointCount (m D r : ℕ) : ℕ := ambientPointCount m D r - tracePointCount m D

/-- The number of points off both slices. -/
def offSlicePointCount (m D r : ℕ) : ℕ := attachedPointCount m D r - 2 * sliceCount m D

/-- The degree-`D−2` ideal dimension after imposing the off-slice conditions. -/
def residualCount (m D r : ℕ) : ℕ := C m D - offSlicePointCount m D r

/-- At a fractional trace the two critical integers differ by one. -/
theorem trace_critical_difference (m D : ℕ) (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ)) :
    upperCritical m D = lowerCritical m D + 1 := by
  have hle : lowerCritical m D ≤ upperCritical m D := Nat.floor_le_ceil _
  have hgap := upperCritical_le_lowerCritical_add_one m D
  have hne : upperCritical m D ≠ lowerCritical m D := by
    intro he
    have hδ := traceDeviation_pos m D hf
    have hfloor : (lowerCritical m D : ℚ) ≤ E m D :=
      Nat.floor_le (by unfold E; positivity)
    unfold traceDeviation at hδ
    rw [he] at hδ
    linarith
  omega

/-- All the natural counts in (5.2) agree with their signed rational formulas. -/
theorem actualPointCounts_cast (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    (tracePointCount m D : ℚ) = tracePointCountQ m D ∧
    (attachedPointCount m D r : ℚ) = attachedPointCountQ m D r ∧
    (offSlicePointCount m D r : ℚ) = offSlicePointCountQ m D r ∧
    (residualCount m D r : ℚ) = residualDimension m D r := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hr₂ : upperCritical m D ≤ F m D :=
    (upperCritical_mem_cell m D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have hrN : r ≤ N (m + 2) D := by
    rcases hr with h | h
    · rw [h]
      exact (lowerCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
    · rw [h]
      exact (upperCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have hp₂ : (tracePointCount m D : ℚ) = tracePointCountQ m D := by
    unfold tracePointCount tracePointCountQ TwoNormalIntegral.tracePointCountQ traceDeviation E
    rw [Nat.cast_sub hr₂]
    field_simp
    ring
  have hdecomp : (N (m + 2) D : ℚ) = (F m D : ℚ) + 2 * L m D + C m D := by
    exact_mod_cast (scalar_count_decomposition m D (by omega)).1
  have hdiff : (ambientPointCount m D r : ℚ) - tracePointCount m D = attachedPointCountQ m D r := by
    unfold ambientPointCount tracePointCount attachedPointCountQ
      TwoNormalIntegral.attachedPointCountQ criticalDeviation traceDeviation E
    rw [Nat.cast_sub hrN, Nat.cast_sub hr₂, hdecomp]
    field_simp
    ring
  have hqb := offSlicePointCountQ_bounds m D r hD hm hr
  have hqpos := hqb.1
  unfold offSlicePointCountQ at hqpos
  have hbn : (0 : ℚ) ≤ sliceCount m D := by positivity
  have hcounts : tracePointCount m D ≤ ambientPointCount m D r := by
    exact_mod_cast (show (tracePointCount m D : ℚ) ≤ ambientPointCount m D r by linarith)
  have hp₁ : (attachedPointCount m D r : ℚ) = attachedPointCountQ m D r := by
    unfold attachedPointCount
    rw [Nat.cast_sub hcounts, hdiff]
  have hslice : 2 * sliceCount m D ≤ attachedPointCount m D r := by
    exact_mod_cast (show 2 * (sliceCount m D : ℚ) ≤ attachedPointCount m D r by rw [hp₁]; linarith)
  have hq : (offSlicePointCount m D r : ℚ) = offSlicePointCountQ m D r := by
    unfold offSlicePointCount offSlicePointCountQ
    simp only [Nat.cast_sub hslice, Nat.cast_mul, Nat.cast_ofNat, hp₁]
  have hqle : offSlicePointCount m D r ≤ C m D := by
    exact_mod_cast (show (offSlicePointCount m D r : ℚ) ≤ C m D by rw [hq]; exact hqb.2.le)
  have hg : (residualCount m D r : ℚ) = residualDimension m D r := by
    unfold residualCount
    rw [Nat.cast_sub hqle, hq, offSlicePointCountQ_eq]
    ring
  exact ⟨hp₂, hp₁, hq, hg⟩

/-- The two sets of slice points and the off-slice points exhaust the attached count. -/
theorem attachedPointCount_decomposition (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    attachedPointCount m D r = 2 * sliceCount m D + offSlicePointCount m D r := by
  have hcast := actualPointCounts_cast m D r hD hm hr
  have hq := hcast.2.2.1
  unfold offSlicePointCountQ at hq
  exact_mod_cast (show (attachedPointCount m D r : ℚ) =
    2 * (sliceCount m D : ℚ) + offSlicePointCount m D r by linarith [hcast.2.1])

/-- The trace, slice, and off-slice points have the ambient critical count. -/
theorem ambientPointCount_decomposition (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    ambientPointCount m D r = tracePointCount m D + 2 * sliceCount m D + offSlicePointCount m D r := by
  have hp := attachedPointCount_decomposition m D r hD hm hr
  have hq := (offSlicePointCountQ_bounds m D r hD hm hr).1
  have hcast := (actualPointCounts_cast m D r hD hm hr).2.2.1
  have hqpos : 0 < offSlicePointCount m D r := by
    exact_mod_cast (show (0 : ℚ) < offSlicePointCount m D r by rw [hcast]; linarith)
  unfold attachedPointCount at hp
  omega

/-- The residual and deleted-residual point counts lie in the degree-`D−2` cell. -/
theorem residual_initialDegreeCell (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    (N m (D - 3) : ℚ) < (Me m D : ℚ) - (residualDimension m D r + 1) ∧
    (Me m D : ℚ) - residualDimension m D r < Me m D := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hwidth := E_le_cell_width m (D - 2) (by omega) (by omega)
  unfold E at hwidth
  simp only [show D - 2 - 1 = D - 3 by omega] at hwidth
  have heq : ((D - 2 : ℕ) : ℚ) + 1 = ((D - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show D - 2 + 1 = D - 1 by omega)
  rw [heq] at hwidth
  have hg := residualDimension_bounds m D r hD hm hr
  constructor <;> linarith [hg.1, hg.2]

/-- The full collection of point-count bounds (5.4) in the natural count model. -/
theorem count_margins (m D r : ℕ) (hD : 4 ≤ D)
    (hm₀ : D * (D - 1) ≤ m) (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ))
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    R m D ≤ sliceCount m D ∧ sliceCount m D < M m D ∧
    (L m D : ℚ) - sliceCount m D < (L m D : ℚ) / D ∧
    0 < residualCount m D r ∧ (residualCount m D r : ℚ) + 1 < (Me m D : ℚ) / (D - 1 : ℕ) ∧
    (m + 1) * (residualCount m D r + 1) < sliceCount m D ∧
    1 < offSlicePointCount m D r ∧ offSlicePointCount m D r < C m D ∧
    attachedPointCount m D r - 1 ≤ tracePointCount m D ∧ M m D ≤ tracePointCount m D := by
  have hm := fractional_dimension_strict m D hD hm₀ hf
  obtain ⟨hp₂, hp₁, hq, hg⟩ := actualPointCounts_cast m D r hD hm hr
  obtain ⟨hb₁, hb₂, hb₃⟩ := sliceCount_margins m D hD hm
  obtain ⟨hg₁, hg₂⟩ := residualDimension_bounds m D r hD hm hr
  obtain ⟨hq₁, hq₂⟩ := offSlicePointCountQ_bounds m D r hD hm hr
  refine ⟨hb₁, hb₂, hb₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℚ) < residualCount m D r by rwa [hg])
  · rwa [hg]
  · exact_mod_cast (show ((m : ℚ) + 1) * ((residualCount m D r : ℚ) + 1) < sliceCount m D by
      rw [hg]
      exact residualDimension_slice_margin m D r hD hm hr)
  · exact_mod_cast (show (1 : ℚ) < offSlicePointCount m D r by rwa [hq])
  · exact_mod_cast (show (offSlicePointCount m D r : ℚ) < C m D by rwa [hq])
  · have h : attachedPointCount m D r < tracePointCount m D := by
      exact_mod_cast (show (attachedPointCount m D r : ℚ) < tracePointCount m D by
        rw [hp₁, hp₂]
        exact attachedPointCountQ_lt_tracePointCountQ m D r hD hm hr)
    omega
  · exact_mod_cast (show (M m D : ℚ) ≤ tracePointCount m D by
      rw [hp₂]
      exact middle_le_tracePointCountQ m D hD hm)

/-- Adjoining the free projected point gives the lower critical trace count. -/
theorem tracePointCount_add_one (m D : ℕ) (hm : 2 ≤ m) (hD : 1 ≤ D)
    (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ)) :
    tracePointCount m D + 1 = F m D - lowerCritical m D := by
  have hdiff := trace_critical_difference m D hf
  have hu : upperCritical m D ≤ F m D :=
    (upperCritical_mem_cell m D hm hD).2.trans (Nat.sub_le _ _)
  unfold tracePointCount
  omega

/-- The trace and the trace with the free projection both belong to the scalar cell. -/
theorem trace_initialDegreeCells (m D : ℕ) (hm : 2 ≤ m) (hD : 1 ≤ D)
    (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ)) :
    M m D ≤ tracePointCount m D ∧ tracePointCount m D + 1 < F m D := by
  have hupper := upperCritical_mem_cell m D hm hD
  have hlower := lowerCritical_mem_cell m D hm hD
  constructor
  · unfold tracePointCount F M
    omega
  · rw [tracePointCount_add_one m D hm hD hf]
    have hpos : 0 < F m D := N_pos (by omega)
    omega

/-- The Euler source minus target dimension at the chosen trace count is `κ`. -/
theorem trace_kernel_from_counts (m D : ℕ) (hm : 2 ≤ m) (hD : 1 ≤ D) :
    (m : ℚ) * F m D - N m (D + 1) - ((m : ℚ) - 1) * tracePointCount m D =
      traceKernel m D := by
  have hu : upperCritical m D ≤ F m D :=
    (upperCritical_mem_cell m D hm hD).2.trans (Nat.sub_le _ _)
  have h := multiplication_dimension_difference_points m D (tracePointCount m D) (by omega)
  unfold tracePointCount at h ⊢
  rw [Nat.cast_sub hu] at h ⊢
  unfold traceKernel traceDeviation
  nlinarith

/-- The Euler source minus target dimension at the ambient count is `σ`. -/
theorem ambient_discrepancy_from_counts (m D r : ℕ) (hr : r ≤ N (m + 2) D) :
    ((m : ℚ) + 2) * N (m + 2) D - N (m + 2) (D + 1) -
      ((m : ℚ) + 1) * ambientPointCount m D r = ambientDiscrepancy m D r := by
  have h := multiplication_dimension_difference_points (m + 2) D (ambientPointCount m D r) (by omega)
  unfold ambientPointCount at h ⊢
  simp only [Nat.cast_sub hr, Nat.cast_add, Nat.cast_ofNat] at h ⊢
  unfold ambientDiscrepancy criticalDeviation
  nlinarith

/-- Both the slice cokernel and the pure normal kernel admit their natural counts. -/
theorem kernelCounts_cast (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    ((tracePointCount m D - m * (L m D - sliceCount m D) : ℕ) : ℚ) = sliceCokernel m D ∧
    ((L m D + (m + 1) * residualCount m D r - 2 * sliceCount m D : ℕ) : ℚ) =
      normalKernelDimension m D r := by
  have hm13 := (fractional_dimension_bounds m D hD hm).1
  have hm₁ : 1 ≤ m := by omega
  have hcasts := actualPointCounts_cast m D r hD hm hr
  have hbL : sliceCount m D ≤ L m D :=
    (sliceCount_margins m D hD hm).2.1.le.trans (TwoNormalIntegral.middle_lt_sliceWidth m D hD).le
  have hslice : (tracePointCount m D : ℚ) - ((m * (L m D - sliceCount m D) : ℕ) : ℚ) =
      sliceCokernel m D := by
    rw [hcasts.1, Nat.cast_mul, Nat.cast_sub hbL]
    exact slice_cokernel_identity m D hm₁ (by omega)
  have hsliceLe : m * (L m D - sliceCount m D) ≤ tracePointCount m D := by
    exact_mod_cast (show ((m * (L m D - sliceCount m D) : ℕ) : ℚ) ≤ tracePointCount m D by
      have h := (sliceCokernel_bounds m D hm₁).1
      have hmQ : (0 : ℚ) ≤ m := by positivity
      linarith)
  have hnormal : ((L m D + (m + 1) * residualCount m D r : ℕ) : ℚ) -
      ((2 * sliceCount m D : ℕ) : ℚ) = normalKernelDimension m D r := by
    push_cast
    rw [hcasts.2.2.2]
    rfl
  have hnormalLe : 2 * sliceCount m D ≤ L m D + (m + 1) * residualCount m D r := by
    exact_mod_cast (show ((2 * sliceCount m D : ℕ) : ℚ) ≤
      ((L m D + (m + 1) * residualCount m D r : ℕ) : ℚ) by
      linarith [normalKernelDimension_pos m D r hm₁ (by omega) hr])
  exact ⟨by rw [Nat.cast_sub hsliceLe, hslice], by rw [Nat.cast_sub hnormalLe, hnormal]⟩

/-- Deleting the distinguished off-slice point increases the ideal dimension by one. -/
theorem residualCount_of_deleted_point (m D r : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) < m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    C m D - (offSlicePointCount m D r - 1) = residualCount m D r + 1 := by
  have hq := (actualPointCounts_cast m D r hD hm hr).2.2.1
  have hqBounds := offSlicePointCountQ_bounds m D r hD hm hr
  have hqpos : 1 < offSlicePointCount m D r := by
    exact_mod_cast (show (1 : ℚ) < offSlicePointCount m D r by rw [hq]; exact hqBounds.1)
  have hqle : offSlicePointCount m D r ≤ C m D := by
    exact_mod_cast (show (offSlicePointCount m D r : ℚ) ≤ C m D by rw [hq]; exact hqBounds.2.le)
  unfold residualCount
  omega

end IdealGeneration.TwoNormalFractional
