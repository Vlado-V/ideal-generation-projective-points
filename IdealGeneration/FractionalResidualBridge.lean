module

public import IdealGeneration.FractionalHyperplaneCounts
public import IdealGeneration.CriticalOpen
public import IdealGeneration.FourVariableFractional

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Natural residual dimensions, directional opens, and actual off-hyperplane witnesses. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- A directional injection open cannot prescribe more equations than the
whole homogeneous component contains. -/
theorem scalarInjectionAt_count_le {n d r : ℕ}
    (h : ScalarInjectionAt K n d r) : r ≤ N (n + 1) d := by
  obtain ⟨Δ, ⟨a, ha⟩, hgood⟩ := h
  have hdim := (hgood a ha).2.2
  have hbound := Submodule.finrank_le (pointDegreePiece K a d)
  rw [hdim, finrank_chart_forms] at hbound
  simpa only [← N_chart n d] using hbound

/-- The full directional injection open has a scalar-postulated witness
whose points all avoid the fixed hyperplane. -/
theorem scalarInjectionAt_off_witness [CharZero K] (m d r : ℕ)
    (h : ScalarInjectionAt K (m + 1) d r) :
    ∃ a : PointCoordinates K (m + 1) (N (m + 2) d - r),
      (∀ i, a (i, 0) ≠ 0) ∧
      Function.Surjective (pointEvaluation K a d) ∧
      Function.Injective (pointMultiplication a d) ∧
      finrank K (pointDegreePiece K a d) = r := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  obtain ⟨a, ha, hoff⟩ := principal_open_meets_off_hyperplane Δ hΔ
  exact ⟨a, hoff, hgood a ha⟩

/-- A single largest residual injection supplies off-hyperplane witnesses
for every smaller residual dimension. -/
theorem scalarInjectionAt_off_witness_of_le [CharZero K] (m d r s : ℕ)
    (hrs : r ≤ s) (h : ScalarInjectionAt K (m + 1) d s) :
    ∃ a : PointCoordinates K (m + 1) (N (m + 2) d - r),
      (∀ i, a (i, 0) ≠ 0) ∧
      Function.Surjective (pointEvaluation K a d) ∧
      Function.Injective (pointMultiplication a d) ∧
      finrank K (pointDegreePiece K a d) = r := by
  have hsmall := scalarInjectionAt_mono (by omega : 1 ≤ m + 1) hrs
    (scalarInjectionAt_count_le h) h
  exact scalarInjectionAt_off_witness m d r hsmall

/-- A preceding-degree maximal-rank assertion on the injective side gives
the largest natural residual injection used by the fractional transfer. -/
theorem fractionalResidualSCount_scalarInjectionAt [CharZero K]
    (n d : ℕ) (hn : 3 ≤ n) (hd : 3 ≤ d)
    (hdef : N (n - 1) (d + 1) ≤ (n - 1) * N (n - 1) (d - 1))
    (hpos : 0 ≤ fractionalResidualS n d)
    (hcritical : fractionalResidualS n d ≤ E n (d - 2))
    (hprevious : IdealGenerationAt K (n - 1) (d - 2)
      (N n (d - 2) - fractionalResidualSCount n d)) :
    ScalarInjectionAt K (n - 1) (d - 2) (fractionalResidualSCount n d) := by
  have hcast := fractionalResidualSCount_cast n d hn hdef hpos
  have hwidth := E_le_cell_width n (d - 2) (by omega) (by omega)
  have hbound : (fractionalResidualSCount n d : ℚ) ≤ N n (d - 2) := by
    rw [hcast]
    have hnonneg : (0 : ℚ) ≤ N n (d - 2 - 1) := by positivity
    linarith
  have hnat : fractionalResidualSCount n d ≤ N n (d - 2) := by exact_mod_cast hbound
  apply scalarInjectionAt_of_idealGenerationAt (by omega) (fractionalResidualSCount n d)
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hnat
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega), hcast] using hcritical
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hprevious

/-- The higher fractional estimates turn the preceding-degree theorem into
the single largest residual injection required by Proposition 3.8. -/
theorem higherFractional_residual_scalarInjectionAt [CharZero K]
    (n d : ℕ) (hn : 5 ≤ n) (hd : 5 ≤ d) (hu : n ≤ d * (d - 1) + 1)
    (hfrac : upperCritical (n - 1) d = lowerCritical (n - 1) d + 1)
    (hprevious : ∀ p, IdealGenerationAt K (n - 1) (d - 2) p) :
    ScalarInjectionAt K (n - 1) (d - 2) (fractionalResidualSCount n d) := by
  obtain ⟨hpos, horder, hcritical, _⟩ := higherFractional_residual_bounds n d hn hd hu hfrac
  exact fractionalResidualSCount_scalarInjectionAt n d (by omega) (by omega)
    (higherFractional_defect_nonnegative n d (by omega) (by omega) hu)
    (le_trans (le_of_lt hpos) horder) (le_of_lt hcritical) (hprevious _)

/-- The four-variable odd-degree estimates supply the same largest residual injection. -/
theorem fourFractional_residual_scalarInjectionAt [CharZero K]
    (k : ℕ) (hk : 3 ≤ k)
    (hprevious : ∀ p, IdealGenerationAt K 3 (2 * k + 1 - 2) p) :
    ScalarInjectionAt K 3 (2 * k + 1 - 2) (fractionalResidualSCount 4 (2 * k + 1)) := by
  obtain ⟨hpos, horder, hcritical, _⟩ := four_fractional_residual_bounds k hk
  exact fractionalResidualSCount_scalarInjectionAt 4 (2 * k + 1) (by decide) (by omega)
    (four_fractional_defect_nonnegative k (by omega))
    (le_trans (by linarith) horder) (le_of_lt hcritical) (hprevious _)

/-- The one largest residual injection provides both actual off-hyperplane
configurations used in the injective and independent fractional constructions. -/
theorem fractionalResidual_off_witnesses [CharZero K]
    (n d : ℕ) (hn : 3 ≤ n)
    (horder : fractionalResidualICount n d ≤ fractionalResidualSCount n d)
    (hres : ScalarInjectionAt K (n - 1) (d - 2) (fractionalResidualSCount n d)) :
    (∃ a : PointCoordinates K (n - 1) (N n (d - 2) - fractionalResidualICount n d),
      (∀ i, a (i, ⟨0, by omega⟩) ≠ 0) ∧ Function.Surjective (pointEvaluation K a (d - 2)) ∧
      Function.Injective (pointMultiplication a (d - 2)) ∧
      finrank K (pointDegreePiece K a (d - 2)) = fractionalResidualICount n d) ∧
    (∃ a : PointCoordinates K (n - 1) (N n (d - 2) - fractionalResidualSCount n d),
      (∀ i, a (i, ⟨0, by omega⟩) ≠ 0) ∧ Function.Surjective (pointEvaluation K a (d - 2)) ∧
      Function.Injective (pointMultiplication a (d - 2)) ∧
      finrank K (pointDegreePiece K a (d - 2)) = fractionalResidualSCount n d) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  subst n
  constructor
  · exact scalarInjectionAt_off_witness_of_le m (d - 2)
      (fractionalResidualICount (m + 2) d) (fractionalResidualSCount (m + 2) d) horder hres
  · exact scalarInjectionAt_off_witness m (d - 2) (fractionalResidualSCount (m + 2) d) hres

end IdealGeneration
