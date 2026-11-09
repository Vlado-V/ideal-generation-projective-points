module

public import IdealGeneration.TwoNormalFractionalBudgets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Fractional count data used by the marked configuration -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
set_option maxHeartbeats 1200000

abbrev attachedOffCount (m D r : ℕ) := offSlicePointCount m D r - 1
abbrev extraTraceCount (m D r : ℕ) := tracePointCount m D - (attachedPointCount m D r - 1)

/-- The point counts and rank budgets for the two critical constructions. -/
structure FractionalCountFacts (m D r : ℕ) : Prop where
  traceSum : sliceCount m D + (sliceCount m D +
    (attachedOffCount m D r + extraTraceCount m D r)) = tracePointCount m D
  offSum : attachedOffCount m D r + 1 = offSlicePointCount m D r
  ambientSum : sliceCount m D + (sliceCount m D +
    (tracePointCount m D + offSlicePointCount m D r)) = ambientPointCount m D r
  sliceLower : N (m + 1) (D - 2) ≤ sliceCount m D
  sliceUpper : sliceCount m D ≤ N (m + 1) (D - 1)
  sliceTraceUpper : sliceCount m D ≤ N m (D - 1)
  sliceCritical : ((N (m + 1) (D - 1) - sliceCount m D : ℕ) : ℚ) ≤ E (m + 1) (D - 1)
  residualUpper : residualCount m D r + 1 ≤ N m (D - 2)
  residualCritical : ((residualCount m D r + 1 : ℕ) : ℚ) ≤ E m (D - 2)
  fullResidualSum : offSlicePointCount m D r + residualCount m D r = N (m + 2) (D - 2)
  attachedResidualSum : attachedOffCount m D r + (residualCount m D r + 1) =
    N (m + 2) (D - 2)
  pureBudget : (m + 1) * (residualCount m D r + 1) ≤ sliceCount m D
  codeBudget : m * (N (m + 1) (D - 1) - sliceCount m D) ≤ tracePointCount m D
  pairBudget : 2 * sliceCount m D ≤ m * residualCount m D r +
    (N (m + 2) (D - 1) - offSlicePointCount m D r)

/-- The count bounds of Section 5 supply every marked interpolation budget. -/
theorem fractionalCountFacts (m D r : ℕ) (hD : 4 ≤ D)
    (hm₀ : D * (D - 1) ≤ m) (hf : ¬ ∃ r : ℕ, E m D = (r : ℚ))
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    FractionalCountFacts m D r := by
  have hm := fractional_dimension_strict m D hD hm₀ hf
  obtain ⟨hR, hM, hgap, _, hg, hpure, hq, hqC, hp, _⟩ :=
    count_margins m D r hD hm₀ hf hr
  have hbL : sliceCount m D ≤ N (m + 1) (D - 1) :=
    hM.le.trans (TwoNormalIntegral.middle_lt_sliceWidth m D hD).le
  have hslice : ((N (m + 1) (D - 1) - sliceCount m D : ℕ) : ℚ) ≤ E (m + 1) (D - 1) := by
    have hdcast : ((D - 1 : ℕ) : ℚ) + 1 = (D : ℚ) := by
      exact_mod_cast (show D - 1 + 1 = D by omega)
    rw [Nat.cast_sub hbL, E, hdcast]
    exact hgap.le
  have hcrit : ((residualCount m D r + 1 : ℕ) : ℚ) ≤ E m (D - 2) := by
    have hdcast : ((D - 2 : ℕ) : ℚ) + 1 = ((D - 1 : ℕ) : ℚ) := by
      exact_mod_cast (show D - 2 + 1 = D - 1 by omega)
    rw [E, hdcast, Nat.cast_add, Nat.cast_one]
    exact hg.le
  have hgUpper : residualCount m D r + 1 ≤ N m (D - 2) := by
    have hE : E m (D - 2) ≤ N m (D - 2) := by
      unfold E
      apply div_le_self (by positivity)
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact_mod_cast hcrit.trans hE
  have hs := attachedPointCount_decomposition m D r hD hm hr
  have ha := ambientPointCount_decomposition m D r hD hm hr
  have hfull : offSlicePointCount m D r + residualCount m D r = N (m + 2) (D - 2) := by
    change offSlicePointCount m D r < N (m + 2) (D - 2) at hqC
    change offSlicePointCount m D r + (N (m + 2) (D - 2) - offSlicePointCount m D r) = _
    omega
  obtain ⟨hcode, hpair⟩ := fractional_marked_budgets m D r hD hm hr
  refine ⟨?_, ?_, by omega, hR, hbL, hM.le, hslice, hgUpper, hcrit,
    hfull, ?_, hpure.le, hcode, hpair⟩
  · unfold attachedOffCount extraTraceCount
    omega
  · unfold attachedOffCount
    omega
  · unfold attachedOffCount
    omega

end IdealGeneration.TwoNormalFractional
