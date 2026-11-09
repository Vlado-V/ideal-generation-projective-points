module

public import IdealGeneration.TwoNormalMargins

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Actual integral marked counts

The rational bounds of (4.1)–(4.9) determine all the natural point counts
and the signed residual kernel dimension used by the marked construction.
-/

namespace IdealGeneration.TwoNormalIntegral
set_option maxHeartbeats 1200000

abbrev integralAmbientCount (m D r : ℕ) := N (m + 2) D - r
abbrev integralTraceCount (m D r₂ : ℕ) := N m D - r₂
abbrev integralAttachedCount (m D r r₂ : ℕ) := integralAmbientCount m D r - integralTraceCount m D r₂
abbrev integralOffCount (m D r r₂ : ℕ) := integralAttachedCount m D r r₂ - 2 * sliceCount m D
abbrev integralResidualDimension (m D r r₂ : ℕ) := N (m + 2) (D - 2) - integralOffCount m D r r₂
abbrev integralExtraTraceCount (m D r r₂ : ℕ) := integralTraceCount m D r₂ - integralAttachedCount m D r r₂
abbrev integralCodeDimension (m D r₂ : ℕ) :=
  integralTraceCount m D r₂ - m * (N (m + 1) (D - 1) - sliceCount m D)

/-- The count bounds and signed identities at either ambient critical count. -/
structure IntegralCountFacts (m D r r₂ : ℕ) : Prop where
  traceSum : sliceCount m D + (sliceCount m D +
      (integralOffCount m D r r₂ + integralExtraTraceCount m D r r₂)) = integralTraceCount m D r₂
  ambientSum : sliceCount m D + (sliceCount m D +
      (integralOffCount m D r r₂ + integralTraceCount m D r₂)) = integralAmbientCount m D r
  traceLower : N m (D - 1) ≤ integralTraceCount m D r₂
  sliceLower : N (m + 1) (D - 2) ≤ sliceCount m D
  sliceUpper : sliceCount m D ≤ N (m + 1) (D - 1)
  sliceTraceUpper : sliceCount m D ≤ N m (D - 1)
  sliceCritical : ((N (m + 1) (D - 1) - sliceCount m D : ℕ) : ℚ) ≤ E (m + 1) (D - 1)
  residualUpper : integralResidualDimension m D r r₂ ≤ N m (D - 2)
  offSum : integralOffCount m D r r₂ + integralResidualDimension m D r r₂ = N (m + 2) (D - 2)
  residualCritical : (integralResidualDimension m D r r₂ : ℚ) ≤ E m (D - 2)
  pureBound : (m + 1) * integralResidualDimension m D r r₂ ≤ sliceCount m D
  codeBudget : m * (N (m + 1) (D - 1) - sliceCount m D) ≤ integralTraceCount m D r₂
  residualSigned :
    ((m * integralResidualDimension m D r r₂ +
        (N (m + 2) (D - 1) - integralOffCount m D r r₂) : ℕ) : ℚ) - 2 * sliceCount m D =
      2 * integralCodeDimension m D r₂ + ((m : ℚ) + 1) * criticalDeviation m D r

/-- The marked counts are valid at both critical choices. -/
theorem integralCountFacts (m D r r₂ : ℕ) (hD : 4 ≤ D)
    (hm : D * (D - 1) ≤ m)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D)
    (htrace : E m D = (r₂ : ℚ)) : IntegralCountFacts m D r r₂ := by
  let b := sliceCount m D
  let p := integralAmbientCount m D r
  let p₂ := integralTraceCount m D r₂
  let p₁ := integralAttachedCount m D r r₂
  let q := integralOffCount m D r r₂
  let g := integralResidualDimension m D r r₂
  let l := integralExtraTraceCount m D r r₂
  let c := integralCodeDimension m D r₂
  let L := N (m + 1) (D - 1)
  have hm₁ : 1 ≤ m := by
    have hpos : 0 < D * (D - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hcasts := actualPointCounts_cast m D r r₂ hD hm hr htrace
  change (p₂ : ℚ) = tracePointCountQ m D ∧ (p₁ : ℚ) = attachedPointCountQ m D r ∧
    (q : ℚ) = offSlicePointCountQ m D r ∧ (g : ℚ) = residualDimension m D r at hcasts
  obtain ⟨hp₂, hp₁, hq, hg⟩ := hcasts
  have hqbounds := offSlicePointCountQ_bounds m D r hD hm hr
  have hqpos : 0 < q := by
    have h : (0 : ℚ) < q := hq.symm ▸ hqbounds.1
    exact_mod_cast h
  have hqC : q ≤ N (m + 2) (D - 2) := by
    have h : (q : ℚ) < N (m + 2) (D - 2) := hq.symm ▸ hqbounds.2.1
    exact_mod_cast h.le
  have hp₁₂ : p₁ ≤ p₂ := by
    have h := attachedPointCountQ_lt_tracePointCountQ m D r hD hm hr
    rw [← hp₁, ← hp₂] at h
    exact_mod_cast h.le
  have hp₁q : p₁ = 2 * b + q := by
    change 0 < p₁ - 2 * b at hqpos
    change p₁ = 2 * b + (p₁ - 2 * b)
    omega
  have hp₁pos : 0 < p₁ := by omega
  have hp₂p : p₂ ≤ p := by
    change 0 < p - p₂ at hp₁pos
    omega
  have htraceSum : b + (b + (q + l)) = p₂ := by
    change b + (b + (q + (p₂ - p₁))) = p₂
    omega
  have hambientSum : b + (b + (q + p₂)) = p := by
    change p - p₂ = 2 * b + q at hp₁q
    omega
  have htraceLower : N m (D - 1) ≤ p₂ := by
    have h := middle_le_tracePointCountQ m D hD hm
    rw [← hp₂] at h
    exact_mod_cast h
  obtain ⟨hR, hM, hML, hgap⟩ := sliceCount_margins m D hD hm
  have hL : b ≤ L := hM.trans hML.le
  have hsliceCritical : ((L - b : ℕ) : ℚ) ≤ E (m + 1) (D - 1) := by
    have hdcast : ((D - 1 : ℕ) : ℚ) + 1 = (D : ℚ) := by
      exact_mod_cast (show D - 1 + 1 = D by omega)
    rw [Nat.cast_sub hL, E, hdcast]
    exact hgap.le
  have hres := residualDimension_bounds m D r hD hm hr
  have hden : (1 : ℚ) ≤ ((D - 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ D - 1 by omega)
  have hgUpper : g ≤ N m (D - 2) := by
    have h : (g : ℚ) < (N m (D - 2) : ℚ) / (D - 1 : ℕ) := hg.symm ▸ hres.2
    have hdiv : (N m (D - 2) : ℚ) / (D - 1 : ℕ) ≤ N m (D - 2) :=
      div_le_self (by positivity) hden
    exact_mod_cast (h.trans_le hdiv).le
  have hoffSum : q + g = N (m + 2) (D - 2) := by
    change q + (N (m + 2) (D - 2) - q) = N (m + 2) (D - 2)
    omega
  have hresCritical : (g : ℚ) ≤ E m (D - 2) := by
    have hdcast : ((D - 2 : ℕ) : ℚ) + 1 = ((D - 1 : ℕ) : ℚ) := by
      exact_mod_cast (show D - 2 + 1 = D - 1 by omega)
    rw [hg, E, hdcast]
    exact hres.2.le
  have hpure : (m + 1) * g ≤ b := by
    have h := residualDimension_slice_margin m D r hD hm hr
    rw [← hg] at h
    exact_mod_cast h.le
  have hcok := slice_cokernel_identity m D hm₁ (by omega)
  change tracePointCountQ m D - (m : ℚ) * ((L : ℚ) - b) = m * sliceRounding m D at hcok
  rw [← hp₂, ← Nat.cast_sub hL] at hcok
  have hbudget : m * (L - b) ≤ p₂ := by
    have hpos : (0 : ℚ) ≤ (m : ℚ) * sliceRounding m D :=
      mul_nonneg (by positivity) (sliceRounding_bounds m D).1
    have h : (m : ℚ) * ((L - b : ℕ) : ℚ) ≤ p₂ := by linarith
    exact_mod_cast h
  have hc : (c : ℚ) = m * sliceRounding m D := by
    change ((p₂ - m * (L - b) : ℕ) : ℚ) = _
    rw [Nat.cast_sub hbudget, Nat.cast_mul]
    exact hcok
  have hnext : N (m + 2) (D - 1) - q = L + g := by
    have h := (scalar_count_decomposition m D (by omega)).2
    change N (m + 2) (D - 1) = L + N (m + 2) (D - 2) at h
    omega
  have hsigned : ((m * g + (N (m + 2) (D - 1) - q) : ℕ) : ℚ) - 2 * b =
      2 * (c : ℚ) + ((m : ℚ) + 1) * criticalDeviation m D r := by
    calc
      _ = (L : ℚ) + ((m : ℚ) + 1) * (g : ℚ) - 2 * b := by
        rw [hnext]
        push_cast
        ring
      _ = 2 * (m : ℚ) * sliceRounding m D + ((m : ℚ) + 1) * criticalDeviation m D r := by
        rw [hg]
        exact residual_kernel_identity m D r hm₁ (by omega)
      _ = _ := by rw [hc]; ring
  exact ⟨htraceSum, hambientSum, htraceLower, hR, hL, hM, hsliceCritical,
    hgUpper, hoffSum, hresCritical, hpure, hbudget, hsigned⟩

end IdealGeneration.TwoNormalIntegral
