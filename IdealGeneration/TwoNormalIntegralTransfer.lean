module

public import IdealGeneration.TwoNormalIntegralCritical
public import IdealGeneration.TwoNormalEndpoint
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The integral two-normal transfer

The marked rank construction gives witnesses at both critical counts.
The ordinary point-count reduction then proves Proposition 4.5.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral

open TwoNormalSlice

variable {K : Type*} [Field K] [CharZero K]

private theorem idealGenerationAt_of_integralMarkedMotion
    {n b q l d g : ℕ} (c : MarkedParameters K n b q l)
    (hgood : IntegralMarkedGood c d g) (hmotion : IntegralMarkedMotionResult c d) :
    IdealGenerationAt K (n + 2) (d + 1 + 1) (b + (b + (q + (b + (b + (q + l)))))) := by
  let a := markedSliceA c
  let b' := markedSliceB c
  let x := markedOffSlice c
  let Z := markedTraceCoordinates c
  let z := chartPoint K Z
  have hz := commonTracePoint_chart_last Z
  have hscalar := markedScalarEvaluation_surjective_of_groups (d := d) a b' z x
    hgood.sliceA.normal hgood.sliceB.normal hgood.offSlice.sNonzero hgood.offSlice.tNonzero
    hgood.sliceA.scalar hgood.sliceB.scalar hgood.offSlice.scalar hgood.trace.scalar
  rw [Nat.add_comm q (b + (b + (q + l)))]
  unfold IntegralMarkedMotionResult at hmotion
  rcases hmotion with hEuler | ⟨v, u, _, _, P, hP, hEuler⟩
  · exact idealGenerationAt_of_marked_ambient_evaluation (by omega) a b' z x hz hscalar hEuler
  · exact idealGenerationAt_of_marked_moving_evaluation (by omega) a b' z x hz hscalar
      v u P hP hEuler

private theorem integral_two_normal_transfer_from_marked
    (n d r₂ : ℕ) (hD : 4 ≤ d + 1 + 1)
    (hm : (d + 1 + 1) * (d + 1) ≤ n + 1)
    (htrace : E (n + 1) (d + 1 + 1) = (r₂ : ℚ))
    (hTraceGen : ∀ p, IdealGenerationAt K n (d + 1 + 1) p)
    (hSlice : ∀ p, IdealGenerationAt K (n + 1) (d + 1) p)
    (hResidual : ∀ p, IdealGenerationAt K n d p) :
    ∀ p, IdealGenerationAt K (n + 2) (d + 1 + 1) p := by
  let m := n + 1
  let D := d + 1 + 1
  have hDm : D - 1 = d + 1 := rfl
  have hm' : D * (D - 1) ≤ m := by simpa only [hDm] using hm
  have hcrit (r : ℕ)
      (hr : r = lowerCritical (n + 3) D ∨ r = upperCritical (n + 3) D) :
      IdealGenerationAt K (n + 2) D (N (n + 3) D - r) := by
    let b := sliceCount m D
    let q := integralOffCount m D r r₂
    let l := integralExtraTraceCount m D r r₂
    obtain ⟨c, hgood, hmotion⟩ := exists_integral_critical_marked_motion n d r r₂ hD hm hr htrace
      hTraceGen hSlice hResidual
    have htotal : b + (b + (q + (b + (b + (q + l))))) = N (n + 3) D - r := by
      have counts := integralCountFacts m D r r₂ hD hm' hr htrace
      have htraceCount : b + (b + (q + l)) = integralTraceCount m D r₂ := counts.traceSum
      rw [htraceCount]
      exact counts.ambientSum
    have hw := idealGenerationAt_of_integralMarkedMotion c hgood hmotion
    change IdealGenerationAt K (n + 2) D (b + (b + (q + (b + (b + (q + l)))))) at hw
    rwa [htotal] at hw
  exact idealGenerationAt_all_of_critical (by omega : 1 ≤ n + 2) (by omega)
    (hcrit _ (Or.inl rfl)) (hcrit _ (Or.inr rfl))

/-- Proposition 4.5. An integral trace critical value lets the two-normal
construction transfer ideal generation to the ambient dimension. -/
theorem proposition4_5
    (n D : ℕ) (hD : 4 ≤ D) (hlarge : D * (D - 1) < n)
    (hIntegral : ∃ r₂ : ℕ, E (n - 1) D = (r₂ : ℚ))
    (hSlice : ∀ p, IdealGenerationAt K (n - 1) (D - 1) p)
    (hResidual : ∀ p, IdealGenerationAt K (n - 2) (D - 2) p)
    (hTrace : ∀ p, IdealGenerationAt K (n - 2) D p) :
    ∀ p, IdealGenerationAt K n D p := by
  obtain ⟨r₂, hr₂⟩ := hIntegral
  let n₀ := n - 2
  let d := D - 2
  have hprod : 2 ≤ D * (D - 1) := Nat.mul_le_mul (show 1 ≤ D by omega) (show 2 ≤ D - 1 by omega)
  have hn : n₀ + 2 = n := by dsimp [n₀]; omega
  have hNm : n₀ + 1 = n - 1 := by dsimp [n₀]; omega
  have hDm : d + 1 = D - 1 := by dsimp [d]; omega
  have hDe : d + 1 + 1 = D := by dsimp [d]; omega
  have hlarge' : (d + 1 + 1) * (d + 1) ≤ n₀ + 1 := by rw [hDe, hDm, hNm]; omega
  have htrace' : E (n₀ + 1) (d + 1 + 1) = (r₂ : ℚ) := by rw [hNm, hDe]; exact hr₂
  have hSlice' : ∀ p, IdealGenerationAt K (n₀ + 1) (d + 1) p := by
    simpa only [hNm, hDm] using hSlice
  have hTrace' : ∀ p, IdealGenerationAt K n₀ (d + 1 + 1) p := by
    simpa only [hDe] using hTrace
  have h := integral_two_normal_transfer_from_marked n₀ d r₂ (by rwa [hDe])
    hlarge' htrace' hTrace' hSlice' hResidual
  simpa only [hn, hDe] using h

end IdealGeneration.TwoNormalIntegral
