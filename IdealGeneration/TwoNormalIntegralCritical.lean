module

public import IdealGeneration.TwoNormalIntegralConfiguration
public import IdealGeneration.TwoNormalIntegralDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The marked Euler witness at each ambient critical count

The numerical identities fix the marked counts. The genuine pair kernel and
Euler-fiber dimensions then determine the signed residual count in the
marked-motion theorem.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoGroupInterpolation
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d : ℕ}

/-- Maximal ambient fiber rank at the marked configuration, or on its
polynomial normal motion. -/
def IntegralMarkedMotionResult (c : MarkedParameters K n b q l) (d : ℕ) : Prop :=
  let a := markedSliceA c
  let b' := markedSliceB c
  let x := chartPoint K (markedOffSlice c)
  let Z := markedTraceCoordinates c
  let z := chartPoint K Z
  HasMaximalRank (ambientFiberEvaluation a b' z x (d + 1 + 1)) ∨
    ∃ (v u : Fin (b + (b + (q + l))) → K),
      (∀ i, v i = 0 ∨ v i = 1) ∧ (∀ i, u i = 0 ∨ u i = 1) ∧
      ∃ P : MvPolynomial (Fin 1) K, eval 0 P ≠ 0 ∧
        ∀ ε : Fin 1 → K, ε 0 ≠ 0 → eval ε P ≠ 0 →
          HasMaximalRank (markedMovingEvaluation (ambientFixedEvaluation a b' z x (d + 1 + 1)) z
            (ambientTraceInclusion a b' z x) (commonTracePoint_chart_last Z) v u ε)

/-- At either critical ambient count, the integral trace and the two lower
degrees give a good marked configuration with a maximal-rank Euler witness. -/
theorem exists_integral_critical_marked_motion [CharZero K]
    (n d r r₂ : ℕ) (hD : 4 ≤ d + 1 + 1)
    (hm : (d + 1 + 1) * (d + 1) ≤ n + 1)
    (hr : r = lowerCritical (n + 3) (d + 1 + 1) ∨
      r = upperCritical (n + 3) (d + 1 + 1))
    (htrace : E (n + 1) (d + 1 + 1) = (r₂ : ℚ))
    (hTraceGen : ∀ p, IdealGenerationAt K n (d + 1 + 1) p)
    (hPrev : ∀ p, IdealGenerationAt K (n + 1) (d + 1) p)
    (hPrev₂ : ∀ p, IdealGenerationAt K n d p) :
    let m := n + 1
    let D := d + 1 + 1
    let b := sliceCount m D
    let q := integralOffCount m D r r₂
    let l := integralExtraTraceCount m D r r₂
    let g := integralResidualDimension m D r r₂
    ∃ c : MarkedParameters K n b q l, IntegralMarkedGood c d g ∧ IntegralMarkedMotionResult c d := by
  let m := n + 1
  let D := d + 1 + 1
  let b := sliceCount m D
  let q := integralOffCount m D r r₂
  let l := integralExtraTraceCount m D r r₂
  let g := integralResidualDimension m D r r₂
  let p := integralAmbientCount m D r
  let p₂ := integralTraceCount m D r₂
  let c₂ := integralCodeDimension m D r₂
  let Ntrace := b + (b + (q + l))
  have hDm : D - 1 = d + 1 := rfl
  have hDe : D - 2 = d := by dsimp [D]; omega
  have hm' : D * (D - 1) ≤ m := by simpa only [hDm] using hm
  have hn : 1 ≤ n := by
    have hprod : 2 ≤ D * (d + 1) := Nat.mul_le_mul
      (show 1 ≤ D from (by decide : 1 ≤ 4).trans hD) (show 2 ≤ d + 1 by omega)
    dsimp [m] at hm'
    rw [hDm] at hm'
    omega
  have counts := integralCountFacts m D r r₂ hD hm' hr htrace
  have hZcount : Ntrace = p₂ := counts.traceSum
  have hZlower : N m (d + 1) ≤ Ntrace := by
    rw [hZcount]
    simpa only [hDm] using counts.traceLower
  have hR : N (m + 1) d ≤ b := by simpa only [hDe] using counts.sliceLower
  have hL : b ≤ N (m + 1) (d + 1) := by simpa only [hDm] using counts.sliceUpper
  have hM : b ≤ N m (d + 1) := by simpa only [hDm] using counts.sliceTraceUpper
  have hsliceCrit : ((N (m + 1) (d + 1) - b : ℕ) : ℚ) ≤ E (m + 1) (d + 1) := by
    simpa only [hDm] using counts.sliceCritical
  have hg : g ≤ N m d := by simpa only [hDe] using counts.residualUpper
  have hXcount : q + g = N (m + 2) d := by simpa only [hDe] using counts.offSum
  have hXcrit : (g : ℚ) ≤ E m d := by simpa only [hDe] using counts.residualCritical
  have hbudget : m * (N (m + 1) (d + 1) - b) ≤ Ntrace := by
    rw [hZcount]
    simpa only [hDm] using counts.codeBudget
  obtain ⟨c, hc⟩ := exists_integralMarkedGood hn d b q l g r₂ htrace hZcount hZlower
    hR hL hM hsliceCrit hg hXcount hXcrit counts.pureBound hbudget
    (hTraceGen Ntrace) (hPrev b) (hPrev₂ (N m d - g))
  change ∃ c : MarkedParameters K n b q l, IntegralMarkedGood c d g ∧ IntegralMarkedMotionResult c d
  refine ⟨c, hc, ?_⟩
  let a := markedSliceA c
  let b' := markedSliceB c
  let x := markedOffSlice c
  let Z := markedTraceCoordinates c
  let z := chartPoint K Z
  let W := AmbientFiberValues a b' z (chartPoint K x)
  let σ : ℤ := (finrank K (AmbientEuler K m d) : ℤ) - finrank K W
  have hTotal : b + (b + (q + Ntrace)) = p := by rw [hZcount]; exact counts.ambientSum
  have hW : finrank K W = (n + 2) * p := by
    rw [marked_ambientFiber_finrank a b' x Z]
    exact congrArg (fun t : ℕ => (n + 2) * t) hTotal
  have hrN : r ≤ N (n + 3) D := by
    rcases hr with h | h
    · rw [h]
      exact (lowerCritical_mem_cell (n + 3) D (by omega) (by dsimp [D]; omega)).2.trans
        (Nat.sub_le _ _)
    · rw [h]
      exact (upperCritical_mem_cell (n + 3) D (by omega) (by dsimp [D]; omega)).2.trans
        (Nat.sub_le _ _)
  have hσ : (σ : ℚ) = ((n : ℚ) + 2) * criticalDeviation m D r := by
    change (((finrank K (AmbientEuler K m d) : ℤ) - finrank K W : ℤ) : ℚ) = _
    rw [hW]
    exact ambientEuler_discrepancy n d r p hrN rfl
  have hmQ : ((m : ℚ) + 1) = (n : ℚ) + 2 := by
    dsimp [m]
    push_cast
    ring
  let Acount := m * g + (N (m + 2) (d + 1) - q)
  have hsignedQ : (Acount : ℚ) - 2 * b = 2 * c₂ + (σ : ℚ) := by
    rw [hσ, ← hmQ]
    have h := counts.residualSigned
    rw [hDm] at h
    exact h
  have hsigned : (Acount : ℤ) - 2 * (b : ℤ) = 2 * (c₂ : ℤ) + σ := by
    exact_mod_cast hsignedQ
  have hc₂ : Ntrace - m * (finrank K (Forms K (m + 1) (d + 1)) - b) = c₂ := by
    rw [finrank_forms, hZcount]
    change p₂ - m * (N (m + 1) (d + 1) - b) = p₂ - m * (N (m + 1) (D - 1) - b)
    rw [hDm]
  have hpair : (finrank K (twoGroupEvaluation (residualPairSpace x d) a b').ker : ℤ) =
      max 0 (2 * ((Ntrace - m * (finrank K (Forms K (m + 1) (d + 1)) - b) : ℕ) : ℤ) + σ) := by
    rw [hc.pair.kernelDimension, hc₂]
    change ((Acount - 2 * b : ℕ) : ℤ) = max 0 (2 * (c₂ : ℤ) + σ)
    omega
  exact integral_marked_fiber_transfer a b' x z (commonTracePoint_chart_last Z)
    hc.sliceA.normal hc.sliceB.normal hc.offSlice.sNonzero hc.offSlice.tNonzero
    hc.trace.euler hc.sliceA.scalar hc.sliceB.scalar hc.sliceA.multiplication hc.sliceB.multiplication
    hc.evalA hc.evalB hc.sliceA.lowerScalar hc.sliceB.lowerScalar hc.trace.lowerScalar
    hc.offSlice.trace hc.offSlice.product hc.pair.pureA hc.pair.pureB hc.codeA hc.codeB σ rfl hpair

end IdealGeneration.TwoNormalIntegral
