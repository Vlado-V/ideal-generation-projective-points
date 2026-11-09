module

public import IdealGeneration.TwoNormalIntegralInputs
public import IdealGeneration.TwoNormalMarkedCode
public import IdealGeneration.TwoNormalIntegralMarkedTransfer

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The common good marked configuration in the integral case

The slice-code conditions, the square trace, and the lower-degree slice
conditions share a marked open. The off-slice ideal is chosen on its own
open, and pair interpolation is then imposed for that fixed ideal.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d g : ℕ}

private theorem witness_mul [Infinite K] {ι : Type*} (P Q : MvPolynomial ι K)
    (hP : ∃ c, eval c P ≠ 0) (hQ : ∃ c, eval c Q ≠ 0) :
    ∃ c, eval c (P * Q) ≠ 0 := by
  obtain ⟨c, hp, hq⟩ := principal_opens_meet P Q hP hQ
  exact ⟨c, by simpa only [map_mul] using mul_ne_zero hp hq⟩

/-- The two independent scalar groups impose the residual pair conditions. -/
structure IntegralPairGood (x : PointCoordinates K (n + 2) q)
    (a b' : PointCoordinates K (n + 1) b) (d g : ℕ) : Prop where
  kernelDimension : finrank K (twoGroupEvaluation (residualPairSpace x d) a b').ker =
    (n + 1) * g + (N (n + 3) (d + 1) - q) - 2 * b
  pureA : Function.Injective ((leftGroupEvaluation (residualPairSpace x d) a).comp
    (rightProjection (residualPairSpace x d)).ker.subtype)
  pureB : Function.Injective ((rightGroupEvaluation (residualPairSpace x d) b').comp
    (leftProjection (residualPairSpace x d)).ker.subtype)

/-- All actual geometric conditions on one marked configuration. -/
structure IntegralMarkedGood (c : MarkedParameters K n b q l) (d g : ℕ) : Prop where
  sliceA : IntegralSliceGood (markedSliceA c) d
  sliceB : IntegralSliceGood (markedSliceB c) d
  trace : IntegralTraceGood (markedTraceCoordinates c) d
  offSlice : IntegralOffSliceGood (markedOffSlice c) d g
  pair : IntegralPairGood (markedOffSlice c) (markedSliceA c) (markedSliceB c) d g
  evalA : Function.Injective
    ((scalarEvaluation (chartPoint K (markedTraceCoordinates c)) (d + 1 + 1)).comp
      (tangentPointProductForm (markedSliceA c) (d + 1)).range.subtype)
  evalB : Function.Injective
    ((scalarEvaluation (chartPoint K (markedTraceCoordinates c)) (d + 1 + 1)).comp
      (tangentPointProductForm (markedSliceB c) (d + 1)).range.subtype)
  codeA : ∀ (r : ℕ) (f : Fin r ↪ Fin (b + (b + (q + l)))),
    r ≤ finrank K (TraceProductQuotient (markedSliceA c)
      (chartPoint K (markedTraceCoordinates c)) (d + 1)) →
    LinearIndependent K (traceProductCoordinate (markedSliceA c)
      (chartPoint K (markedTraceCoordinates c)) (d + 1) ∘ f)
  codeB : ∀ (r : ℕ) (f : Fin r ↪ Fin (b + (b + (q + l)))),
    r ≤ finrank K (TraceProductQuotient (markedSliceB c)
      (chartPoint K (markedTraceCoordinates c)) (d + 1)) →
    LinearIndependent K (traceProductCoordinate (markedSliceB c)
      (chartPoint K (markedTraceCoordinates c)) (d + 1) ∘ f)

private theorem traceProductCoordinate_eq_class
    (a : PointCoordinates K (n + 1) b) (z : PointCoordinates K n p)
    (e : ℕ) (i : Fin p) :
    traceProductCoordinate a (chartPoint K z) e i =
      coordinateClass (traceProductCodeMap a (chartPoint K z) e) i := by
  classical
  apply congrArg (traceProductCodeMap a (chartPoint K z) e).range.mkQ
  funext j
  by_cases hij : j = i <;> simp [hij]

/-- The common marked configuration exists under the numerical count bounds
and the three lower-dimensional or lower-degree ideal-generation inputs. -/
theorem exists_integralMarkedGood [CharZero K]
    (hn : 1 ≤ n) (d b q l g r₂ : ℕ)
    (htraceCrit : E (n + 1) (d + 1 + 1) = (r₂ : ℚ))
    (htraceCount : b + (b + (q + l)) = N (n + 1) (d + 1 + 1) - r₂)
    (htraceLower : N (n + 1) (d + 1) ≤ b + (b + (q + l)))
    (hR : N (n + 2) d ≤ b) (hL : b ≤ N (n + 2) (d + 1))
    (hM : b ≤ N (n + 1) (d + 1))
    (hsliceCrit : ((N (n + 2) (d + 1) - b : ℕ) : ℚ) ≤ E (n + 2) (d + 1))
    (hg : g ≤ N (n + 1) d) (hXcount : q + g = N (n + 3) d)
    (hXcrit : (g : ℚ) ≤ E (n + 1) d)
    (hpure : (n + 2) * g ≤ b)
    (hbudget : (n + 1) * (N (n + 2) (d + 1) - b) ≤ b + (b + (q + l)))
    (hGTrace : IdealGenerationAt K n (d + 1 + 1) (b + (b + (q + l))))
    (hGSlice : IdealGenerationAt K (n + 1) (d + 1) b)
    (hGX : IdealGenerationAt K n d (N (n + 1) d - g)) :
    ∃ c : MarkedParameters K n b q l, IntegralMarkedGood c d g := by
  let r := (n + 1) * (N (n + 2) (d + 1) - b)
  obtain ⟨S, hS, hslice⟩ := generic_integralSliceGood hn d b hR hL hM hsliceCrit hGSlice
  obtain ⟨a₀, ha₀⟩ := hS
  have hsa := hslice a₀ ha₀
  have hr₀ : r = finrank K (sliceProductSpace a₀ d) := by
    rw [finrank_sliceProductSpace a₀ hsa.normal hsa.multiplication, hsa.dimension]
  obtain ⟨U, hU, hUgood⟩ := generic_markedSliceCodes_unisolvent
    (q := q) (l := l) (d := d) (r := r) a₀ a₀ hsa.normal hsa.normal
      hsa.multiplication hsa.multiplication hsa.projectedScalar hsa.projectedScalar hr₀ hr₀
  obtain ⟨T, hT, hTgood⟩ := generic_integralTraceGood hn d (b + (b + (q + l))) r₂
    htraceCrit htraceCount htraceLower hGTrace
  obtain ⟨P, hP, hPgood⟩ := generic_integralOffSliceGood hn d q g hg hXcount hXcrit hGX
  let eA : (Fin b × Fin (n + 1)) ↪ MarkedIndex n b q l := Function.Embedding.inl
  let eB : (Fin b × Fin (n + 1)) ↪ MarkedIndex n b q l :=
    Function.Embedding.inl.trans Function.Embedding.inr
  let eZ := markedTraceIndex n b q l
  obtain ⟨hA, hAgood⟩ := principalOpen_pullback eA S ⟨a₀, ha₀⟩
  obtain ⟨hB, hBgood⟩ := principalOpen_pullback eB S ⟨a₀, ha₀⟩
  obtain ⟨hZ, hZgood⟩ := principalOpen_pullback eZ T hT
  let D := rename eA S * rename eB S * rename eZ T * U
  have hD : ∃ c : MarkedParameters K n b q l, eval c D ≠ 0 :=
    witness_mul _ _ (witness_mul _ _ (witness_mul _ _ hA hB) hZ) hU
  have hpair : ∀ x : PointCoordinates K (n + 2) q, eval x P ≠ 0 →
      ∃ Q : MvPolynomial ((Fin b × Fin (n + 1)) ⊕ (Fin b × Fin (n + 1))) K,
        (∃ c, eval c Q ≠ 0) ∧ ∀ c, eval c Q ≠ 0 →
          IntegralPairGood x (c ∘ Sum.inl) (c ∘ Sum.inr) d g := by
    intro x hx
    have hX := hPgood x hx
    have hp : (n + 2) * finrank K (pointDegreePiece K x d) ≤ b := by
      rw [hX.dimension]
      exact hpure
    obtain ⟨Q, hQ, hQgood⟩ := generic_residualPair_conditions x hX.sNonzero hX.tNonzero
      hX.trace hX.product b hp
    refine ⟨Q, hQ, fun c hc => ?_⟩
    obtain ⟨hk, hL, hR⟩ := hQgood c hc
    rw [hX.dimension, hX.nextDimension] at hk
    exact ⟨hk, hL, hR⟩
  obtain ⟨c, hcD, hcP, hcPair⟩ := exists_marked_on_joint_and_pair_opens D hD P hP
    (fun x a b' => IntegralPairGood x a b' d g) hpair
  have hparts : ((eval c (rename eA S) ≠ 0 ∧ eval c (rename eB S) ≠ 0) ∧
      eval c (rename eZ T) ≠ 0) ∧ eval c U ≠ 0 := by
    simpa only [D, map_mul, mul_ne_zero_iff] using hcD
  have ha : IntegralSliceGood (markedSliceA c) d := hslice _ (hAgood c hparts.1.1.1)
  have hb : IntegralSliceGood (markedSliceB c) d := hslice _ (hBgood c hparts.1.1.2)
  have hz : IntegralTraceGood (markedTraceCoordinates c) d := hTgood _ (hZgood c hparts.1.2)
  have hrA : r = finrank K (sliceProductSpace (markedSliceA c) d) := by
    rw [finrank_sliceProductSpace _ ha.normal ha.multiplication, ha.dimension]
  have hrB : r = finrank K (sliceProductSpace (markedSliceB c) d) := by
    rw [finrank_sliceProductSpace _ hb.normal hb.multiplication, hb.dimension]
  have ⟨hevalA, hcodeA⟩ := orderedTraceProduct_coordinateClasses (markedSliceA c)
    (markedTraceCoordinates c) ha.normal ha.multiplication hrA hbudget
    (fun f => (hUgood c hparts.2 f).1)
  have ⟨hevalB, hcodeB⟩ := orderedTraceProduct_coordinateClasses (markedSliceB c)
    (markedTraceCoordinates c) hb.normal hb.multiplication hrB hbudget
    (fun f => (hUgood c hparts.2 f).2)
  refine ⟨c, ha, hb, hz, hPgood _ hcP, hcPair, hevalA, hevalB, ?_, ?_⟩
  · intro k f hk
    simpa only [Function.comp_def, traceProductCoordinate_eq_class] using hcodeA k f hk
  · intro k f hk
    simpa only [Function.comp_def, traceProductCoordinate_eq_class] using hcodeB k f hk

end IdealGeneration.TwoNormalIntegral
