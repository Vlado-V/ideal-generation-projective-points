module

public import IdealGeneration.TwoNormalMarkedMotion
public import IdealGeneration.TwoNormalAmbientComparison
public import IdealGeneration.TwoNormalNormalClasses
public import IdealGeneration.TwoNormalSource
public import IdealGeneration.TwoNormalResidualInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The integral trace at a marked configuration

The full Euler fiber evaluation has the pair-space kernel and the two
slice-code quotients. These identifications feed the actual polynomial
motion of the marked trace points.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoNormalTrace TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m b q p d : ℕ}

/-- The fixed ambient evaluation on the two slices and the residual group. -/
def ambientFixedEvaluation (a b' : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (x : Fin q → Fin (m + 2) → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 2) d →ₗ[K] AmbientFiberValues a b' z x :=
  (traceFiberEvaluation (ambientPointA a) d).prod
    ((traceFiberEvaluation (ambientPointB b') d).prod
      ((0 : HyperplaneEuler.Relations K (m + 2) d →ₗ[K] TraceFibers (ambientTracePoint z)).prod
        (traceFiberEvaluation x d)))

/-- Insert the moving trace fiber in the ambient condition space. -/
def ambientTraceInclusion (a b' : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (x : Fin q → Fin (m + 2) → K) :
    TraceFibers (ambientTracePoint z) →ₗ[K] AmbientFiberValues a b' z x where
  toFun u := (0, 0, u, 0)
  map_add' u v := by simp
  map_smul' c u := by simp

/-- The special evaluation in the motion is exactly the genuine ambient
fiber evaluation, in its original group order. -/
theorem markedBaseEvaluation_eq_ambient (a b' : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (x : Fin q → Fin (m + 2) → K) :
    markedBaseEvaluation (ambientFixedEvaluation a b' z x (d + 1 + 1)) z
        (ambientTraceInclusion a b' z x) = ambientFiberEvaluation a b' z x (d + 1 + 1) := by
  apply LinearMap.ext
  intro F
  change (traceFiberEvaluation (ambientPointA a) (d + 1 + 1) F,
      traceFiberEvaluation (ambientPointB b') (d + 1 + 1) F,
      0, traceFiberEvaluation x (d + 1 + 1) F) +
    (0, 0, traceFiberEvaluation (ambientTracePoint z) (d + 1 + 1) F, 0) = _
  simp [ambientFiberEvaluation]

/-- The trace product evaluation as a map from the ideal coefficient tuple. -/
abbrev traceProductCodeMap (a : PointCoordinates K m b) (z : Fin p → Fin m → K) (e : ℕ) :=
  (scalarEvaluation z (e + 1)).comp (tangentPointProductForm a e)

/-- The scalar quotient code for a slice. -/
abbrev TraceProductQuotient (a : PointCoordinates K m b) (z : Fin p → Fin m → K) (e : ℕ) :=
  (Fin p → K) ⧸ (traceProductCodeMap a z e).range

/-- Both slice codes have the dimension given by their common point count. -/
theorem traceProductQuotient_finrank (a : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (e : ℕ)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hscalar : Function.Surjective (pointEvaluation K a e))
    (hmul : Function.Injective (pointMultiplication a e))
    (hcode : Function.Injective ((scalarEvaluation z (e + 1)).comp
      (tangentPointProductForm a e).range.subtype)) :
    finrank K (TraceProductQuotient a z e) =
      p - m * (finrank K (Forms K (m + 1) e) - b) := by
  have hpiece := (pointEvaluation K a e).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hscalar, finrank_top] at hpiece
  have hb : finrank K (Fin b → K) = b := by simp
  rw [hb] at hpiece
  change b + finrank K (pointDegreePiece K a e) = finrank K (Forms K (m + 1) e) at hpiece
  have hpiece' : finrank K (pointDegreePiece K a e) = finrank K (Forms K (m + 1) e) - b := by omega
  have hrange : finrank K (traceProductCodeMap a z e).range =
      m * (finrank K (Forms K (m + 1) e) - b) := by
    change finrank K ((scalarEvaluation z (e + 1)).comp (tangentPointProductForm a e)).range = _
    rw [range_comp_range_subtype, LinearMap.finrank_range_of_inj hcode,
      finrank_tangentPointProductForm_range a ha hmul, hpiece']
  have hq : finrank K (TraceProductQuotient a z e) +
      m * (finrank K (Forms K (m + 1) e) - b) = p := calc
    _ = finrank K (TraceProductQuotient a z e) + finrank K (traceProductCodeMap a z e).range := by
      rw [hrange]
    _ = finrank K (Fin p → K) := (traceProductCodeMap a z e).range.finrank_quotient_add_finrank
    _ = p := by simp
  omega

/-- The genuine ambient cokernel surjects onto both scalar quotient codes. -/
theorem ambientCokernelTraceCodes_surjective (a b' : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (x : Fin q → Fin (m + 2) → K) (e : ℕ)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (e + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a e))
    (hscalarB : Function.Surjective (pointEvaluation K b' e)) :
    Function.Surjective (ambientCokernelTraceCodes a b' z x e ha hb htrace hscalarA hscalarB) :=
  ((sliceCokernelTraceProductEquiv a z e ha htrace hscalarA).prodCongr
    (sliceCokernelTraceProductEquiv b' z e hb htrace hscalarB)).surjective.comp
      (ambientCokernelToSlices_surjective a b' z x (e + 1) ha hb htrace.2)

/-- The coefficient tuple of an ambient-kernel relation, extracted linearly. -/
def ambientKernelCoefficients (a b' : PointCoordinates K m b)
    (x : PointCoordinates K (m + 1) q) (z : Fin p → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (sliceEvaluation b' z (d + 1 + 1))) :
    (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)).ker →ₗ[K]
      NormalCoefficients K m d :=
  (parameterLift K m x d).comp ((pairEvaluation K m a b' x d).ker.subtype.comp
    (pairAmbientFiberKernelEquiv K m a b' x z ha hb hxs hxt hA hB).symm.toLinearMap)

/-- Reconstructing the Euler tuple recovers the original kernel relation. -/
theorem ambientKernelCoefficients_reconstruct (a b' : PointCoordinates K m b)
    (x : PointCoordinates K (m + 1) q) (z : Fin p → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (sliceEvaluation b' z (d + 1 + 1)))
    (F : (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)).ker) :
    residualEuler K m d (ambientKernelCoefficients a b' x z ha hb hxs hxt hA hB F) = F.val := by
  let e := pairAmbientFiberKernelEquiv K m a b' x z ha hb hxs hxt hA hB
  exact congrArg (fun f : (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)).ker => f.val)
    (e.apply_symm_apply F)

/-- Both normal coefficient families span the dual of the actual ambient
kernel, by their identification with the two trace maps on the pair kernel. -/
theorem ambientKernelCoefficients_spans (a b' : PointCoordinates K m b)
    (x : PointCoordinates K (m + 1) q) (z : Fin p → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (sliceEvaluation b' z (d + 1 + 1)))
    (hpair : Function.Injective (residualPair K m (d := d) x))
    (hsmallA : Function.Injective (pointEvaluation K a d))
    (hsmallB : Function.Injective (pointEvaluation K b' d))
    (hpureA : Function.Injective ((leftGroupEvaluation (residualPairSpace x d) a).comp
      (rightProjection (residualPairSpace x d)).ker.subtype))
    (hpureB : Function.Injective ((rightGroupEvaluation (residualPairSpace x d) b').comp
      (leftProjection (residualPairSpace x d)).ker.subtype))
    (hZ : Function.Injective (scalarEvaluation z (d + 1))) :
    Submodule.span K (Set.range (fun i : Fin p => (normalSCoefficient (z i)).comp
      (ambientKernelCoefficients a b' x z ha hb hxs hxt hA hB))) = ⊤ ∧
    Submodule.span K (Set.range (fun i : Fin p => (normalTCoefficient (z i)).comp
      (ambientKernelCoefficients a b' x z ha hb hxs hxt hA hB))) = ⊤ := by
  let eP := pairAmbientFiberKernelEquiv K m a b' x z ha hb hxs hxt hA hB
  let eR := pairEvaluationRangeKernelEquiv K m a b' x hpair
  let e := eP.symm.trans eR
  let U := residualPairSpace x d
  let S := (rightTraceOnPairKernel U a b').comp e.toLinearMap
  let T := -((leftTraceOnPairKernel U a b').comp e.toLinearMap)
  have hS : Function.Injective S :=
    (rightTraceOnPairKernel_injective U a b' hb hsmallB hpureA).comp e.injective
  have hT : Function.Injective T := by
    intro F G hFG
    apply e.injective
    apply leftTraceOnPairKernel_injective U a b' ha hsmallA hpureB
    exact neg_inj.mp hFG
  let w := ambientKernelCoefficients a b' x z ha hb hxs hxt hA hB
  have heqS : (fun i : Fin p => (normalSCoefficient (z i)).comp w) =
      fun i => (evaluationLinear K m (d + 1) (z i)).comp S := by
    funext i
    apply LinearMap.ext
    intro F
    rfl
  have heqT : (fun i : Fin p => (normalTCoefficient (z i)).comp w) =
      fun i => (evaluationLinear K m (d + 1) (z i)).comp T := by
    funext i
    apply LinearMap.ext
    intro F
    let v := (eP.symm F).val
    let h := v.2.val.val
    let t := (tangentProduct K m d (fun j => (v.1 j).val)).val
    change eval (z i) (restrictTrace K m (-h - t)) =
      eval (z i) (-(hyperplaneRestrict K m (restrictA K m (h + t))))
    rw [restrictA_trace]
    simp only [map_sub, map_neg, map_add]
    ring
  let : AddCommGroup (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)).ker :=
    Module.addCommMonoidToAddCommGroup K
  let : FiniteDimensional K (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)).ker :=
    FiniteDimensional.of_injective S hS
  change Submodule.span K (Set.range (fun i : Fin p => (normalSCoefficient (z i)).comp w)) = ⊤ ∧
    Submodule.span K (Set.range (fun i : Fin p => (normalTCoefficient (z i)).comp w)) = ⊤
  rw [heqS, heqT]
  constructor
  · apply scalarRows_span_of_injective
    exact hZ.comp hS
  · apply scalarRows_span_of_injective
    exact hZ.comp hT

end IdealGeneration.TwoNormalIntegral
