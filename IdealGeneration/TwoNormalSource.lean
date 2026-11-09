module

public import IdealGeneration.TwoGroupInterpolation
public import IdealGeneration.HyperplanePolynomial
public import IdealGeneration.ScalarSelection
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Source functionals for the two-normal response

A zero common trace first forces a slice polynomial to vanish by lower-degree
scalar interpolation. Pure-side injectivity then kills the whole residual
pair. Thus both normal trace families span the dual of the residual kernel.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d b : ℕ}

/-- A slice form with zero trace and zero point values vanishes when division
by its nonvanishing normal coordinate is tested by an injective evaluation. -/
theorem sliceForm_eq_zero_of_trace_and_values
    (a : PointCoordinates K m b)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (heval : Function.Injective (pointEvaluation K a d))
    (f : Forms K (m + 1) (d + 1))
    (htrace : restrictForm K m (d + 1) f = 0)
    (hvalues : pointEvaluation K a (d + 1) f = 0) : f = 0 := by
  obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K m f).mp htrace
  have hgvalues : pointEvaluation K a d g = 0 := by
    ext i
    have hi := congrFun hvalues i
    change eval (chartPoint K a i) f.val = 0 at hi
    rw [hg, map_mul, eval_X] at hi
    exact (mul_eq_zero.mp hi).resolve_left (ha i)
  have hgzero : g = 0 := heval (by simpa using hgvalues)
  apply Subtype.ext
  simp [hg, hgzero]

variable (U : Submodule K
  (Forms K (m + 1) (d + 1) × Forms K (m + 1) (d + 1)))
  (a b' : PointCoordinates K m b)

local instance pairKernelGroup : AddCommGroup (twoGroupEvaluation U a b').ker :=
  Module.addCommMonoidToAddCommGroup K

/-- The common trace of the first scalar component on the pair kernel. -/
def leftTraceOnPairKernel : (twoGroupEvaluation U a b').ker →ₗ[K] Forms K m (d + 1) :=
  (restrictForm K m (d + 1)).comp
    ((leftProjection U).comp (twoGroupEvaluation U a b').ker.subtype)

/-- The common trace of the second scalar component on the pair kernel. -/
def rightTraceOnPairKernel : (twoGroupEvaluation U a b').ker →ₗ[K] Forms K m (d + 1) :=
  (restrictForm K m (d + 1)).comp
    ((rightProjection U).comp (twoGroupEvaluation U a b').ker.subtype)

/-- Lower-degree interpolation on the second slice makes its normal-trace
map injective on the entire residual kernel. -/
theorem rightTraceOnPairKernel_injective
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (heval : Function.Injective (pointEvaluation K b' d))
    (hpure : Function.Injective ((leftGroupEvaluation U a).comp
      (rightProjection U).ker.subtype)) :
    Function.Injective (rightTraceOnPairKernel U a b') := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hv := congrArg Prod.snd f.property
  have hz : rightProjection U f.val = 0 :=
    sliceForm_eq_zero_of_trace_and_values b' hb heval (rightProjection U f.val) hf hv
  have hp : (⟨f.val, hz⟩ : (rightProjection U).ker) = 0 := by
    apply hpure
    have hv' := congrArg Prod.fst f.property
    change leftGroupEvaluation U a f.val = 0 at hv'
    change leftGroupEvaluation U a f.val = leftGroupEvaluation U a 0
    rw [map_zero]
    exact hv'
  apply Subtype.ext
  exact congrArg (fun q : (rightProjection U).ker => q.val) hp

/-- The symmetric normal-trace map is injective on the residual kernel. -/
theorem leftTraceOnPairKernel_injective
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (heval : Function.Injective (pointEvaluation K a d))
    (hpure : Function.Injective ((rightGroupEvaluation U b').comp
      (leftProjection U).ker.subtype)) :
    Function.Injective (leftTraceOnPairKernel U a b') := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hv := congrArg Prod.fst f.property
  have hz : leftProjection U f.val = 0 :=
    sliceForm_eq_zero_of_trace_and_values a ha heval (leftProjection U f.val) hf hv
  have hp : (⟨f.val, hz⟩ : (leftProjection U).ker) = 0 := by
    apply hpure
    have hv' := congrArg Prod.snd f.property
    change rightGroupEvaluation U b' f.val = 0 at hv'
    change rightGroupEvaluation U b' f.val = rightGroupEvaluation U b' 0
    rw [map_zero]
    exact hv'
  apply Subtype.ext
  exact congrArg (fun q : (leftProjection U).ker => q.val) hp

/-- Injective scalar evaluation on the trace yields a spanning family of
source functionals for either of the two normal components. -/
theorem traceSourceFunctionals_span {p : ℕ}
    (T : (twoGroupEvaluation U a b').ker →ₗ[K] Forms K m (d + 1))
    (hT : Function.Injective T)
    (z : Fin p → Fin m → K)
    (hz : Function.Injective (LinearMap.pi (fun i => evaluationLinear K m (d + 1) (z i)))) :
    Submodule.span K (Set.range (fun i : Fin p =>
      (evaluationLinear K m (d + 1) (z i)).comp T)) = ⊤ := by
  let : FiniteDimensional K (twoGroupEvaluation U a b').ker :=
    FiniteDimensional.of_injective T hT
  apply scalarRows_span_of_injective
  exact hz.comp hT

end IdealGeneration.TwoNormalIntegral
