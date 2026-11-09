module

public import IdealGeneration.TwoNormalAmbientKernel
public import IdealGeneration.TwoNormalAmbientCokernel
public import IdealGeneration.TwoGroupInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Comparing component and Euler fiber evaluations

The kernel calculation can use every polynomial component. The cokernel
calculation uses the Euler fibers. Their evaluations have the same kernel.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial TwoNormalSlice TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ)

/-- The full component and genuine Euler fiber evaluations vanish together. -/
theorem ambientEvaluation_eq_zero_iff_fiber {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (f : HyperplaneEuler.Relations K (m + 2) d) :
    ambientEvaluation K m a b x z d f = 0 ↔
      ambientFiberEvaluation a b z (chartPoint K x) d f = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun v => v.1.1) h
    · apply Prod.ext
      · apply Subtype.ext
        funext i j
        change eval (ambientPointB b i) (f.val j).val = 0
        rw [ambientPointB_eq]
        exact congrFun (congrFun (congrArg (fun v => v.1.2) h) i) j
      · apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun v => v.2.2) h
        · apply Subtype.ext
          exact congrArg (fun v => v.2.1) h
  · intro h
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun v => v.1.val) h
      · funext i j
        have hi := congrFun (congrFun (congrArg (fun v => v.2.1.val) h) i) j
        change eval (ambientPointB b i) (f.val j).val = 0 at hi
        rw [ambientPointB_eq] at hi
        exact hi
    · apply Prod.ext
      · exact congrArg (fun v => v.2.2.2.val) h
      · exact congrArg (fun v => v.2.2.1.val) h

/-- Both evaluation maps define the same submodule of ambient Euler relations. -/
theorem ambientEvaluation_ker_eq_fiber {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K) :
    (ambientEvaluation K m a b x z d).ker =
      (ambientFiberEvaluation a b z (chartPoint K x) d).ker := by
  ext f
  exact ambientEvaluation_eq_zero_iff_fiber K m a b x z f

/-- The residual pair kernel is the kernel of genuine ambient Euler fiber evaluation. -/
def pairAmbientFiberKernelEquiv {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (sliceEvaluation b z (d + 1 + 1))) :
    (pairEvaluation K m a b x d).ker ≃ₗ[K]
      (ambientFiberEvaluation a b z (chartPoint K x) (d + 1 + 1)).ker :=
  (pairAmbientKernelEquiv K m a b x z ha hb hxs hxt hA hB).trans
    (LinearEquiv.ofEq _ _ (ambientEvaluation_ker_eq_fiber K m a b x z))

/-- Parametrizing the pair image identifies the two scalar evaluation kernels. -/
def pairEvaluationRangeKernelEquiv {p s d : ℕ}
    (a b : PointCoordinates K m p) (x : PointCoordinates K (m + 1) s)
    (hPair : Function.Injective (residualPair K m (d := d) x)) :
    (pairEvaluation K m a b x d).ker ≃ₗ[K]
      (twoGroupEvaluation (residualPair K m (d := d) x).range a b).ker := by
  let P := residualPair K m (d := d) x
  let e := LinearEquiv.ofInjective P hPair
  apply e.ofSubmodules
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    change twoGroupEvaluation P.range a b (e w) = 0
    exact hw
  · intro hu
    obtain ⟨w, rfl⟩ := e.surjective u
    exact ⟨w, hu, rfl⟩

/-- The kernel counted by the two-group interpolation lemma is the actual
ambient Euler fiber kernel. -/
def residualPairAmbientFiberKernelEquiv {p s q d : ℕ}
    (a b : PointCoordinates K m p) (x : PointCoordinates K (m + 1) s)
    (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (sliceEvaluation b z (d + 1 + 1)))
    (htrace : Function.Injective ((restrictTraceForm K m d).comp
      (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    (twoGroupEvaluation (residualPair K m (d := d) x).range a b).ker ≃ₗ[K]
      (ambientFiberEvaluation a b z (chartPoint K x) (d + 1 + 1)).ker :=
  (pairEvaluationRangeKernelEquiv K m a b x
    (residualPair_injective K m x hxs htrace hproduct)).symm.trans
    (pairAmbientFiberKernelEquiv K m a b x z ha hb hxs hxt hA hB)

end IdealGeneration.TwoNormalTrace
