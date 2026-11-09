module

public import IdealGeneration.TwoNormalAmbientFiber
public import IdealGeneration.TwoNormalKernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The ambient cokernel maps onto both slice cokernels

Every compatible pair of slice values lifts to the ambient Euler fibers.
Polynomial restriction identifies the two projections of ambient section
evaluation with evaluation of its actual slice restrictions. The projection
therefore descends to the cokernels.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial

set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p r q l : ℕ}

/-- Euler evaluation at all four groups of an ambient two-slice configuration. -/
def ambientFiberEvaluation (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 2) d →ₗ[K] AmbientFiberValues a b z x :=
  (traceFiberEvaluation (ambientPointA a) d).prod
    ((traceFiberEvaluation (ambientPointB b) d).prod
      ((traceFiberEvaluation (ambientTracePoint z) d).prod (traceFiberEvaluation x d)))

/-- The second slice is embedded by prepending its zero normal coordinate. -/
theorem ambientPointB_eq (b : PointCoordinates K m r) (i : Fin r) :
    ambientPointB b i = Fin.cons 0 (chartPoint K b i) := by
  unfold ambientPointB
  congr 1
  exact Fin.cons_self_tail (chartPoint K b i)

private theorem sliceARepresentative_trace (z : Fin m → K) :
    TwoNormalTrace.sliceARepresentative K m (Fin.cons 0 z) = Fin.cons 0 (Fin.cons 0 z) := by
  simp [TwoNormalTrace.sliceARepresentative]

/-- Projecting ambient evaluation onto the first slice equals evaluating
the polynomial restriction of the section. -/
theorem ambientProjection_left_evaluation (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (F : HyperplaneEuler.Relations K (m + 2) d) :
    compatibleLeft z p r
      (ambientFiberProjection a b z x (ambientFiberEvaluation a b z x d F)) =
      fiberSliceEvaluation a z d (TwoNormalTrace.sliceARelation K m d F) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      funext i j
      change eval (ambientTracePoint z i) (F.val j.succ.succ).val =
        eval (z i) (hyperplaneRestrict K m
          ((TwoNormalTrace.sliceARelation K m d F).val j.succ).val)
      rw [eval_hyperplaneRestrict]
      have h := TwoNormalTrace.eval_sliceARelation K m F (Fin.cons 0 (z i)) j.succ
      simpa only [Fin.cases_succ, sliceARepresentative_trace, ambientTracePoint] using h.symm
    · funext i j
      change eval (ambientPointA a i) (F.val j.succ.succ).val =
        eval (chartPoint K a i) ((TwoNormalTrace.sliceARelation K m d F).val j.succ).val
      have h := TwoNormalTrace.eval_sliceARelation K m F (chartPoint K a i) j.succ
      simpa only [Fin.cases_succ, TwoNormalTrace.sliceARepresentative, ambientPointA] using h.symm
  · funext i
    change eval (ambientTracePoint z i) (F.val 0).val =
      eval (Fin.cons 0 (z i)) ((TwoNormalTrace.sliceARelation K m d F).val 0).val
    have h := TwoNormalTrace.eval_sliceARelation K m F (Fin.cons 0 (z i)) 0
    simpa only [Fin.cases_zero, sliceARepresentative_trace, ambientTracePoint] using h.symm

/-- The second projection also agrees with genuine polynomial restriction. -/
theorem ambientProjection_right_evaluation (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (F : HyperplaneEuler.Relations K (m + 2) d) :
    compatibleRight z p r
      (ambientFiberProjection a b z x (ambientFiberEvaluation a b z x d F)) =
      fiberSliceEvaluation b z d (TwoNormalTrace.sliceBRelation K m d F) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      funext i j
      change eval (ambientTracePoint z i) (F.val j.succ.succ).val =
        eval (z i) (hyperplaneRestrict K m
          ((TwoNormalTrace.sliceBRelation K m d F).val j.succ).val)
      rw [eval_hyperplaneRestrict]
      exact (TwoNormalTrace.eval_sliceBRelation K m F (Fin.cons 0 (z i)) j.succ).symm
    · funext i j
      change eval (ambientPointB b i) (F.val j.succ.succ).val =
        eval (chartPoint K b i) ((TwoNormalTrace.sliceBRelation K m d F).val j.succ).val
      rw [ambientPointB_eq]
      exact (TwoNormalTrace.eval_sliceBRelation K m F (chartPoint K b i) j.succ).symm
  · funext i
    change eval (ambientTracePoint z i) (F.val (0 : Fin (m + 1)).succ).val =
      eval (Fin.cons 0 (z i)) ((TwoNormalTrace.sliceBRelation K m d F).val 0).val
    exact (TwoNormalTrace.eval_sliceBRelation K m F (Fin.cons 0 (z i)) 0).symm

/-- Ambient section values give zero in both slice cokernels. -/
theorem ambientFiberCokernelClasses_evaluation (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (F : HyperplaneEuler.Relations K (m + 2) d) :
    ambientFiberCokernelClasses a b z x d (ambientFiberEvaluation a b z x d F) = 0 := by
  apply Prod.ext
  · change (fiberSliceEvaluation a z d).range.mkQ
      (compatibleLeft z p r (ambientFiberProjection a b z x
        (ambientFiberEvaluation a b z x d F))) = 0
    rw [ambientProjection_left_evaluation]
    change (Submodule.Quotient.mk (fiberSliceEvaluation a z d
      (TwoNormalTrace.sliceARelation K m d F)) : _ ⧸ (fiberSliceEvaluation a z d).range) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨TwoNormalTrace.sliceARelation K m d F, rfl⟩
  · change (fiberSliceEvaluation b z d).range.mkQ
      (compatibleRight z p r (ambientFiberProjection a b z x
        (ambientFiberEvaluation a b z x d F))) = 0
    rw [ambientProjection_right_evaluation]
    change (Submodule.Quotient.mk (fiberSliceEvaluation b z d
      (TwoNormalTrace.sliceBRelation K m d F)) : _ ⧸ (fiberSliceEvaluation b z d).range) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨TwoNormalTrace.sliceBRelation K m d F, rfl⟩

/-- The natural ambient-cokernel map to the two slice cokernels. -/
def ambientCokernelToSlices (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) (d : ℕ) :
    (AmbientFiberValues a b z x ⧸ (ambientFiberEvaluation a b z x d).range) →ₗ[K]
      ((((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) ⧸
          (fiberSliceEvaluation a z d).range) ×
        (((TraceFibers z × (Fin r → Fin m → K)) × (Fin q → K)) ⧸
          (fiberSliceEvaluation b z d).range)) :=
  (ambientFiberEvaluation a b z x d).range.liftQ
    (ambientFiberCokernelClasses a b z x d) (by
      rintro _ ⟨F, rfl⟩
      exact ambientFiberCokernelClasses_evaluation a b z x d F)

/-- Trace Euler surjectivity gives the surjection used in the two-normal
cokernel calculation of Proposition 4.5. -/
theorem ambientCokernelToSlices_surjective (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z d)) :
    Function.Surjective (ambientCokernelToSlices a b z x d) := by
  intro c
  obtain ⟨u, hu⟩ := ambientFiberCokernelClasses_surjective a b z x d hA hB htrace c
  exact ⟨Submodule.Quotient.mk u, hu⟩

end IdealGeneration.TwoNormalSlice
