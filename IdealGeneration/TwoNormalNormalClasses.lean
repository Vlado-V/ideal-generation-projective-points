module

public import IdealGeneration.TwoNormalAmbientCokernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normal values in the two slice quotient codes

A pure normal representative on the common trace retains its scalar
coordinate class under the ambient-to-slice cokernel maps.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m p r q l : ℕ}

/-- Insert the two normal scalar arrays into the Euler fibers on the trace. -/
def traceNormalValues (z : Fin q → Fin m → K) :
    ((Fin q → K) × (Fin q → K)) →ₗ[K] TraceFibers (ambientTracePoint z) where
  toFun u := ⟨fun i => Fin.cons (u.1 i) (Fin.cons (u.2 i) (fun _ => 0)), by
    funext i
    change (∑ j, ambientTracePoint z i j *
      (Fin.cons (α := fun _ => K) (u.1 i) (Fin.cons (u.2 i) (fun _ : Fin m => 0)) j)) = 0
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [ambientTracePoint, Fin.cons_zero, Fin.cons_succ,
      zero_mul, mul_zero, Finset.sum_const_zero, zero_add]⟩
  map_add' u v := by
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · change (0 : K) = 0 + 0
        simp
  map_smul' c u := by
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · change (0 : K) = c • (0 : K)
        simp

/-- Place those normal values on the trace and zero in the other groups. -/
def ambientNormalValues (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) :
    ((Fin q → K) × (Fin q → K)) →ₗ[K] AmbientFiberValues a b z x where
  toFun u := (0, (0, (traceNormalValues z u, 0)))
  map_add' u v := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · apply Prod.ext
        · exact (traceNormalValues z).map_add u v
        · simp
  map_smul' c u := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · apply Prod.ext
        · exact (traceNormalValues z).map_smul c u
        · simp

/-- The compatible slice projection separates the two normal scalar arrays. -/
theorem ambientFiberProjection_normalValues (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (u : (Fin q → K) × (Fin q → K)) :
    ambientFiberProjection a b z x (ambientNormalValues a b z x u) =
      (0, ((0, u.1), (0, u.2))) := by
  apply Prod.ext
  · apply Subtype.ext
    funext i j
    rfl
  · rfl

/-- Passing to ambient and slice cokernels preserves pure scalar representatives. -/
theorem ambientCokernelToSlices_normalClass (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (D : ℕ) (u : (Fin q → K) × (Fin q → K)) :
    ambientCokernelToSlices a b z x D
      (Submodule.Quotient.mk (ambientNormalValues a b z x u)) =
        (Submodule.Quotient.mk (0, u.1), Submodule.Quotient.mk (0, u.2)) := by
  change ambientFiberCokernelClasses a b z x D (ambientNormalValues a b z x u) = _
  rw [ambientFiberCokernelClasses, LinearMap.comp_apply, ambientFiberProjection_normalValues]
  rfl

/-- The scalar trace-code identification keeps the pure normal representative. -/
theorem sliceCokernelTraceProductEquiv_normalClass (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) (u : Fin q → K) :
    sliceCokernelTraceProductEquiv a z d hnormal htrace hscalar
      (Submodule.Quotient.mk (0, u)) = Submodule.Quotient.mk u := by
  let : AddCommGroup (HyperplaneEuler.Relations K (m + 1) (d + 1)) :=
    Module.addCommMonoidToAddCommGroup K
  have h := TwoNormalCokernelLinear.cokernelEquiv_scalarClass
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace.2 hscalar) u
  let E := TwoNormalCokernelLinear.cokernelEquiv_monoid
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace.2 hscalar)
  change E (Submodule.Quotient.mk (0, u)) = Submodule.Quotient.mk u at h
  let E₁ := Submodule.quotEquivOfEq _ _
    (normalTrace_tangentialKernel_range a z d hnormal htrace.1)
  let E₂ := Submodule.quotEquivOfEq _ _ (scalarNormalCode_range a z d)
  calc
    _ = E₂ (E₁ (E (Submodule.Quotient.mk (0, u)))) := rfl
    _ = E₂ (E₁ (Submodule.Quotient.mk u)) := congrArg (fun c => E₂ (E₁ c)) h
    _ = _ := rfl

/-- The natural ambient cokernel map into the two trace quotient codes. -/
def ambientCokernelTraceCodes (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a d))
    (hscalarB : Function.Surjective (pointEvaluation K b d)) :
    (AmbientFiberValues a b z x ⧸ (ambientFiberEvaluation a b z x (d + 1)).range) →ₗ[K]
      (((Fin q → K) ⧸ ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm a d)).range) ×
       ((Fin q → K) ⧸ ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm b d)).range)) :=
  ((sliceCokernelTraceProductEquiv a z d hA htrace hscalarA).toLinearMap.prodMap
    (sliceCokernelTraceProductEquiv b z d hB htrace hscalarB).toLinearMap).comp
      (ambientCokernelToSlices a b z x (d + 1))

/-- A normal-only array maps to its two scalar quotient classes. -/
theorem ambientCokernelTraceCodes_normalClass (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a d))
    (hscalarB : Function.Surjective (pointEvaluation K b d))
    (u : (Fin q → K) × (Fin q → K)) :
    ambientCokernelTraceCodes a b z x d hA hB htrace hscalarA hscalarB
      (Submodule.Quotient.mk (ambientNormalValues a b z x u)) =
        (Submodule.Quotient.mk u.1, Submodule.Quotient.mk u.2) := by
  rw [ambientCokernelTraceCodes, LinearMap.comp_apply, ambientCokernelToSlices_normalClass]
  apply Prod.ext
  · exact sliceCokernelTraceProductEquiv_normalClass a z d hA htrace hscalarA u.1
  · exact sliceCokernelTraceProductEquiv_normalClass b z d hB htrace hscalarB u.2

end IdealGeneration.TwoNormalSlice
