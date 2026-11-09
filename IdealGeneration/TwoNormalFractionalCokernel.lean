module

public import IdealGeneration.TwoNormalFractionalTrace
public import IdealGeneration.TwoNormalNormalClasses

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Trace quotient codes with a nonzero trace kernel

An extension of a trace kernel element vanishes at all attached slice
points. Subtracting that extension isolates the normal tuple without
altering any of the slice values.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial TwoNormalTrace TwoNormalSlice

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m p r q l : ℕ}

/-- The normal image of the tangential kernel is the scalar trace-product
code when every slice point projects to a common trace point. -/
theorem normalTrace_tangentialKernel_range_of_attached (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hattach : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0) :
    ((normalTraceEvaluation z (d + 1)).comp
      (tangentialSliceEvaluation a z (d + 1)).ker.subtype).range =
      (scalarNormalCode a z d).range := by
  ext y
  constructor
  · rintro ⟨F, rfl⟩
    let τ := HyperplaneEuler.trace K m (d + 1) F.val
    have ht : traceFiberEvaluation z (d + 1) τ = 0 :=
      congrArg Prod.fst F.property
    have hτ : relationEvaluation z (d + 1) τ = 0 :=
      congrArg Subtype.val ht
    let e := HyperplaneEuler.extend K m (d + 1) τ
    have he : sliceEvaluation a z (d + 1) e = 0 :=
      extendRelation_slice_vanishing a z hattach τ hτ
    have heT : residualTangentEvaluation a (d + 1) e = 0 := by
      funext i j
      exact congrFun (congrFun (congrArg Prod.fst he) i) j.succ
    have heN : normalTraceEvaluation z (d + 1) e = 0 := by
      funext i
      exact congrFun (congrFun (congrArg Prod.snd he) i) 0
    let w := F.val + (-1 : K) • e
    have hwT : HyperplaneEuler.trace K m (d + 1) w = 0 := by
      dsimp only [w, e]
      rw [map_add, map_smul, HyperplaneEuler.trace_extend]
      let : AddCommGroup (HyperplaneEuler.Relations K m (d + 1)) :=
        Module.addCommMonoidToAddCommGroup K
      change τ + (-1 : K) • τ = 0
      rw [neg_one_smul, add_neg_cancel]
    have hwA : residualTangentEvaluation a (d + 1) w = 0 := by
      have hA : residualTangentEvaluation a (d + 1) F.val = 0 :=
        congrArg Prod.snd F.property
      dsimp only [w]
      rw [map_add, map_smul, hA, heT, smul_zero, add_zero]
    have hwN : normalTraceEvaluation z (d + 1) w =
        normalTraceEvaluation z (d + 1) F.val := by
      dsimp only [w]
      rw [map_add, map_smul, heN, smul_zero, add_zero]
    obtain ⟨g, hg⟩ := HyperplaneEuler.exists_normal_of_trace_eq_zero K m d w hwT
    rw [← hg] at hwA
    have hgi (j : Fin m) : g j ∈ pointDegreePiece K a d := by
      rw [mem_pointDegreePiece]
      intro i
      have h := congrFun (congrFun hwA i) j
      change eval (chartPoint K a i) (X 0 * (g j).val) = 0 at h
      rw [map_mul, eval_X] at h
      exact (mul_eq_zero.mp h).resolve_left (hnormal i)
    refine ⟨fun j => -(⟨g j, hgi j⟩ : pointDegreePiece K a d), ?_⟩
    change scalarNormalCode a z d _ = normalTraceEvaluation z (d + 1) F.val
    rw [← hwN, ← hg, normalTrace_normalInjection]
    ext i
    simp [scalarNormalCode, Finset.sum_neg_distrib]
  · rintro ⟨w, rfl⟩
    let g : Fin m → Forms K (m + 1) d := fun j => -(w j).val
    let F := HyperplaneEuler.normalInjection K m d g
    have hF : F ∈ (tangentialSliceEvaluation a z (d + 1)).ker := by
      apply Prod.ext
      · change traceFiberEvaluation z (d + 1) (HyperplaneEuler.trace K m (d + 1) F) = 0
        dsimp [F]
        rw [HyperplaneEuler.trace_normalInjection, map_zero]
      · funext i j
        change eval (chartPoint K a i) (X 0 * -(w j).val.val) = 0
        rw [map_mul, map_neg, (mem_pointDegreePiece a (w j).val).mp (w j).property i,
          neg_zero, mul_zero]
    refine ⟨⟨F, hF⟩, ?_⟩
    change normalTraceEvaluation z (d + 1) F = scalarNormalCode a z d w
    dsimp [F]
    rw [normalTrace_normalInjection]
    ext i
    simp [g, scalarNormalCode, Finset.sum_neg_distrib]

/-- The attached slice cokernel is the normal scalar quotient on the trace. -/
def sliceCokernelTraceProductEquiv_of_attached (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hattach : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) :
    (((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) ⧸
      (fiberSliceEvaluation a z (d + 1)).range) ≃ₗ[K]
      (Fin q → K) ⧸
        ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm a d)).range :=
  ((TwoNormalCokernelLinear.cokernelEquiv_monoid
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace hscalar)).trans
      (Submodule.quotEquivOfEq _ _
        (normalTrace_tangentialKernel_range_of_attached a z d hattach hnormal))).trans
    (Submodule.quotEquivOfEq _ _ (scalarNormalCode_range a z d))

/-- The attached slice equivalence retains pure scalar representatives. -/
theorem sliceCokernelTraceProductEquiv_normalClass_of_attached (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hattach : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) (u : Fin q → K) :
    sliceCokernelTraceProductEquiv_of_attached a z d hattach hnormal htrace hscalar
      (Submodule.Quotient.mk (0, u)) = Submodule.Quotient.mk u := by
  let : AddCommGroup (HyperplaneEuler.Relations K (m + 1) (d + 1)) :=
    Module.addCommMonoidToAddCommGroup K
  have h := TwoNormalCokernelLinear.cokernelEquiv_scalarClass
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace hscalar) u
  let E := TwoNormalCokernelLinear.cokernelEquiv_monoid
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace hscalar)
  change E (Submodule.Quotient.mk (0, u)) = Submodule.Quotient.mk u at h
  let E₁ := Submodule.quotEquivOfEq _ _
    (normalTrace_tangentialKernel_range_of_attached a z d hattach hnormal)
  let E₂ := Submodule.quotEquivOfEq _ _ (scalarNormalCode_range a z d)
  calc
    _ = E₂ (E₁ (E (Submodule.Quotient.mk (0, u)))) := rfl
    _ = E₂ (E₁ (Submodule.Quotient.mk u)) := congrArg (fun c => E₂ (E₁ c)) h
    _ = _ := rfl

/-- The ambient cokernel map to the two attached trace quotient codes. -/
def ambientCokernelTraceCodes_of_attached (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hattachA : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hattachB : ∀ i : Fin r, ∃ j : Fin q, (fun k => chartPoint K b i k.succ) = z j)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a d))
    (hscalarB : Function.Surjective (pointEvaluation K b d)) :
    (AmbientFiberValues a b z x ⧸ (ambientFiberEvaluation a b z x (d + 1)).range) →ₗ[K]
      (((Fin q → K) ⧸ ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm a d)).range) ×
       ((Fin q → K) ⧸ ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm b d)).range)) :=
  ((sliceCokernelTraceProductEquiv_of_attached a z d hattachA hA htrace hscalarA).toLinearMap.prodMap
    (sliceCokernelTraceProductEquiv_of_attached b z d hattachB hB htrace hscalarB).toLinearMap).comp
      (ambientCokernelToSlices a b z x (d + 1))

/-- The ambient cokernel map onto the two attached trace codes is onto. -/
theorem ambientCokernelTraceCodes_surjective_of_attached (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hattachA : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hattachB : ∀ i : Fin r, ∃ j : Fin q, (fun k => chartPoint K b i k.succ) = z j)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a d))
    (hscalarB : Function.Surjective (pointEvaluation K b d)) :
    Function.Surjective
      (ambientCokernelTraceCodes_of_attached a b z x d hattachA hattachB
        hA hB htrace hscalarA hscalarB) :=
  ((sliceCokernelTraceProductEquiv_of_attached a z d hattachA hA htrace hscalarA).prodCongr
    (sliceCokernelTraceProductEquiv_of_attached b z d hattachB hB htrace hscalarB)).surjective.comp
      (ambientCokernelToSlices_surjective a b z x (d + 1) hA hB htrace)

/-- The ambient map preserves the two pure normal coordinate classes. -/
theorem ambientCokernelTraceCodes_normalClass_of_attached (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hattachA : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hattachB : ∀ i : Fin r, ∃ j : Fin q, (fun k => chartPoint K b i k.succ) = z j)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a d))
    (hscalarB : Function.Surjective (pointEvaluation K b d))
    (u : (Fin q → K) × (Fin q → K)) :
    ambientCokernelTraceCodes_of_attached a b z x d hattachA hattachB hA hB htrace hscalarA hscalarB
      (Submodule.Quotient.mk (ambientNormalValues a b z x u)) =
        (Submodule.Quotient.mk u.1, Submodule.Quotient.mk u.2) := by
  rw [ambientCokernelTraceCodes_of_attached, LinearMap.comp_apply, ambientCokernelToSlices_normalClass]
  apply Prod.ext
  · exact sliceCokernelTraceProductEquiv_normalClass_of_attached a z d hattachA hA htrace hscalarA u.1
  · exact sliceCokernelTraceProductEquiv_normalClass_of_attached b z d hattachB hB htrace hscalarB u.2

end IdealGeneration.TwoNormalFractional
