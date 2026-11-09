module

public import IdealGeneration.TwoNormalSliceCokernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Compatible slice values and their cokernel classes

The two slices share the tangential trace fiber. A trace Euler section can
adjust one representative without changing its cokernel class, so any pair
of slice cokernel classes has compatible representatives.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial Module

set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p r q : ℕ}

/-- Values in two slice targets with one shared tangential trace fiber. -/
abbrev CompatibleSliceValues (z : Fin q → Fin m → K) (p r : ℕ) :=
  TraceFibers z ×
    (((Fin p → Fin m → K) × (Fin q → K)) ×
      ((Fin r → Fin m → K) × (Fin q → K)))

/-- The first slice target obtained from compatible values. -/
def compatibleLeft (z : Fin q → Fin m → K) (p r : ℕ) :
    CompatibleSliceValues z p r →ₗ[K]
      ((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) where
  toFun c := ((c.1, c.2.1.1), c.2.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The second slice target obtained from compatible values. -/
def compatibleRight (z : Fin q → Fin m → K) (p r : ℕ) :
    CompatibleSliceValues z p r →ₗ[K]
      ((TraceFibers z × (Fin r → Fin m → K)) × (Fin q → K)) where
  toFun c := ((c.1, c.2.2.1), c.2.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compatible fiber values define a pair of actual slice cokernel classes. -/
def compatibleCokernelClasses (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K) (d : ℕ) :
    CompatibleSliceValues z p r →ₗ[K]
      ((((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) ⧸
          (fiberSliceEvaluation a z d).range) ×
        (((TraceFibers z × (Fin r → Fin m → K)) × (Fin q → K)) ⧸
          (fiberSliceEvaluation b z d).range)) :=
  ((fiberSliceEvaluation a z d).range.mkQ.comp (compatibleLeft z p r)).prod
    ((fiberSliceEvaluation b z d).range.mkQ.comp (compatibleRight z p r))

/-- Trace Euler surjectivity makes every pair of slice cokernel classes
representable by compatible fiber values. -/
theorem compatibleCokernelClasses_surjective (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K) (d : ℕ)
    (htrace : Function.Surjective (traceFiberEvaluation z d)) :
    Function.Surjective (compatibleCokernelClasses a b z d) := by
  rintro ⟨cA, cB⟩
  obtain ⟨uA, huA⟩ := (fiberSliceEvaluation a z d).range.mkQ_surjective cA
  obtain ⟨uB, huB⟩ := (fiberSliceEvaluation b z d).range.mkQ_surjective cB
  obtain ⟨τ, hτ⟩ := htrace (uA.1.1 - uB.1.1)
  let F := HyperplaneEuler.extend K m d τ
  let vB := uB + fiberSliceEvaluation b z d F
  have htF : (fiberSliceEvaluation b z d F).1.1 = uA.1.1 - uB.1.1 := by
    change traceFiberEvaluation z d
      (HyperplaneEuler.trace K m d (HyperplaneEuler.extend K m d τ)) = _
    rw [HyperplaneEuler.trace_extend]
    exact hτ
  have htB : vB.1.1 = uA.1.1 := by
    change uB.1.1 + (fiberSliceEvaluation b z d F).1.1 = uA.1.1
    rw [htF]
    abel
  have hclassB : (fiberSliceEvaluation b z d).range.mkQ vB =
      (fiberSliceEvaluation b z d).range.mkQ uB := by
    change (fiberSliceEvaluation b z d).range.mkQ
      (uB + fiberSliceEvaluation b z d F) = _
    rw [map_add]
    have hzero : (fiberSliceEvaluation b z d).range.mkQ
        (fiberSliceEvaluation b z d F) = 0 := by
      change (Submodule.Quotient.mk (fiberSliceEvaluation b z d F) :
        _ ⧸ (fiberSliceEvaluation b z d).range) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨F, rfl⟩
    rw [hzero, add_zero]
  let c : CompatibleSliceValues z p r :=
    (uA.1.1, ((uA.1.2, uA.2), (vB.1.2, vB.2)))
  refine ⟨c, ?_⟩
  apply Prod.ext
  · change (fiberSliceEvaluation a z d).range.mkQ uA = cA
    exact huA
  · have hright : compatibleRight z p r c = vB := by
      apply Prod.ext
      · apply Prod.ext
        · exact htB.symm
        · rfl
      · rfl
    change (fiberSliceEvaluation b z d).range.mkQ (compatibleRight z p r c) = cB
    rw [hright, hclassB, huB]

end IdealGeneration.TwoNormalSlice
