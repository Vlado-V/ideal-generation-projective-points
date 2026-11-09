module

public import IdealGeneration.TwoNormalSlice
public import IdealGeneration.TwoNormalCokernelLinear

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The scalar quotient left by slice Euler interpolation

The condition space uses the Euler fibers. At residual points, the nonzero
normal coordinate determines the normal component from the tangential ones.
At trace points, the tangential Euler fiber and the normal scalar are kept
separately.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial Module

set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p q : ℕ}

/-- The Euler contraction in the tangent coordinates at the trace points. -/
def traceFiberDot (z : Fin q → Fin m → K) :
    (Fin q → Fin m → K) →ₗ[K] (Fin q → K) where
  toFun u i := ∑ j, z i j * u i j
  map_add' u v := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The tangential Euler fiber at all trace points. -/
abbrev TraceFibers (z : Fin q → Fin m → K) := (traceFiberDot z).ker

/-- Trace Euler evaluation takes values in the genuine tangent fibers. -/
def traceFiberEvaluation (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K m d →ₗ[K] TraceFibers z :=
  (relationEvaluation z d).codRestrict _ (by
    intro F
    funext i
    have hF : (∑ j, X j * (F.val j).val) = 0 := congrArg Subtype.val F.property
    have h := congrArg (eval (z i)) hF
    change (∑ j, z i j * eval (z i) (F.val j).val) = 0
    simpa only [map_sum, map_mul, eval_X, map_zero] using h)

@[simp] theorem traceFiberEvaluation_val (z : Fin q → Fin m → K) {d : ℕ}
    (F : HyperplaneEuler.Relations K m d) :
    (traceFiberEvaluation z d F).val = relationEvaluation z d F := rfl

/-- The residual-point part is represented by its tangential coordinates. -/
def residualTangentEvaluation (a : PointCoordinates K m p) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 1) d →ₗ[K] (Fin p → Fin m → K) where
  toFun F i j := eval (chartPoint K a i) (F.val j.succ).val
  map_add' F G := by ext i j; simp
  map_smul' c F := by ext i j; simp

/-- Normal components at the trace points are unconstrained scalar values. -/
def normalTraceEvaluation (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 1) d →ₗ[K] (Fin q → K) where
  toFun F i := eval (Fin.cons 0 (z i)) (F.val 0).val
  map_add' F G := by ext i; simp
  map_smul' c F := by ext i; simp

/-- All conditions except the scalar normal values on the trace. -/
def tangentialSliceEvaluation (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 1) d →ₗ[K]
      (TraceFibers z × (Fin p → Fin m → K)) :=
  ((traceFiberEvaluation z d).comp (HyperplaneEuler.trace K m d)).prod
    (residualTangentEvaluation a d)

/-- Slice evaluation in independent coordinates on its Euler fibers. -/
def fiberSliceEvaluation (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 1) d →ₗ[K]
      ((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) :=
  (tangentialSliceEvaluation a z d).prod (normalTraceEvaluation z d)

/-- Trace Euler interpolation and scalar interpolation at the residual
points solve every condition except the trace normal scalar values. -/
theorem tangentialSliceEvaluation_surjective (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (tangentialSliceEvaluation a z (d + 1)) := by
  rintro ⟨t, v⟩
  obtain ⟨τ, hτ⟩ := htrace t
  let eτ := HyperplaneEuler.extend K m (d + 1) τ
  choose g hg using fun j : Fin m => hscalar
    (fun i => (v i j - eval (chartPoint K a i) (eτ.val j.succ).val) /
      chartPoint K a i 0)
  refine ⟨eτ + HyperplaneEuler.normalInjection K m d g, ?_⟩
  apply Prod.ext
  · change traceFiberEvaluation z (d + 1)
      (HyperplaneEuler.trace K m (d + 1) (eτ +
        HyperplaneEuler.normalInjection K m d g)) = t
    rw [map_add, HyperplaneEuler.trace_normalInjection, add_zero]
    change traceFiberEvaluation z (d + 1)
      (HyperplaneEuler.trace K m (d + 1) (HyperplaneEuler.extend K m (d + 1) τ)) = t
    rw [HyperplaneEuler.trace_extend]
    exact hτ
  · funext i j
    change eval (chartPoint K a i)
      ((eτ.val j.succ).val + X 0 * (g j).val) = v i j
    rw [map_add, map_mul, eval_X]
    have hgi := congrFun (hg j) i
    change eval (chartPoint K a i) (g j).val = _ at hgi
    rw [hgi]
    field_simp [hnormal i]
    ring

/-- Scalar normal values arising from residual point-ideal tuples. -/
def scalarNormalCode (a : PointCoordinates K m p) (z : Fin q → Fin m → K)
    (d : ℕ) : (Fin m → pointDegreePiece K a d) →ₗ[K] (Fin q → K) where
  toFun w i := ∑ j, z i j * eval (Fin.cons 0 (z i)) (w j).val.val
  map_add' u v := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.smul_eval, smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The normal values of a normal Euler tuple have the expected minus sign. -/
theorem normalTrace_normalInjection (z : Fin q → Fin m → K) (d : ℕ)
    (g : Fin m → Forms K (m + 1) d) :
    normalTraceEvaluation z (d + 1) (HyperplaneEuler.normalInjection K m d g) =
      fun i => -(∑ j, z i j * eval (Fin.cons 0 (z i)) (g j).val) := by
  ext i
  simp [normalTraceEvaluation, HyperplaneEuler.normalInjection_zero,
    HyperplaneEuler.tangentProduct]

/-- The scalar normal image of the remaining kernel is precisely the
trace-product code of the residual ideal. -/
theorem normalTrace_tangentialKernel_range (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Injective (traceFiberEvaluation z (d + 1))) :
    ((normalTraceEvaluation z (d + 1)).comp
      (tangentialSliceEvaluation a z (d + 1)).ker.subtype).range =
      (scalarNormalCode a z d).range := by
  ext y
  constructor
  · rintro ⟨F, rfl⟩
    have ht : traceFiberEvaluation z (d + 1)
        (HyperplaneEuler.trace K m (d + 1) F.val) = 0 :=
      congrArg Prod.fst F.property
    have hτ : HyperplaneEuler.trace K m (d + 1) F.val = 0 :=
      htrace (by simpa using ht)
    obtain ⟨g, hg⟩ :=
      HyperplaneEuler.exists_normal_of_trace_eq_zero K m d F.val hτ
    have hA : residualTangentEvaluation a (d + 1) F.val = 0 :=
      congrArg Prod.snd F.property
    rw [← hg] at hA
    have hgi (j : Fin m) : g j ∈ pointDegreePiece K a d := by
      rw [mem_pointDegreePiece]
      intro i
      have h := congrFun (congrFun hA i) j
      change eval (chartPoint K a i) (X 0 * (g j).val) = 0 at h
      rw [map_mul, eval_X] at h
      exact (mul_eq_zero.mp h).resolve_left (hnormal i)
    refine ⟨fun j => -(⟨g j, hgi j⟩ : pointDegreePiece K a d), ?_⟩
    change scalarNormalCode a z d _ = normalTraceEvaluation z (d + 1) F.val
    rw [← hg, normalTrace_normalInjection]
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

/-- The slice cokernel is the scalar quotient code on the trace. -/
def sliceCokernelEquiv (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) :
    (((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) ⧸
      (fiberSliceEvaluation a z (d + 1)).range) ≃ₗ[K]
      (Fin q → K) ⧸ (scalarNormalCode a z d).range :=
  (TwoNormalCokernelLinear.cokernelEquiv_monoid
    (tangentialSliceEvaluation a z (d + 1)) (normalTraceEvaluation z (d + 1))
    (tangentialSliceEvaluation_surjective a z d hnormal htrace.2 hscalar)).trans
      (Submodule.quotEquivOfEq _ _
        (normalTrace_tangentialKernel_range a z d hnormal htrace.1))

/-- The code is exactly evaluation of the homogeneous trace-product space
used in the attached-projection construction. -/
theorem scalarNormalCode_range (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ) :
    (scalarNormalCode a z d).range =
      ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm a d)).range := by
  have hval (w : Fin m → pointDegreePiece K a d) :
      scalarNormalCode a z d w = scalarEvaluation z (d + 1)
        (tangentPointProductForm a d
          (fun j => pointPolynomialPieceEquiv a d (w j))) := by
    ext i
    simp [scalarNormalCode, scalarEvaluation, tangentPointProductForm,
      tangentPointProduct, eval_hyperplaneRestrict]
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨fun j => pointPolynomialPieceEquiv a d (w j), (hval w).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨fun j => (pointPolynomialPieceEquiv a d).symm (w j), ?_⟩
    rw [hval]
    simp only [LinearEquiv.apply_symm_apply]
    rfl

/-- The quotient-code form of the integral trace slice cokernel. -/
def sliceCokernelTraceProductEquiv (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1)))
    (hscalar : Function.Surjective (pointEvaluation K a d)) :
    (((TraceFibers z × (Fin p → Fin m → K)) × (Fin q → K)) ⧸
      (fiberSliceEvaluation a z (d + 1)).range) ≃ₗ[K]
      (Fin q → K) ⧸
        ((scalarEvaluation z (d + 1)).comp (tangentPointProductForm a d)).range :=
  (sliceCokernelEquiv a z d hnormal htrace hscalar).trans
    (Submodule.quotEquivOfEq _ _ (scalarNormalCode_range a z d))

end IdealGeneration.TwoNormalSlice
