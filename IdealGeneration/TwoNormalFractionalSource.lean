module

public import IdealGeneration.TwoNormalDivision
public import IdealGeneration.TwoNormalEuler
public import IdealGeneration.TwoNormalSource

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The larger coefficient space for a fractional trace

After deleting the free off-slice point, the tangential coefficients are
allowed to belong to the larger point ideal. The two slice products on that
space are injective. Their scalar evaluations give the coefficient elimination
in the free-projection argument of Proposition 5.1.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoNormalTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ) {d : ℕ}

/-- Tangential multiplication of coefficients in a fixed homogeneous space. -/
def tangentOn (G : Submodule K (Forms K (m + 2) d)) :
    (Fin m → G) →ₗ[K] Forms K (m + 2) (d + 1) :=
  (tangentProduct K m d).comp (LinearMap.pi fun i => G.subtype.comp (LinearMap.proj i))

/-- Add one normal multiple before restricting to a slice. -/
def sliceProductOf (G : Submodule K (Forms K (m + 2) d))
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1)) :
    ((Fin m → G) × G) →ₗ[K] Forms K (m + 1) (d + 1) :=
  R.comp ((tangentOn K m G).coprod (M.comp G.subtype))

@[simp] theorem sliceProductOf_apply (G : Submodule K (Forms K (m + 2) d))
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1))
    (v : (Fin m → G) × G) :
    sliceProductOf K m G R M v = R
      (tangentProduct K m d (fun i => (v.1 i).val) + M v.2.val) := rfl

/-- The product space on `t=0`, with the extra coefficient multiplied by `s`. -/
def sliceAProduct (G : Submodule K (Forms K (m + 2) d)) :
    ((Fin m → G) × G) →ₗ[K] Forms K (m + 1) (d + 1) :=
  sliceProductOf K m G (restrictAForm K m (d + 1)) (normalFormMul K (m + 1) d)

/-- The product space on `s=0`, with the extra coefficient multiplied by `t`. -/
def sliceBProduct (G : Submodule K (Forms K (m + 2) d)) :
    ((Fin m → G) × G) →ₗ[K] Forms K (m + 1) (d + 1) :=
  sliceProductOf K m G (restrictForm K (m + 1) (d + 1)) (secondNormalMul K m d)

/-- Restriction from the first slice to the common trace. -/
theorem restrictForm_restrictAForm {e : ℕ} (f : Forms K (m + 2) e) :
    restrictForm K m e (restrictAForm K m e f) = restrictTraceForm K m e f :=
  Subtype.ext (restrictA_trace K m f.val)

private theorem sliceProductOf_injective (G : Submodule K (Forms K (m + 2) d))
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1))
    (hR : ∀ f, restrictForm K m (d + 1) (R f) = restrictTraceForm K m (d + 1) f)
    (hM : ∀ g, restrictTraceForm K m (d + 1) (M g) = 0)
    (hproduct : Function.Injective (traceProduct K m d G))
    (hzero : ∀ g : G, R (M g.val) = 0 → g = 0) :
    Function.Injective (sliceProductOf K m G R M) := by
  have hk : ∀ v, sliceProductOf K m G R M v = 0 → v = 0 := by
    intro v hv
    have ht := congrArg (restrictForm K m (d + 1)) hv
    rw [sliceProductOf_apply, map_zero, hR, map_add, hM, add_zero] at ht
    have hfirst : v.1 = 0 := hproduct (by
      rw [map_zero]
      exact ht)
    have hsecond : v.2 = 0 := hzero _ (by
      rw [sliceProductOf_apply, hfirst] at hv
      change R (tangentProduct K m d 0 + M v.2.val) = 0 at hv
      rw [map_zero, zero_add] at hv
      exact hv)
    exact Prod.ext hfirst hsecond
  intro a b hab
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, sub_eq_zero]
  exact hab

/-- The larger product space has no relations on the first slice. -/
theorem sliceAProduct_injective (G : Submodule K (Forms K (m + 2) d))
    (htrace : Function.Injective ((restrictTraceForm K m d).comp G.subtype))
    (hproduct : Function.Injective (traceProduct K m d G)) :
    Function.Injective (sliceAProduct K m G) := by
  refine sliceProductOf_injective K m G _ _ (restrictForm_restrictAForm K m) ?_ hproduct ?_
  · intro f
    apply Subtype.ext
    change restrictTrace K m (X 0 * f.val) = 0
    simp
  · intro g hg
    have h : X (0 : Fin (m + 1)) * restrictA K m g.val.val = 0 := by
      have h' := congrArg Subtype.val hg
      change restrictA K m (X 0 * g.val.val) = 0 at h'
      simpa only [map_mul, restrictA_s] using h'
    have hr := (mul_eq_zero.mp h).resolve_left (X_ne_zero _)
    apply htrace
    rw [map_zero]
    apply Subtype.ext
    change restrictTrace K m g.val.val = 0
    rw [← restrictA_trace, hr, map_zero]

/-- The larger product space has no relations on the second slice. -/
theorem sliceBProduct_injective (G : Submodule K (Forms K (m + 2) d))
    (htrace : Function.Injective ((restrictTraceForm K m d).comp G.subtype))
    (hproduct : Function.Injective (traceProduct K m d G)) :
    Function.Injective (sliceBProduct K m G) := by
  refine sliceProductOf_injective K m G _ _ (fun _ => rfl) ?_ hproduct ?_
  · intro f
    apply Subtype.ext
    change restrictTrace K m (X (0 : Fin (m + 1)).succ * f.val) = 0
    rw [map_mul, restrictTrace_t, zero_mul]
  · intro g hg
    have h : X (0 : Fin (m + 1)) * hyperplaneRestrict K (m + 1) g.val.val = 0 := by
      have h' := congrArg Subtype.val hg
      change hyperplaneRestrict K (m + 1) (X (0 : Fin (m + 1)).succ * g.val.val) = 0 at h'
      simpa only [map_mul, hyperplaneRestrict_X_succ] using h'
    have hr := (mul_eq_zero.mp h).resolve_left (X_ne_zero _)
    apply htrace
    rw [map_zero]
    apply Subtype.ext
    change hyperplaneRestrict K m (hyperplaneRestrict K (m + 1) g.val.val) = 0
    rw [hr, map_zero]

variable {K m} {p r q : ℕ}

/-- The residual coefficients vanish if the first normal trace vanishes.
The conditions concern scalar interpolation on the enlarged coefficient space
and on degree-`d` forms on the opposite slice. -/
theorem residual_eq_zero_of_first_normal_trace
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q)
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1))
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (hbEval : Function.Injective (pointEvaluation K b d))
    (hcoeff : ∀ j, w.1 j ∈ pointDegreePiece K x d)
    (hh : w.2 ∈ pointDegreePiece K x (d + 1))
    (hA : pointEvaluation K a (d + 1) (restrictAForm K m (d + 1)
      (w.2 + tangentProduct K m d w.1)) = 0)
    (hB : pointEvaluation K b (d + 1) (restrictForm K (m + 1) (d + 1) w.2) = 0)
    (hlarge : Function.Injective ((pointEvaluation K a (d + 1)).comp
      (sliceAProduct K m (pointDegreePiece K x d))))
    (hzero : restrictTraceForm K m (d + 1) w.2 = 0) : w = 0 := by
  have hB0 : restrictForm K (m + 1) (d + 1) w.2 = 0 :=
    TwoNormalIntegral.sliceForm_eq_zero_of_trace_and_values b hb hbEval _ hzero hB
  obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K (m + 1) w.2).mp hB0
  have hgG : g ∈ pointDegreePiece K x d := by
    apply (mem_pointDegreePiece x g).mpr
    intro i
    have hi := (mem_pointDegreePiece x w.2).mp hh i
    rw [hg, map_mul, eval_X] at hi
    exact (mul_eq_zero.mp hi).resolve_left (hs i)
  let v : (Fin m → pointDegreePiece K x d) × pointDegreePiece K x d :=
    (fun j => ⟨w.1 j, hcoeff j⟩, ⟨g, hgG⟩)
  have hn : normalFormMul K (m + 1) d g = w.2 := Subtype.ext hg.symm
  have hvEval : ((pointEvaluation K a (d + 1)).comp
      (sliceAProduct K m (pointDegreePiece K x d))) v = 0 := by
    change pointEvaluation K a (d + 1) (sliceProductOf K m (pointDegreePiece K x d)
      (restrictAForm K m (d + 1)) (normalFormMul K (m + 1) d) v) = 0
    rw [sliceProductOf_apply]
    change pointEvaluation K a (d + 1) (restrictAForm K m (d + 1)
      (tangentProduct K m d w.1 + normalFormMul K (m + 1) d g)) = 0
    rw [hn, show tangentProduct K m d w.1 + w.2 = w.2 + tangentProduct K m d w.1 by abel]
    exact hA
  have hv : v = 0 := hlarge (by simpa using hvEval)
  have h1 : w.1 = 0 := by
    funext j
    exact congrArg (fun u : (Fin m → pointDegreePiece K x d) × pointDegreePiece K x d =>
      (u.1 j).val) hv
  have hg0 : g = 0 := congrArg (fun u : (Fin m → pointDegreePiece K x d) ×
    pointDegreePiece K x d => u.2.val) hv
  exact Prod.ext h1 (by rw [← hn, hg0, map_zero]; rfl)

/-- The analogous elimination uses the other slice and other normal trace. -/
theorem residual_eq_zero_of_second_normal_trace
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q)
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1))
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (haEval : Function.Injective (pointEvaluation K a d))
    (hcoeff : ∀ j, w.1 j ∈ pointDegreePiece K x d)
    (hh : w.2 ∈ pointDegreePiece K x (d + 1))
    (hA : pointEvaluation K a (d + 1) (restrictAForm K m (d + 1)
      (w.2 + tangentProduct K m d w.1)) = 0)
    (hB : pointEvaluation K b (d + 1) (restrictForm K (m + 1) (d + 1) w.2) = 0)
    (hlarge : Function.Injective ((pointEvaluation K b (d + 1)).comp
      (sliceBProduct K m (pointDegreePiece K x d))))
    (hzero : restrictTraceForm K m (d + 1) (-w.2 - tangentProduct K m d w.1) = 0) :
    w = 0 := by
  let k := -w.2 - tangentProduct K m d w.1
  have hk : k ∈ pointDegreePiece K x (d + 1) := by
    apply (mem_pointDegreePiece x k).mpr
    intro i
    have hi := (mem_pointDegreePiece x w.2).mp hh i
    have hj (j : Fin m) := (mem_pointDegreePiece x (w.1 j)).mp (hcoeff j) i
    change eval (chartPoint K x i) (-w.2.val - ∑ j : Fin m, X j.succ.succ * (w.1 j).val) = 0
    simp [hi, hj]
  have hAk : pointEvaluation K a (d + 1) (restrictAForm K m (d + 1) k) = 0 := by
    have he : k = -(w.2 + tangentProduct K m d w.1) := by dsimp [k]; abel
    rw [he, map_neg, map_neg, hA, neg_zero]
  have htraceA : restrictForm K m (d + 1) (restrictAForm K m (d + 1) k) = 0 := by
    rw [restrictForm_restrictAForm]
    exact hzero
  have hA0 := TwoNormalIntegral.sliceForm_eq_zero_of_trace_and_values a ha haEval _ htraceA hAk
  obtain ⟨g, hg⟩ := (restrictA_eq_zero_iff K m k).mp (congrArg Subtype.val hA0)
  have hgG : g ∈ pointDegreePiece K x d := by
    apply (mem_pointDegreePiece x g).mpr
    intro i
    have hi := (mem_pointDegreePiece x k).mp hk i
    rw [hg, map_mul, eval_X] at hi
    exact (mul_eq_zero.mp hi).resolve_left (ht i)
  let v : (Fin m → pointDegreePiece K x d) × pointDegreePiece K x d :=
    (fun j => ⟨w.1 j, hcoeff j⟩, ⟨g, hgG⟩)
  have hn : secondNormalMul K m d g = k := Subtype.ext hg.symm
  have hvEval : ((pointEvaluation K b (d + 1)).comp
      (sliceBProduct K m (pointDegreePiece K x d))) v = 0 := by
    change pointEvaluation K b (d + 1) (sliceProductOf K m (pointDegreePiece K x d)
      (restrictForm K (m + 1) (d + 1)) (secondNormalMul K m d) v) = 0
    rw [sliceProductOf_apply]
    change pointEvaluation K b (d + 1) (restrictForm K (m + 1) (d + 1)
      (tangentProduct K m d w.1 + secondNormalMul K m d g)) = 0
    rw [hn, show tangentProduct K m d w.1 + k = -w.2 by dsimp [k]; abel,
      map_neg, map_neg, hB, neg_zero]
  have hv : v = 0 := hlarge (by simpa using hvEval)
  have h1 : w.1 = 0 := by
    funext j
    exact congrArg (fun u : (Fin m → pointDegreePiece K x d) × pointDegreePiece K x d =>
      (u.1 j).val) hv
  have hg0 : g = 0 := congrArg (fun u : (Fin m → pointDegreePiece K x d) ×
    pointDegreePiece K x d => u.2.val) hv
  have hk0 : k = 0 := by rw [← hn, hg0, map_zero]
  have h2 : w.2 = 0 := by
    change -w.2 - tangentProduct K m d w.1 = 0 at hk0
    simpa [h1] using hk0
  exact Prod.ext h1 h2

end IdealGeneration.TwoNormalFractional
