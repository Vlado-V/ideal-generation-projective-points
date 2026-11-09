module

public import IdealGeneration.TwoNormalFractionalFreePoint
public import IdealGeneration.TwoNormalAmbientKernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normal form of the fractional ambient kernel

Each slice section is a common trace kernel extension. Subtracting its
two-normal extension leaves the exact residual polynomial form. This
works before surjectivity on the off-slice points is used.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d p r q k : ℕ}

private theorem restrictA_extendTrace (K : Type*) [Field K] (m : ℕ) (f : Poly K m) :
    restrictA K m (hyperplaneExtend K (m + 1) (hyperplaneExtend K m f)) =
      hyperplaneExtend K m f := by
  have h : (restrictA K m).comp ((hyperplaneExtend K (m + 1)).comp
      (hyperplaneExtend K m)) = hyperplaneExtend K m := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, hyperplaneExtend_X, restrictA_y]
  exact DFunLike.congr_fun h f

/-- Restricting the double extension on the first slice keeps the trace extension. -/
@[simp] theorem sliceA_extendTraceRelation (D : ℕ) (τ : HyperplaneEuler.Relations K m D) :
    sliceARelation K m D (extendTraceRelation K m D τ) = HyperplaneEuler.extend K m D τ := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [sliceARelation_zero_val]
    change restrictA K m (0 : Poly K (m + 2)) = 0
    exact map_zero _
  · simp only [sliceARelation_succ_val]
    change restrictA K m (hyperplaneExtend K (m + 1)
      (hyperplaneExtend K m (τ.val i).val)) = hyperplaneExtend K m (τ.val i).val
    exact restrictA_extendTrace K m _

/-- Restricting the double extension on the second slice keeps the trace extension. -/
@[simp] theorem sliceB_extendTraceRelation (D : ℕ) (τ : HyperplaneEuler.Relations K m D) :
    sliceBRelation K m D (extendTraceRelation K m D τ) = HyperplaneEuler.extend K m D τ :=
  HyperplaneEuler.trace_extend K (m + 1) D _

/-- The common tangential trace restriction of an ambient Euler relation. -/
def ambientTraceRelation (K : Type*) [Field K] (m D : ℕ) :
    HyperplaneEuler.Relations K (m + 2) D →ₗ[K] HyperplaneEuler.Relations K m D :=
  (HyperplaneEuler.trace K m D).comp (sliceBRelation K m D)

@[simp] theorem ambientTraceRelation_extend (D : ℕ) (τ : HyperplaneEuler.Relations K m D) :
    ambientTraceRelation K m D (extendTraceRelation K m D τ) = τ := by
  change HyperplaneEuler.trace K m D
    (sliceBRelation K m D (extendTraceRelation K m D τ)) = τ
  rw [sliceB_extendTraceRelation, HyperplaneEuler.trace_extend]

/-- Ambient vanishing gives slice vanishing, whether or not the slice has a kernel. -/
theorem slice_evaluations_zero_of_ambient_eq_zero {D : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (f : HyperplaneEuler.Relations K (m + 2) D)
    (hf : ambientEvaluation K m a b x z D f = 0) :
    sliceEvaluation a z D (sliceARelation K m D f) = 0 ∧
      sliceEvaluation b z D (sliceBRelation K m D f) = 0 := by
  have hAeval (i : Fin p) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.1.1) hf) i) j
  have hBeval (i : Fin r) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.1.2) hf) i) j
  have hZeval (i : Fin k) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.2.2) hf) i) j
  constructor <;> apply Prod.ext
  · funext i j
    change eval (chartPoint K a i) ((sliceARelation K m D f).val j).val = 0
    rw [eval_sliceARelation]
    exact hAeval i _
  · funext i j
    change eval (Fin.cons 0 (z i)) ((sliceARelation K m D f).val j).val = 0
    rw [eval_sliceARelation]
    exact hZeval i _
  · funext i j
    change eval (chartPoint K b i) ((sliceBRelation K m D f).val j).val = 0
    rw [eval_sliceBRelation]
    exact hBeval i _
  · funext i j
    change eval (Fin.cons 0 (z i)) ((sliceBRelation K m D f).val j).val = 0
    rw [eval_sliceBRelation]
    exact hZeval i _

/-- The fixed slice data used to reduce ambient vanishing to the trace kernel. -/
structure SliceConditions (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin k → Fin m → K) (d : ℕ) : Prop where
  attachedA : ∀ i : Fin p, ∃ j : Fin k, (fun l => chartPoint K a i l.succ) = z j
  attachedB : ∀ i : Fin r, ∃ j : Fin k, (fun l => chartPoint K b i l.succ) = z j
  normalA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0
  normalB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0
  multA : Function.Injective (pointMultiplication a (d + 1))
  multB : Function.Injective (pointMultiplication b (d + 1))
  codeA : Function.Injective ((scalarEvaluation z (d + 1 + 1)).comp
    (tangentPointProductForm a (d + 1)).range.subtype)
  codeB : Function.Injective ((scalarEvaluation z (d + 1 + 1)).comp
    (tangentPointProductForm b (d + 1)).range.subtype)

/-- Every fractional ambient kernel section has the stated extended trace and
residual polynomial form, with the residual scalar pair vanishing at the slices. -/
theorem exists_assembledRelation_of_ambient_eq_zero
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d)
    (f : HyperplaneEuler.Relations K (m + 2) (d + 1 + 1))
    (hf : ambientEvaluation K m a b x z (d + 1 + 1) f = 0) :
    let τ := ambientTraceRelation K m (d + 1 + 1) f
    relationEvaluation z (d + 1 + 1) τ = 0 ∧
      ∃ w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1),
        assembledRelation τ w = f ∧
        pointEvaluation K a (d + 1) (restrictAForm K m (d + 1)
          (w.2 + tangentProduct K m d w.1)) = 0 ∧
        pointEvaluation K b (d + 1) (restrictForm K (m + 1) (d + 1) w.2) = 0 := by
  let D := d + 1 + 1
  let τ := ambientTraceRelation K m D f
  obtain ⟨hfA, hfB⟩ := slice_evaluations_zero_of_ambient_eq_zero a b x z f hf
  have hτ : relationEvaluation z D τ = 0 :=
    trace_vanishing_of_slice_vanishing b z (sliceBRelation K m D f) hfB
  have hA : sliceARelation K m D f = HyperplaneEuler.extend K m D τ := by
    rw [slice_eq_extend_of_vanishing a z (d + 1) hc.attachedA hc.normalA
      hc.multA hc.codeA _ hfA, sliceRelations_trace_eq]
    rfl
  have hB : sliceBRelation K m D f = HyperplaneEuler.extend K m D τ :=
    slice_eq_extend_of_vanishing b z (d + 1) hc.attachedB hc.normalB hc.multB hc.codeB _ hfB
  let ext := extendTraceRelation K m D τ
  have cancel (g : HyperplaneEuler.Relations K (m + 1) D) : g + (-1 : K) • g = 0 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (g.val i).val + (-1 : K) • (g.val i).val = 0
    simp
  obtain ⟨w, hw⟩ := exists_residualEuler_of_slice_relations_zero K m d
    (f + (-1 : K) • ext)
    (by
      change sliceARelation K m D (f + (-1 : K) • ext) = 0
      rw [map_add, map_smul, hA, show ext = extendTraceRelation K m D τ from rfl,
        sliceA_extendTraceRelation, cancel])
    (by
      change sliceBRelation K m D (f + (-1 : K) • ext) = 0
      rw [map_add, map_smul, hB, show ext = extendTraceRelation K m D τ from rfl,
        sliceB_extendTraceRelation, cancel])
  have hfw : assembledRelation τ w = f := by
    change ext + residualEuler K m d w = f
    rw [hw]
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (ext.val i).val + ((f.val i).val + (-1 : K) • (ext.val i).val) = (f.val i).val
    simp [add_left_comm]
  have hAres (i : Fin p) (j : Fin (m + 2)) :
      eval (sliceARepresentative K m (chartPoint K a i))
        ((residualEuler K m d w).val j).val = 0 := by
    have he := extendTraceRelation_vanishes_at_attached z τ hτ
      (sliceARepresentative K m (chartPoint K a i)) (hc.attachedA i) j
    have hv := congrFun (congrFun (congrArg (fun v => v.1.1) hf) i) j
    change eval (sliceARepresentative K m (chartPoint K a i)) (f.val j).val = 0 at hv
    rw [← hfw] at hv
    change eval (sliceARepresentative K m (chartPoint K a i))
      (((extendTraceRelation K m D τ).val j).val + ((residualEuler K m d w).val j).val) = 0 at hv
    rwa [map_add, he, zero_add] at hv
  have hBres (i : Fin r) (j : Fin (m + 2)) :
      eval (Fin.cons 0 (chartPoint K b i)) ((residualEuler K m d w).val j).val = 0 := by
    have he := extendTraceRelation_vanishes_at_attached z τ hτ
      (Fin.cons 0 (chartPoint K b i)) (hc.attachedB i) j
    have hv := congrFun (congrFun (congrArg (fun v => v.1.2) hf) i) j
    change eval (Fin.cons 0 (chartPoint K b i)) (f.val j).val = 0 at hv
    rw [← hfw] at hv
    change eval (Fin.cons 0 (chartPoint K b i))
      (((extendTraceRelation K m D τ).val j).val + ((residualEuler K m d w).val j).val) = 0 at hv
    rwa [map_add, he, zero_add] at hv
  refine ⟨hτ, w, hfw, ?_, ?_⟩
  · funext i
    change eval (chartPoint K a i) (restrictA K m
      (w.2.val + (tangentProduct K m d w.1).val)) = 0
    rw [eval_restrictA, map_add]
    have hi := hAres i (0 : Fin (m + 1)).succ
    change eval (sliceARepresentative K m (chartPoint K a i))
      (X 0 * (-w.2.val - (tangentProduct K m d w.1).val)) = 0 at hi
    rw [map_mul, eval_X] at hi
    have hneg := (mul_eq_zero.mp hi).resolve_left (hc.normalA i)
    rw [map_sub, map_neg] at hneg
    linear_combination -hneg
  · funext i
    change eval (chartPoint K b i) (hyperplaneRestrict K (m + 1) w.2.val) = 0
    rw [eval_hyperplaneRestrict]
    have hi := hBres i 0
    change eval (Fin.cons 0 (chartPoint K b i))
      (X (0 : Fin (m + 1)).succ * w.2.val) = 0 at hi
    rw [map_mul, eval_X] at hi
    exact (mul_eq_zero.mp hi).resolve_left (hc.normalB i)

end IdealGeneration.TwoNormalFractional
