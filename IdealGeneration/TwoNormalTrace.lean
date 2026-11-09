module

public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.Points
public import IdealGeneration.SubspaceInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Two-normal polynomial restriction and residual pairs

The first two variables are `s,t`; all later variables are trace variables.
These are the polynomial restriction and correction constructions used in
Lemma 4.2 and in the residual pair map (4.8). The geometric genericity
step is handled separately.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- Interchange the two normal variables and fix the trace variables. -/
def swapNormals : Poly K (m + 2) →ₐ[K] Poly K (m + 2) :=
  MvPolynomial.aeval (Fin.cons (X (0 : Fin (m + 1)).succ)
    (Fin.cons (X 0) (fun i : Fin m => X i.succ.succ)))

@[simp] theorem swapNormals_s : swapNormals K m (X 0) = X (0 : Fin (m + 1)).succ := by
  simp [swapNormals]

@[simp] theorem swapNormals_t :
    swapNormals K m (X (0 : Fin (m + 1)).succ) = X 0 := by
  simp [swapNormals]

@[simp] theorem swapNormals_y (i : Fin m) :
    swapNormals K m (X i.succ.succ) = X i.succ.succ := by
  simp [swapNormals]

@[simp] theorem swapNormals_twice (f : Poly K (m + 2)) :
    swapNormals K m (swapNormals K m f) = f := by
  have h : (swapNormals K m).comp (swapNormals K m) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change swapNormals K m (swapNormals K m (X 0)) = X 0
      rw [swapNormals_s, swapNormals_t]
    · refine Fin.cases ?_ (fun i => ?_) i
      · change swapNormals K m (swapNormals K m (X (0 : Fin (m + 1)).succ)) =
          X (0 : Fin (m + 1)).succ
        rw [swapNormals_t, swapNormals_s]
      · change swapNormals K m (swapNormals K m (X i.succ.succ)) = X i.succ.succ
        rw [swapNormals_y, swapNormals_y]
  exact congrArg (fun F : Poly K (m + 2) →ₐ[K] Poly K (m + 2) => F f) h

/-- Restriction to the slice `s=0`, with `t` as its first coordinate. -/
abbrev restrictB := hyperplaneRestrict K (m + 1)

/-- Restriction to the slice `t=0`, with `s` as its first coordinate. -/
def restrictA : Poly K (m + 2) →ₐ[K] Poly K (m + 1) :=
  (hyperplaneRestrict K (m + 1)).comp (swapNormals K m)

/-- Restriction to the common trace `s=t=0`. -/
def restrictTrace : Poly K (m + 2) →ₐ[K] Poly K m :=
  (hyperplaneRestrict K m).comp (hyperplaneRestrict K (m + 1))

@[simp] theorem restrictA_s : restrictA K m (X 0) = X 0 := by
  simp only [restrictA, AlgHom.comp_apply, swapNormals_s, hyperplaneRestrict_X_succ]

@[simp] theorem restrictA_t : restrictA K m (X (0 : Fin (m + 1)).succ) = 0 := by
  simp only [restrictA, AlgHom.comp_apply, swapNormals_t, hyperplaneRestrict_X_zero]

@[simp] theorem restrictA_y (i : Fin m) : restrictA K m (X i.succ.succ) = X i.succ := by
  simp only [restrictA, AlgHom.comp_apply, swapNormals_y, hyperplaneRestrict_X_succ]

@[simp] theorem restrictTrace_s : restrictTrace K m (X 0) = 0 := by
  simp only [restrictTrace, AlgHom.comp_apply, hyperplaneRestrict_X_zero, map_zero]

@[simp] theorem restrictTrace_t : restrictTrace K m (X (0 : Fin (m + 1)).succ) = 0 := by
  simp only [restrictTrace, AlgHom.comp_apply, hyperplaneRestrict_X_succ, hyperplaneRestrict_X_zero]

@[simp] theorem restrictTrace_y (i : Fin m) : restrictTrace K m (X i.succ.succ) = X i := by
  simp only [restrictTrace, AlgHom.comp_apply, hyperplaneRestrict_X_succ]

/-- The common trace is independent of which slice is taken first. -/
theorem restrictA_trace (f : Poly K (m + 2)) :
    hyperplaneRestrict K m (restrictA K m f) = restrictTrace K m f := by
  have h : (hyperplaneRestrict K m).comp (restrictA K m) = restrictTrace K m := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change hyperplaneRestrict K m (restrictA K m (X 0)) = restrictTrace K m (X 0)
      rw [restrictA_s, hyperplaneRestrict_X_zero, restrictTrace_s]
    · refine Fin.cases ?_ (fun i => ?_) i
      · change hyperplaneRestrict K m (restrictA K m (X (0 : Fin (m + 1)).succ)) =
          restrictTrace K m (X (0 : Fin (m + 1)).succ)
        rw [restrictA_t, map_zero, restrictTrace_t]
      · change hyperplaneRestrict K m (restrictA K m (X i.succ.succ)) =
          restrictTrace K m (X i.succ.succ)
        rw [restrictA_y, hyperplaneRestrict_X_succ, restrictTrace_y]
  exact congrArg (fun F : Poly K (m + 2) →ₐ[K] Poly K m => F f) h

/-- Swapping normals preserves homogeneous degree. -/
theorem swapNormals_homogeneous {d : ℕ} {f : Poly K (m + 2)}
    (hf : f.IsHomogeneous d) : (swapNormals K m f).IsHomogeneous d := by
  have hvars : ∀ j : Fin (m + 2),
      (Fin.cons (α := fun _ => Poly K (m + 2)) (X (0 : Fin (m + 1)).succ)
        (Fin.cons (X 0) (fun i : Fin m => X i.succ.succ)) j : Poly K (m + 2)).IsHomogeneous 1 := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact isHomogeneous_X (R := K) _
    · refine Fin.cases ?_ (fun i => ?_) i <;> exact isHomogeneous_X (R := K) _
  unfold swapNormals
  simpa only [one_mul] using hf.aeval _ hvars

/-- The first slice restriction on homogeneous forms. -/
def restrictAForm (d : ℕ) : Forms K (m + 2) d →ₗ[K] Forms K (m + 1) d where
  toFun f := ⟨restrictA K m f.val,
    hyperplaneRestrict_homogeneous K (m + 1) (swapNormals_homogeneous K m f.property)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The common-trace restriction on homogeneous forms. -/
def restrictTraceForm (d : ℕ) : Forms K (m + 2) d →ₗ[K] Forms K m d :=
  (restrictForm K m d).comp (restrictForm K (m + 1) d)

@[simp] theorem restrictAForm_val {d : ℕ} (f : Forms K (m + 2) d) :
    (restrictAForm K m d f).val = restrictA K m f.val := rfl

@[simp] theorem restrictTraceForm_val {d : ℕ} (f : Forms K (m + 2) d) :
    (restrictTraceForm K m d f).val = restrictTrace K m f.val := rfl

/-- Extend a trace form independently of both normal variables. -/
def extendTraceForm (d : ℕ) : Forms K m d →ₗ[K] Forms K (m + 2) d :=
  (extendForm K (m + 1) d).comp (extendForm K m d)

@[simp] theorem restrict_extendTraceForm {d : ℕ} (f : Forms K m d) :
    restrictTraceForm K m d (extendTraceForm K m d f) = f := by
  simp [restrictTraceForm, extendTraceForm]

/-- Restriction to the codimension-two trace is split surjective. -/
theorem restrictTraceForm_surjective (d : ℕ) :
    Function.Surjective (restrictTraceForm K m d) :=
  fun f => ⟨extendTraceForm K m d f, restrict_extendTraceForm K m f⟩

/-- Tangential multiplication in the ambient polynomial ring. -/
def tangentProduct (d : ℕ) :
    (Fin m → Forms K (m + 2) d) →ₗ[K] Forms K (m + 2) (d + 1) where
  toFun f := ⟨∑ i, X i.succ.succ * (f i).val, by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) i.succ.succ).mul (f i).property⟩
  map_add' f g := by apply Subtype.ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by apply Subtype.ext; simp [Finset.smul_sum]

@[simp] theorem tangentProduct_val {d : ℕ} (f : Fin m → Forms K (m + 2) d) :
    (tangentProduct K m d f).val = ∑ i, X i.succ.succ * (f i).val := rfl

/-- Tangential multiplication followed by restriction to the common trace. -/
def traceProduct (d : ℕ) (G : Submodule K (Forms K (m + 2) d)) :
    (Fin m → G) →ₗ[K] Forms K m (d + 1) :=
  (restrictTraceForm K m (d + 1)).comp
    ((tangentProduct K m d).comp (LinearMap.pi fun i => G.subtype.comp (LinearMap.proj i)))

@[simp] theorem traceProduct_val {d : ℕ} (G : Submodule K (Forms K (m + 2) d))
    (f : Fin m → G) :
    (traceProduct K m d G f).val = ∑ i, X i * restrictTrace K m (f i).val.val := by
  change restrictTrace K m (∑ i, X i.succ.succ * (f i).val.val) = _
  simp

/-- The actual polynomial-pair map appearing in (4.8). -/
def residualPair {p d : ℕ} (x : PointCoordinates K (m + 1) p) :
    ((Fin m → pointDegreePiece K x d) × pointDegreePiece K x (d + 1)) →ₗ[K]
      (Forms K (m + 1) (d + 1) × Forms K (m + 1) (d + 1)) where
  toFun z := (restrictAForm K m (d + 1)
      (z.2.val + tangentProduct K m d (fun i => (z.1 i).val)),
    restrictForm K (m + 1) (d + 1) z.2.val)
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      simp [tangentProduct, map_add, mul_add, Finset.sum_add_distrib]
      ring
    · exact (restrictForm K (m + 1) (d + 1)).map_add _ _
  map_smul' c z := by
    apply Prod.ext
    · apply Subtype.ext
      simp [tangentProduct, smul_add, Finset.smul_sum]
    · exact (restrictForm K (m + 1) (d + 1)).map_smul _ _

/-- Injectivity of the residual pair parametrization uses only the two
restriction injections and nonzero residual normal coordinates. -/
theorem residualPair_injective {p d : ℕ} (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp
      (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    Function.Injective (residualPair K m (d := d) x) := by
  have hzero : ∀ z, residualPair K m (d := d) x z = 0 → z = 0 := by
    rintro ⟨a, h⟩ hz
    have hA : restrictA K m (h.val.val + ∑ i, X i.succ.succ * (a i).val.val) = 0 :=
      congrArg (fun z => z.1.val) hz
    have hB : hyperplaneRestrict K (m + 1) h.val.val = 0 :=
      congrArg (fun z => z.2.val) hz
    have hhtrace : restrictTrace K m h.val.val = 0 := by
      change hyperplaneRestrict K m (hyperplaneRestrict K (m + 1) h.val.val) = 0
      rw [hB, map_zero]
    have hatrace : traceProduct K m d (pointDegreePiece K x d) a = 0 := by
      apply Subtype.ext
      have hh := congrArg (hyperplaneRestrict K m) hA
      rw [restrictA_trace] at hh
      simpa only [map_add, map_sum, map_mul, restrictTrace_y, hhtrace,
        zero_add, map_zero, Submodule.coe_zero, traceProduct_val] using hh
    have ha : a = 0 := hproduct (by simpa using hatrace)
    have hAzero : restrictA K m h.val.val = 0 := by simpa [ha] using hA
    have hBform : restrictForm K (m + 1) (d + 1) h.val = 0 := Subtype.ext hB
    obtain ⟨v, hv⟩ := (restrictForm_eq_zero_iff K (m + 1) h.val).mp hBform
    have hvG : v ∈ pointDegreePiece K x d := by
      rw [mem_pointDegreePiece]
      intro i
      have hi := (mem_pointDegreePiece x h.val).mp h.property i
      rw [hv, map_mul, eval_X] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hs i)
    have hvA : restrictA K m v.val = 0 := by
      rw [hv, map_mul, restrictA_s] at hAzero
      exact (mul_eq_zero.mp hAzero).resolve_left (X_ne_zero 0)
    have hvtrace : restrictTraceForm K m d v = 0 := by
      apply Subtype.ext
      simp only [restrictTraceForm_val, ← restrictA_trace, hvA, map_zero, Submodule.coe_zero]
    have hvzero : (⟨v, hvG⟩ : pointDegreePiece K x d) = 0 :=
      htrace (by simpa using hvtrace)
    have hhzero : h = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      have hvv : v.val = 0 := congrArg (fun w : pointDegreePiece K x d => w.val.val) hvzero
      simp [hv, hvv]
    exact Prod.ext ha hhzero
  intro z w hzw
  apply sub_eq_zero.mp
  apply hzero
  calc
    residualPair K m (d := d) x (z - w) =
        residualPair K m (d := d) x z - residualPair K m (d := d) x w :=
      map_sub (residualPair K m (d := d) x) z w
    _ = 0 := sub_eq_zero.mpr hzw

end IdealGeneration.TwoNormalTrace
