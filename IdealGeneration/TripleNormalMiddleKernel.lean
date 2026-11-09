module

public import IdealGeneration.TripleNormalReduction
public import IdealGeneration.TripleNormalKernelStages

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Kernel equivalence between the actual middle map and three-normal evaluation. -/
noncomputable section
namespace IdealGeneration.TripleNormal
open MvPolynomial NormalDegree
variable {K : Type*} [Field K] {m p q : ℕ} (C : ConeConfiguration K 3 m p q)

local instance middleOmegaGroup : AddCommGroup (Omega C) :=
  Module.addCommMonoidToAddCommGroup K

local instance middleMixedKernelGroup : AddCommGroup (MixedKernel C) :=
  Module.addCommMonoidToAddCommGroup K

abbrev NormalTuples := Fin 3 → C.residualPiece 2
abbrev TraceTuples := Fin m → C.residualPiece 2
abbrev TraceEquations := Fin 3 → C.tracePiece 2
abbrev SplitSource := NormalTuples C × (TraceTuples C × TraceEquations C)

/-- Separate normal and trace coordinate multipliers in the original source. -/
def sourceCoordinates :
    ((Fin (3 + m) → C.residualPiece 2) × TraceEquations C) ≃ₗ[K] SplitSource C where
  toFun f := (fun i => f.1 (i.castAdd m), (fun j => f.1 (j.natAdd 3), f.2))
  invFun f := (Fin.addCases f.1 f.2.1, f.2.2)
  left_inv f := by
    apply Prod.ext
    · funext i
      exact Fin.addCases_castAdd_natAdd f.1 i
    · rfl
  right_inv f := by
    apply Prod.ext
    · funext i; simp
    · apply Prod.ext
      · funext i; simp
      · rfl
  map_add' f g := rfl
  map_smul' a f := rfl

/-- The original middle map with its coordinate groups separated. -/
def fullProduct : SplitSource C →ₗ[K] C.residualPiece 3 :=
  (normalProduct C).comp (LinearMap.fst K _ _) +
    (traceProduct C).comp ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)) +
      (C.normalTraceMultiplication 2).comp ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))

@[simp] theorem normalTrace_as_product (f : TraceEquations C) :
    (C.normalTraceMultiplication 2 f).val = normalLinearProduct K 3 m 2 (fun i => (f i).val) := by
  apply Subtype.ext
  rfl

/-- The separated map is precisely the actual cone middle map. -/
theorem fullProduct_sourceCoordinates
    (f : (Fin (3 + m) → C.residualPiece 2) × TraceEquations C) :
    fullProduct C (sourceCoordinates C f) = C.middleMultiplication 2 f := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [fullProduct, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Submodule.coe_add, normalProduct_val, traceProduct_val,
    normalTrace_as_product, normalLinearProduct_val, sourceCoordinates, LinearEquiv.coe_mk,
    ConeConfiguration.middleMultiplication_val, formMultiplication_val, Fin.sum_univ_add,
    ConeConfiguration.normalTraceCoefficients, Fin.addCases_left, Fin.addCases_right,
    coneExtendForm, Submodule.coe_zero, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- Pure cubic coefficients on the residual target. -/
def cubicProjection : C.residualPiece 3 →ₗ[K] Forms K 3 3 :=
  (pureRestrictForm K 3 m 3).comp (C.residualPiece 3).subtype

@[simp] theorem cubicProjection_traceProduct (f : TraceTuples C) :
    cubicProjection C (traceProduct C f) = 0 := by
  apply Subtype.ext
  simp [cubicProjection, pureRestrictForm, traceProduct_val, map_sum, map_mul]

@[simp] theorem cubicProjection_normalTrace (f : TraceEquations C) :
    cubicProjection C (C.normalTraceMultiplication 2 f) = 0 := by
  apply Subtype.ext
  change pureRestrict K 3 m (C.normalTraceMultiplication 2 f).val.val = 0
  rw [normalTrace_as_product]
  exact pureRestrict_eq_zero_of_lower_weight K 3 m _
    (normalLinearProduct_weighted K 3 m (fun i => (f i).val)) (by decide)

/-- The first leading coefficient constraint is exactly the definition of Omega. -/
theorem cubicProjection_fullProduct (a : NormalTuples C) (b : TraceTuples C)
    (v : TraceEquations C) :
    cubicProjection C (fullProduct C (a, (b, v))) =
      tripleNormalConstraint (K := K) (V := C.residualPiece 2) (quadraticRestriction C) a := by
  simp only [fullProduct, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_add, cubicProjection_traceProduct, cubicProjection_normalTrace,
    add_zero]
  exact restrict_normalProduct C a

/-- The map after eliminating its pure-normal cubic block. -/
def firstProduct : (Omega C × (TraceTuples C × TraceEquations C)) →ₗ[K] C.residualPiece 3 :=
  (fullProduct C).comp ((Omega C).subtype.prodMap
    (LinearMap.id : (TraceTuples C × TraceEquations C) →ₗ[K]
      (TraceTuples C × TraceEquations C)))

/-- Trace-linear normal-quadratic coefficients on the residual target. -/
def quadraticProjection : C.residualPiece 3 →ₗ[K] (Fin m → Forms K 3 2) :=
  (traceCoefficientMap K 3 m 2).comp (C.residualPiece 3).subtype

/-- The trace-coordinate product contributes its pure-normal quadratic coefficients. -/
theorem quadraticProjection_traceProduct (f : TraceTuples C) :
    quadraticProjection C (traceProduct C f) = fun b => quadraticRestriction C (f b) := by
  classical
  funext b
  apply Subtype.ext
  change pureRestrict K 3 m (pderiv (b.natAdd 3) (traceProduct C f).val.val) =
    pureRestrict K 3 m (f b).val.val
  rw [traceProduct_val]
  simp [map_sum, pderiv_X, map_mul, Pi.single_apply, apply_ite]

@[simp] theorem quadraticProjection_normalTrace (f : TraceEquations C) :
    quadraticProjection C (C.normalTraceMultiplication 2 f) = 0 := by
  change traceCoefficientMap K 3 m 2 (C.normalTraceMultiplication 2 f).val = 0
  rw [normalTrace_as_product]
  exact traceCoefficientMap_eq_zero_of_lower_weight K 3 m _
    (normalLinearProduct_weighted K 3 m (fun i => (f i).val)) (by decide)

/-- Apply pure-normal restriction to each trace-coordinate coefficient. -/
def tupleRestriction : TraceTuples C →ₗ[K] (Fin m → Forms K 3 2) :=
  LinearMap.pi (fun b => (quadraticRestriction C).comp (LinearMap.proj b))

local instance middleTupleKernelGroup : AddCommGroup (tupleRestriction C).ker :=
  Module.addCommMonoidToAddCommGroup K

/-- The second leading block determines the quadratic lift coefficients. -/
theorem quadraticProjection_firstProduct (eta : Omega C) (b : TraceTuples C)
    (v : TraceEquations C) :
    quadraticProjection C (firstProduct C (eta, (b, v))) =
      coefficientQuadrics C eta + tupleRestriction C b := by
  change quadraticProjection C (fullProduct C (eta.val, (b, v))) = _
  simp only [fullProduct, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_add, quadraticProjection_normalTrace, add_zero,
    quadraticProjection_traceProduct]
  rfl

variable (L : Forms K 3 2 →ₗ[K] C.residualPiece 2)

/-- Lift a tuple of pure-normal coefficient quadrics. -/
def tupleSection : (Fin m → Forms K 3 2) →ₗ[K] TraceTuples C :=
  LinearMap.pi (fun b => L.comp (LinearMap.proj b))

theorem tupleSection_rightInverse (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (f : Fin m → Forms K 3 2) : tupleRestriction C (tupleSection C L f) = f := by
  funext b
  exact hL (f b)

/-- The two descriptions of the mixed kernel tuple agree coefficientwise. -/
def mixedTupleEquiv : (Fin m → MixedKernel C) ≃ₗ[K] (tupleRestriction C).ker where
  toFun f := ⟨fun b => (f b).val, by funext b; exact (f b).property⟩
  invFun f b := ⟨f.val b, congrFun f.property b⟩
  left_inv f := by funext b; rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

/-- Regroup the reduced coefficients and the final trace-ideal correction. -/
def reducedCoordinates : (EvaluationSource C × TraceEquations C) ≃ₗ[K]
    (Omega C × ((tupleRestriction C).ker × TraceEquations C)) where
  toFun x := (x.1.1, (mixedTupleEquiv C x.1.2, x.2))
  invFun x := ((x.1, (mixedTupleEquiv C).symm x.2.1), x.2.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The residual normal-linear polynomial with its trace-ideal correction. -/
def augmentedProduct : (EvaluationSource C × TraceEquations C) →ₗ[K] C.residualPiece 3 :=
  (reducedPolynomial C L).comp (LinearMap.fst K _ _) +
    (C.normalTraceMultiplication 2).comp (LinearMap.snd K _ _)

/-- The source substitution solving the trace-linear normal-quadratic block. -/
def secondProduct : (Omega C × ((tupleRestriction C).ker × TraceEquations C)) →ₗ[K]
    C.residualPiece 3 :=
  (firstProduct C).comp
    (triangularSource (K := K) (A := Omega C) (B := TraceTuples C)
      (V := TraceEquations C) (Z := Fin m → Forms K 3 2)
      (coefficientQuadrics C) (tupleRestriction C) (tupleSection C L))

/-- The triangular source substitution produces precisely the corrected polynomial. -/
theorem secondProduct_reducedCoordinates (x : EvaluationSource C × TraceEquations C) :
    secondProduct C L (reducedCoordinates C x) = augmentedProduct C L x := by
  have ht : traceProduct C (fun b => (x.1.2 b).val + (-1 : K) • L (coefficientQuadrics C x.1.1 b)) =
      mixedProduct C x.1.2 + (-1 : K) • liftedCorrection C L x.1.1 := by
    change traceProduct C ((fun b => (x.1.2 b).val) +
      (-1 : K) • (fun b => L (coefficientQuadrics C x.1.1 b))) = _
    simp only [map_add, map_smul]
    rfl
  change fullProduct C (x.1.1.val,
    ((fun b => (x.1.2 b).val + (-1 : K) • L (coefficientQuadrics C x.1.1 b)), x.2)) = _
  simp only [fullProduct, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, ht]
  change omegaProduct C x.1.1 + (mixedProduct C x.1.2 + (-1 : K) • liftedCorrection C L x.1.1) +
    C.normalTraceMultiplication 2 x.2 =
      eliminatedCubic C L x.1.1 + mixedProduct C x.1.2 + C.normalTraceMultiplication 2 x.2
  rw [eliminatedCubic_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (omegaProduct C x.1.1).val.val +
      ((mixedProduct C x.1.2).val.val + (-1 : K) • (liftedCorrection C L x.1.1).val.val) +
      (C.normalTraceMultiplication 2 x.2).val.val =
    (omegaProduct C x.1.1).val.val - (liftedCorrection C L x.1.1).val.val +
      (mixedProduct C x.1.2).val.val + (C.normalTraceMultiplication 2 x.2).val.val
  rw [neg_one_smul K (liftedCorrection C L x.1.1).val.val]
  abel

/-- The trace-ideal tuple included into the full vector of trace quadrics. -/
def traceEquationInclusion : TraceEquations C →ₗ[K] (Fin 3 → Forms K m 2) :=
  LinearMap.pi (fun a => (C.tracePiece 2).subtype.comp (LinearMap.proj a))

/-- The last coefficient equation after the two leading blocks are eliminated. -/
def augmentedCoefficient : (EvaluationSource C × TraceEquations C) →ₗ[K]
    (Fin 3 → Forms K m 2) :=
  (reducedCoefficient C L).comp (LinearMap.fst K _ _) +
    (traceEquationInclusion C).comp (LinearMap.snd K _ _)

/-- The last coefficient equation is represented by its actual normal-linear polynomial. -/
theorem augmentedProduct_as_linear (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (x : EvaluationSource C × TraceEquations C) :
    (augmentedProduct C L x).val = normalLinearProduct K 3 m 2 (augmentedCoefficient C L x) := by
  change ((reducedPolynomial C L x.1).val + (C.normalTraceMultiplication 2 x.2).val) = _
  rw [← reduced_reconstruct C L hL x.1, normalTrace_as_product, ← map_add]
  rfl

/-- Recovering the actual coefficients preserves the kernel of the remaining polynomial map. -/
theorem augmentedProduct_ker (hL : ∀ Q, quadraticRestriction C (L Q) = Q) :
    (augmentedProduct C L).ker = (augmentedCoefficient C L).ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have hh := congrArg Subtype.val hx
    change (augmentedProduct C L x).val = 0 at hh
    rw [augmentedProduct_as_linear C L hL] at hh
    apply normalLinearProduct_injective K 3 m 2
    simpa only [map_zero] using hh
  · intro hx
    apply Subtype.ext
    change (augmentedProduct C L x).val = 0
    rw [augmentedProduct_as_linear C L hL, hx, map_zero]

/-- The final trace-ideal coefficients are the kernel of vector evaluation. -/
def augmentationCoordinates : (EvaluationSource C × TraceEquations C) ≃ₗ[K]
    (EvaluationSource C × (vectorEvaluation C).ker) :=
  LinearEquiv.prodCongr (LinearEquiv.refl K (EvaluationSource C)) (traceEquationEquiv C)

/-- The two coefficient augmentations agree under the natural identification. -/
theorem augmentedCoefficient_coordinates (x : EvaluationSource C × TraceEquations C) :
    kernelAugmentation (K := K) (A := EvaluationSource C) (B := Fin 3 → Forms K m 2)
        (C := Fin 3 → Fin q → K) (reducedCoefficient C L) (vectorEvaluation C)
        (augmentationCoordinates C x) = augmentedCoefficient C L x := rfl

set_option maxHeartbeats 1000000 in
/-- The kernels in (A.8) and (A.11) are linearly equivalent by actual coordinate
coefficient elimination. -/
def middleKernelEquiv (hL : ∀ Q, quadraticRestriction C (L Q) = Q) :
    (C.middleMultiplication 2).ker ≃ₗ[K] (evaluationMap C L).ker := by
  let e₀ := kernelSourceEquiv (K := K)
    (A := (Fin (3 + m) → C.residualPiece 2) × TraceEquations C)
    (B := SplitSource C) (Y := C.residualPiece 3)
    (sourceCoordinates C) (C.middleMultiplication 2) (fullProduct C)
    (fullProduct_sourceCoordinates C)
  let e₁ := firstKernelReduction (K := K) (A := NormalTuples C)
    (B := TraceTuples C × TraceEquations C) (Y := C.residualPiece 3) (Z := Forms K 3 3)
    (tripleNormalConstraint (K := K) (V := C.residualPiece 2) (quadraticRestriction C))
    (fullProduct C) (cubicProjection C)
    (fun a b => cubicProjection_fullProduct C a b.1 b.2)
  let e₂ := triangularKernelReduction (K := K) (A := Omega C) (B := TraceTuples C)
    (V := TraceEquations C) (Y := C.residualPiece 3) (Z := Fin m → Forms K 3 2)
    (coefficientQuadrics C) (tupleRestriction C) (tupleSection C L)
    (tupleSection_rightInverse C L hL) (firstProduct C) (quadraticProjection C)
    (quadraticProjection_firstProduct C)
  let e₃ := kernelSourceEquiv (K := K) (A := EvaluationSource C × TraceEquations C)
    (B := Omega C × ((tupleRestriction C).ker × TraceEquations C)) (Y := C.residualPiece 3)
    (reducedCoordinates C) (augmentedProduct C L) (secondProduct C L)
    (secondProduct_reducedCoordinates C L)
  let e₄ := LinearEquiv.ofEq _ _ (augmentedProduct_ker C L hL)
  let e₅ := kernelSourceEquiv (K := K) (A := EvaluationSource C × TraceEquations C)
    (B := EvaluationSource C × (vectorEvaluation C).ker) (Y := Fin 3 → Forms K m 2)
    (augmentationCoordinates C) (augmentedCoefficient C L) _
    (augmentedCoefficient_coordinates C L)
  let e₆ := kernelAugmentationKerEquiv
    (K := K) (A := EvaluationSource C) (B := Fin 3 → Forms K m 2)
    (C := Fin 3 → Fin q → K) (reducedCoefficient C L) (vectorEvaluation C)
  exact e₀.trans (e₁.trans (e₂.trans (e₃.symm.trans (e₄.trans (e₅.trans e₆)))))

/-- The geometrically allowed codomain has the same middle-map kernel. -/
def middleKernelEquiv_allowed (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hheight : ∀ i, C.height i ≠ 0) :
    (C.middleMultiplication 2).ker ≃ₗ[K] (allowedEvaluationMap C L hL hheight).ker :=
  (middleKernelEquiv C L hL).trans
    (LinearEquiv.ofEq _ _ (allowedEvaluationMap_ker C L hL hheight).symm)

/-- Injectivity is equivalent for the actual middle map and D_h. -/
theorem middle_injective_iff_allowedEvaluation (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hheight : ∀ i, C.height i ≠ 0) :
    Function.Injective (C.middleMultiplication 2) ↔
      Function.Injective (allowedEvaluationMap C L hL hheight) := by
  rw [linearMap_injective_iff_kernel_subsingleton (C.middleMultiplication 2),
    linearMap_injective_iff_kernel_subsingleton (allowedEvaluationMap C L hL hheight)]
  exact (middleKernelEquiv_allowed C L hL hheight).toEquiv.subsingleton_congr

end IdealGeneration.TripleNormal
