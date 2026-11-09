module

public import IdealGeneration.TripleNormalElimination
public import IdealGeneration.NormalCoefficientRecovery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The evaluation map following three-normal coefficient elimination. -/
noncomputable section
namespace IdealGeneration.TripleNormal
open MvPolynomial NormalDegree

variable {K : Type*} [Field K] {m p q : ℕ}
  (C : ConeConfiguration K 3 m p q)

local instance (priority := 2000) canonicalSubmoduleGroup
    {A : Type*} [AddCommMonoid A] [Module K A] (S : Submodule K A) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup K

abbrev MixedKernel := (quadraticRestriction C).ker

/-- Products of the mixed kernel quadrics with trace linear forms. -/
def mixedProduct : (Fin m → MixedKernel C) →ₗ[K] C.residualPiece 3 :=
  (traceProduct C).comp (LinearMap.pi (fun b =>
    (MixedKernel C).subtype.comp (LinearMap.proj b)))

@[simp] theorem mixedProduct_val (f : Fin m → MixedKernel C) :
    (mixedProduct C f).val.val =
      ∑ b : Fin m, X (b.natAdd 3) * (f b).val.val.val := by
  simp [mixedProduct, traceProduct_val]

/-- Mixed kernel quadrics have normal degree one. -/
theorem mixedKernel_weighted (f : MixedKernel C) :
    f.val.val.val.IsWeightedHomogeneous (normalWeight 3 m) 1 := by
  have hs := quadratic_split K 3 m f.val.val f.val.property.2
  have hq : pureRestrict K 3 m f.val.val.val = 0 := congrArg Subtype.val f.property
  rw [hq, map_zero, add_zero] at hs
  rw [hs]
  exact component_weighted K 3 m 1 f.val.val.val

/-- Multiplication by a trace coordinate retains the single normal degree. -/
theorem mixedProduct_weighted (f : Fin m → MixedKernel C) :
    (mixedProduct C f).val.val.IsWeightedHomogeneous (normalWeight 3 m) 1 := by
  rw [mixedProduct_val]
  apply IsWeightedHomogeneous.sum
  intro b _
  simpa using (isWeightedHomogeneous_X (R := K) (normalWeight 3 m) (b.natAdd 3)).mul
    (mixedKernel_weighted C (f b))

/-- The vector of trace quadrics represented by the mixed products. -/
def mixedCoefficient : (Fin m → MixedKernel C) →ₗ[K] (Fin 3 → Forms K m 2) :=
  (linearCoefficientMap K 3 m 2).comp
    ((C.residualPiece 3).subtype.comp (mixedProduct C))

/-- The coefficient-space source of D_h. -/
abbrev EvaluationSource := Omega C × (Fin m → MixedKernel C)

variable (L : Forms K 3 2 →ₗ[K] C.residualPiece 2)

/-- The vector-valued quadratic before evaluating on the trace points. -/
def reducedCoefficient : EvaluationSource C →ₗ[K] (Fin 3 → Forms K m 2) :=
  (coefficientMap C L).comp (LinearMap.fst K _ _) +
    (mixedCoefficient C).comp (LinearMap.snd K _ _)

/-- The same vector represented as an actual residual cubic. -/
def reducedPolynomial : EvaluationSource C →ₗ[K] C.residualPiece 3 :=
  (eliminatedCubic C L).comp (LinearMap.fst K _ _) +
    (mixedProduct C).comp (LinearMap.snd K _ _)

/-- The two descriptions have exactly the same polynomial coefficients. -/
theorem reduced_reconstruct (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (x : EvaluationSource C) :
    normalLinearProduct K 3 m 2 (reducedCoefficient C L x) =
      (reducedPolynomial C L x).val := by
  have hh : linearCoefficientMap K 3 m 2 (reducedPolynomial C L x).val =
      reducedCoefficient C L x := by
    simp [reducedPolynomial, reducedCoefficient, coefficientMap, mixedCoefficient]
  rw [← hh]
  apply normalLinearProduct_coefficient K 3 m
  exact (eliminatedCubic_weighted C L hL x.1).add (mixedProduct_weighted C x.2)

/-- Evaluate each vector coordinate at each trace representative. -/
def vectorEvaluation : (Fin 3 → Forms K m 2) →ₗ[K] (Fin 3 → Fin q → K) where
  toFun f a i := eval (C.trace i) (f a).val
  map_add' f g := by funext a i; simp
  map_smul' r f := by funext a i; simp

/-- D_h as an actual evaluation map, before restricting its codomain to the
allowed value spaces at marked cone supports. -/
def evaluationMap : EvaluationSource C →ₗ[K] (Fin 3 → Fin q → K) :=
  (vectorEvaluation C).comp (reducedCoefficient C L)

/-- The kernel of vector evaluation consists exactly of three trace equations. -/
def traceEquationEquiv : (Fin 3 → C.tracePiece 2) ≃ₗ[K] (vectorEvaluation C).ker where
  toFun f := ⟨fun a => (f a).val, by
    funext a i
    exact (C.mem_tracePiece (f a).val).mp (f a).property i⟩
  invFun f a := ⟨f.val a, by
    apply (C.mem_tracePiece _).mpr
    intro i
    exact congrFun (congrFun f.property a) i⟩
  left_inv f := by funext a; rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

/-- D_h's kernel is the kernel of the augmented coefficient equation after
adjoining three trace-ideal coefficients. -/
def augmentedKernelEquiv :
    (kernelAugmentation (K := K) (A := EvaluationSource C) (B := Fin 3 → Forms K m 2)
      (C := Fin 3 → Fin q → K) (reducedCoefficient C L) (vectorEvaluation C)).ker ≃ₗ[K]
      (evaluationMap C L).ker :=
  kernelAugmentationKerEquiv
    (K := K) (A := EvaluationSource C) (B := Fin 3 → Forms K m 2)
    (C := Fin 3 → Fin q → K) (reducedCoefficient C L) (vectorEvaluation C)

/-- Scalar normal constraints cutting out the allowed trace values. -/
def valueConstraint : (Fin 3 → Fin q → K) →ₗ[K] (Fin p → K) where
  toFun v i := ∑ a : Fin 3, C.normal i a * v a (C.support i)
  map_add' f g := by funext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r f := by funext i; simp [Finset.mul_sum, mul_left_comm]

abbrev AllowedValues := (valueConstraint C).ker

/-- Evaluate a normal-linear cubic on a marked cone point. -/
theorem eval_normalLinearProduct (f : Fin 3 → Forms K m 2) (i : Fin p) :
    eval (C.point i) (normalLinearProduct K 3 m 2 f).val =
      C.height i ^ 2 * ∑ a : Fin 3, C.normal i a * eval (C.trace (C.support i)) (f a).val := by
  rw [normalLinearProduct_val, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, eval_X, eval_coneExtend]
  simp only [ConeConfiguration.point, Fin.addCases_left, Fin.addCases_right]
  rw [homogeneous_eval_scale (f a).property]
  ring

/-- The reduced coefficient vector takes values in the allowed spaces imposed
by the actual cone equations. -/
theorem reducedCoefficient_allowed (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hheight : ∀ i, C.height i ≠ 0) (x : EvaluationSource C) :
    vectorEvaluation C (reducedCoefficient C L x) ∈ AllowedValues C := by
  funext i
  have hzero := (C.mem_conePiece (reducedPolynomial C L x).val).mp
    (reducedPolynomial C L x).property.1 i
  rw [← reduced_reconstruct C L hL x, eval_normalLinearProduct] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 (hheight i))

/-- The square evaluation map from A.4 with its geometrically allowed codomain. -/
def allowedEvaluationMap (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hheight : ∀ i, C.height i ≠ 0) : EvaluationSource C →ₗ[K] AllowedValues C :=
  (evaluationMap C L).codRestrict (AllowedValues C) (reducedCoefficient_allowed C L hL hheight)

/-- Restricting the codomain does not change the evaluation kernel. -/
theorem allowedEvaluationMap_ker (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (hheight : ∀ i, C.height i ≠ 0) :
    (allowedEvaluationMap C L hL hheight).ker = (evaluationMap C L).ker := by
  ext x
  change allowedEvaluationMap C L hL hheight x = 0 ↔ evaluationMap C L x = 0
  exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩

/-- The coefficient-space source has the dimension used in the square map. -/
theorem finrank_evaluationSource [CharZero K]
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (h : ℕ) (hker : Module.finrank K (MixedKernel C) = h) :
    Module.finrank K (EvaluationSource C) = 3 * h + 8 + m * h := by
  have hsum := finrank_eq_add_of_linearEquiv (K := K) (V := EvaluationSource C)
    (W := Omega C) (U := Fin m → MixedKernel C) (LinearEquiv.refl K (EvaluationSource C))
  rw [hsum, finrank_Omega C L hL h hker]
  let : Module.Free K (MixedKernel C) := Module.Free.of_divisionRing K (MixedKernel C)
  rw [Module.finrank_pi_fintype (R := K) (M := fun _ : Fin m => MixedKernel C), hker]
  simp

/-- Independent cone-direction constraints give the allowed value dimension. -/
theorem finrank_allowedValues_add (honto : Function.Surjective (valueConstraint C)) :
    Module.finrank K (AllowedValues C) + p = 3 * q := by
  have hr := TwoGroup.rank_nullity_monoid (K := K) (U := Fin 3 → Fin q → K)
    (C := Fin p → K) (valueConstraint C)
  have hsource : Module.finrank K (Fin 3 → Fin q → K) = 3 * q := by
    simp [Module.finrank_pi_fintype]
  have htarget : Module.finrank K (Fin p → K) = p := by simp
  rw [LinearMap.range_eq_top.mpr honto, finrank_top, hsource, htarget] at hr
  change Module.finrank K (valueConstraint C).ker + p = 3 * q
  omega

/-- The numerical balance in A.4 makes the actual evaluation map square. -/
theorem allowedEvaluationMap_square [CharZero K]
    (hL : ∀ Q, quadraticRestriction C (L Q) = Q)
    (h : ℕ) (hker : Module.finrank K (MixedKernel C) = h)
    (honto : Function.Surjective (valueConstraint C))
    (hcount : 3 * q = 3 * h + 8 + m * h + p) :
    Module.finrank K (EvaluationSource C) = Module.finrank K (AllowedValues C) := by
  rw [finrank_evaluationSource C L hL h hker]
  have hv := finrank_allowedValues_add C honto
  omega

end IdealGeneration.TripleNormal
