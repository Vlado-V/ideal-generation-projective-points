module

public import IdealGeneration.QuadraticCore
public import IdealGeneration.QuadraticIndependentCones
public import IdealGeneration.QuadraticLinearForms
public import IdealGeneration.AffineEulerTransport
public import IdealGeneration.ConeSplitting
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Actual multiplication in the six-point quadratic core

The coordinate matrix is invertible, so its dual linear forms interpolate the
six cone points. These forms give both the residual dimensions and a transport
of the independent-cone multiplication calculation into the actual core.
-/

noncomputable section
namespace IdealGeneration.QuadraticCoreMultiplication
open MvPolynomial Module QuadraticFlag QuadraticIndependentCones

variable (K : Type*) [Field K] [CharZero K]

/-- The core points over an arbitrary characteristic-zero field. -/
def pointMatrix : Matrix (Fin 6) (Fin 6) K :=
  quadraticCoreConeMatrix.map (Rat.castHom K)

/-- The two normal coordinate values on each core point. -/
def normalS (i : Fin 6) : K := pointMatrix K i 0
def normalT (i : Fin 6) : K := pointMatrix K i 1

theorem pointMatrix_det_ne_zero : (pointMatrix K).det ≠ 0 :=
  quadraticCoreConeMatrix_det_ne_zero_over K

theorem normalS_ne_zero (i : Fin 6) : normalS K i ≠ 0 := by
  fin_cases i <;> norm_num [normalS, pointMatrix, quadraticCoreConeMatrix]

theorem normal_directions_distinct (i j : Fin 6) (hij : i ≠ j) :
    normalT K i * normalS K j - normalS K i * normalT K j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [normalS, normalT, pointMatrix, quadraticCoreConeMatrix] at *

/-- The linear coordinate map whose columns are the six core points. -/
def coordinateEquiv : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
  let f := (pointMatrix K).transpose.mulVecLin
  let hf : Function.Injective f := Matrix.mulVec_injective_of_det_ne_zero
    (by simpa only [Matrix.det_transpose] using pointMatrix_det_ne_zero K)
  LinearEquiv.ofBijective f ⟨hf, LinearMap.surjective_of_injective hf⟩

@[simp] theorem coordinateEquiv_apply (x : Fin 6 → K) (j : Fin 6) :
    coordinateEquiv K x j = ∑ i, pointMatrix K i j * x i := rfl

@[simp] theorem coordinateEquiv_basis (i : Fin 6) :
    coordinateEquiv K (Pi.single i 1) = pointMatrix K i := by
  ext j
  simp [coordinateEquiv_apply, Pi.single_apply]

/-- Dual coordinate linear forms for the actual six points. -/
def dualLinear (i : Fin 6) : Poly K 6 :=
  linearCoordinateSubstitution (coordinateEquiv K).symm (X i)

theorem dualLinear_homogeneous (i : Fin 6) : (dualLinear K i).IsHomogeneous 1 :=
  linearCoordinateSubstitution_homogeneous _ (isHomogeneous_X K i)

@[simp] theorem dualLinear_evaluation (i j : Fin 6) :
    eval (pointMatrix K j) (dualLinear K i) = if i = j then 1 else 0 := by
  rw [dualLinear, eval_linearCoordinateSubstitution]
  have he : (coordinateEquiv K).symm (pointMatrix K j) = Pi.single j 1 := by
    rw [← coordinateEquiv_basis K j, LinearEquiv.symm_apply_apply]
  rw [he]
  simp [Pi.single_apply]

/-- Evaluation of the first normal linear form in the coordinate-point model. -/
theorem eval_standard_normalS (x : Fin 6 → K) :
    eval x (linearPolynomial (normalS K)) = coordinateEquiv K x 0 := by
  simp [eval_linearPolynomial, coordinateEquiv_apply, normalS]

/-- Evaluation of the second normal linear form in the coordinate-point model. -/
theorem eval_standard_normalT (x : Fin 6 → K) :
    eval x (linearPolynomial (normalT K)) = coordinateEquiv K x 1 := by
  simp [eval_linearPolynomial, coordinateEquiv_apply, normalT]

theorem substitute_standard_normalS :
    linearCoordinateSubstitution (coordinateEquiv K).symm (linearPolynomial (normalS K)) = X 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_linearCoordinateSubstitution, eval_standard_normalS, LinearEquiv.apply_symm_apply, eval_X]

theorem substitute_standard_normalT :
    linearCoordinateSubstitution (coordinateEquiv K).symm (linearPolynomial (normalT K)) = X 1 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_linearCoordinateSubstitution, eval_standard_normalT, LinearEquiv.apply_symm_apply, eval_X]

/-- The actual residual quadrics obtained by transporting the coordinate-point generators. -/
def residualQuadric (i : Fin 6) : Poly K 6 :=
  dualLinear K i * (C (normalT K i) * X 0 - C (normalS K i) * X 1)

theorem substitute_residualQuadric (i : Fin 6) :
    linearCoordinateSubstitution (coordinateEquiv K).symm
      (QuadraticIndependentCones.residualQuadric (normalS K) (normalT K) i) =
      residualQuadric K i := by
  simp [QuadraticIndependentCones.residualQuadric, residualQuadric, dualLinear,
    substitute_standard_normalS, substitute_standard_normalT]

theorem residualQuadric_homogeneous (i : Fin 6) : (residualQuadric K i).IsHomogeneous 2 := by
  exact (dualLinear_homogeneous K i).mul
    (((isHomogeneous_X K 0).C_mul _).sub ((isHomogeneous_X K 1).C_mul _))

@[simp] theorem residualQuadric_vanishes (i j : Fin 6) :
    eval (pointMatrix K j) (residualQuadric K i) = 0 := by
  simp [residualQuadric, normalS, normalT]
  intro h
  subst j
  ring

@[simp] theorem residualQuadric_restrict (i : Fin 6) :
    coneRestrict K 2 4 (residualQuadric K i) = 0 := by
  have h0 : coneRestrict K 2 4 (X (0 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 0
  have h1 : coneRestrict K 2 4 (X (1 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 1
  simp [residualQuadric, h0, h1]

/-- Actual normal-ideal equations of the six cone points. -/
def residualPiece (d : ℕ) : Submodule K (Forms K 6 d) :=
  representativePiece K (pointMatrix K) d ⊓ (coneRestrictForm K 2 4 d).ker

@[simp] theorem mem_residualPiece {d : ℕ} (f : Forms K 6 d) :
    f ∈ residualPiece K d ↔ (∀ i, eval (pointMatrix K i) f.val = 0) ∧
      coneRestrict K 2 4 f.val = 0 := by
  simp only [residualPiece, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨h, hr⟩
    exact ⟨(mem_representativePiece K (pointMatrix K) f).mp h, congrArg Subtype.val hr⟩
  · rintro ⟨h, hr⟩
    exact ⟨(mem_representativePiece K (pointMatrix K) f).mpr h, Subtype.ext hr⟩

/-- The same residual space expressed literally as the normal-coordinate ideal. -/
theorem mem_residualPiece_ideal {d : ℕ} (f : Forms K 6 d) :
    f ∈ residualPiece K d ↔ f.val ∈ coneNormalIdeal K 2 4 ∧
      ∀ i, eval (pointMatrix K i) f.val = 0 := by
  rw [mem_residualPiece, coneRestrict_eq_zero_iff]
  exact and_comm

/-- The transported coordinate-point quadrics are actual members of the residual space. -/
def residualQuadricForm (i : Fin 6) : residualPiece K 2 :=
  ⟨⟨residualQuadric K i, residualQuadric_homogeneous K i⟩,
    (mem_residualPiece K _).mpr ⟨residualQuadric_vanishes K i, residualQuadric_restrict K i⟩⟩

/-- Normal-ideal interpolation at one of the six cone points. -/
def interpolationForm (d : ℕ) (hd : 2 ≤ d) (i : Fin 6) : Forms K 6 d :=
  ⟨C ((normalS K i)⁻¹) * X 0 * (dualLinear K i) ^ (d - 1), by
    change (C ((normalS K i)⁻¹) * X 0 * (dualLinear K i) ^ (d - 1)).IsHomogeneous d
    have hh := ((isHomogeneous_X K (0 : Fin 6)).C_mul ((normalS K i)⁻¹)).mul
      ((dualLinear_homogeneous K i).pow (d - 1))
    simpa only [one_mul, show 1 + (d - 1) = d by omega] using hh⟩

@[simp] theorem interpolationForm_eval (d : ℕ) (hd : 2 ≤ d) (i j : Fin 6) :
    eval (pointMatrix K j) (interpolationForm K d hd i).val = if i = j then 1 else 0 := by
  have hn : d - 1 ≠ 0 := by omega
  by_cases hij : i = j
  · subst j
    simp only [interpolationForm, map_mul, map_pow, eval_C, eval_X, dualLinear_evaluation,
      ite_true, one_pow, mul_one]
    exact inv_mul_cancel₀ (normalS_ne_zero K i)
  · simp [interpolationForm, hij, hn]

@[simp] theorem interpolationForm_restrict (d : ℕ) (hd : 2 ≤ d) (i : Fin 6) :
    coneRestrictForm K 2 4 d (interpolationForm K d hd i) = 0 := by
  apply Subtype.ext
  have h0 : coneRestrict K 2 4 (X (0 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 0
  simp [coneRestrictForm, interpolationForm, h0]

/-- Record the full pure trace restriction and the six cone values together. -/
def jointConditions (d : ℕ) : Forms K 6 d →ₗ[K] (Forms K 4 d × (Fin 6 → K)) :=
  (coneRestrictForm K 2 4 d).prod
    (LinearMap.pi fun i => evaluationLinear K 6 d (pointMatrix K i))

/-- These conditions are independent in every degree at least two. -/
theorem jointConditions_surjective (d : ℕ) (hd : 2 ≤ d) :
    Function.Surjective (jointConditions K d) := by
  intro v
  let f₀ := coneExtendForm K 2 4 d v.1
  let coeff : Fin 6 → K := fun i => v.2 i - eval (pointMatrix K i) f₀.val
  let f : Forms K 6 d := f₀ + ∑ i, coeff i • interpolationForm K d hd i
  refine ⟨f, ?_⟩
  apply Prod.ext
  · change coneRestrictForm K 2 4 d f = v.1
    simp only [f, map_add, map_sum, map_smul, interpolationForm_restrict,
      smul_zero, Finset.sum_const_zero, add_zero]
    exact coneRestrictForm_extendForm K 2 4 v.1
  · funext j
    change eval (pointMatrix K j) f.val = v.2 j
    simp [f, coeff]

/-- The kernel of the joint conditions is exactly the actual residual space. -/
theorem jointConditions_ker (d : ℕ) :
    (jointConditions K d).ker = residualPiece K d := by
  ext f
  change (coneRestrictForm K 2 4 d f, fun i => eval (pointMatrix K i) f.val) = 0 ↔ _
  rw [mem_residualPiece]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact congrFun (congrArg Prod.snd h) i
    · exact congrArg Subtype.val (congrArg Prod.fst h)
  · rintro ⟨he, hr⟩
    apply Prod.ext
    · exact Subtype.ext hr
    · funext i
      exact he i

/-- Dimension of the residual part before specializing the degree. -/
theorem finrank_residualPiece_add (d : ℕ) (hd : 2 ≤ d) :
    finrank K (residualPiece K d) + (4 + d - 1).choose d + 6 = (6 + d - 1).choose d := by
  have : Module.Free K (Forms K 4 d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (Forms K 4 d)
  have h := (jointConditions K d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (jointConditions_surjective K d hd), finrank_top,
    Module.finrank_prod, finrank_forms, Module.finrank_pi, Fintype.card_fin,
    jointConditions_ker, finrank_forms] at h
  omega

theorem finrank_residualQuadrics : finrank K (residualPiece K 2) = 5 := by
  have h := finrank_residualPiece_add K 2 (by omega)
  norm_num [Nat.choose] at h
  omega

theorem finrank_residualCubics : finrank K (residualPiece K 3) = 30 := by
  have h := finrank_residualPiece_add K 3 (by omega)
  norm_num [Nat.choose] at h
  omega

/-- The actual coordinate multiplication map in the six-point residual ideal. -/
def residualMultiplication : (Fin 6 → residualPiece K 2) →ₗ[K] residualPiece K 3 where
  toFun f := ⟨formMultiplication K 6 2 (fun j => (f j).val), by
    apply (mem_residualPiece K _).mpr
    constructor
    · intro i
      simp only [formMultiplication_val, map_sum, map_mul, eval_X]
      apply Finset.sum_eq_zero
      intro j _
      rw [((mem_residualPiece K _).mp (f j).property).1 i, mul_zero]
    · have h := coneRestrictForm_multiplication K 2 4 (fun j => (f j).val)
      have hz : (fun j : Fin 4 => coneRestrictForm K 2 4 2 (f (j.natAdd 2)).val) = 0 := by
        funext j
        apply Subtype.ext
        exact ((mem_residualPiece K _).mp (f (j.natAdd 2)).property).2
      rw [hz, map_zero] at h
      exact congrArg Subtype.val h⟩
  map_add' f g := by
    apply Subtype.ext
    exact (formMultiplication K 6 2).map_add _ _
  map_smul' a f := by
    apply Subtype.ext
    exact (formMultiplication K 6 2).map_smul a _

@[simp] theorem residualMultiplication_val (f : Fin 6 → residualPiece K 2) :
    (residualMultiplication K f).val.val = ∑ j, X j * (f j).val.val := rfl

/-- Invertible coordinate substitution is injective on actual polynomials. -/
theorem inverseSubstitution_injective :
    Function.Injective (linearCoordinateSubstitution (coordinateEquiv K).symm) := by
  intro f g h
  apply MvPolynomial.funext
  intro z
  have hz := congrArg (eval (coordinateEquiv K z)) h
  simpa only [eval_linearCoordinateSubstitution, LinearEquiv.symm_apply_apply] using hz

/-- Transport the normalized independent-cone product map into the actual coordinates. -/
def transportedCombination :
    normalizedCoefficients (K := K) (5 : Fin 6) →ₗ[K] Poly K 6 :=
  (linearCoordinateSubstitution (coordinateEquiv K).symm).toLinearMap.comp
    (normalizedMultiplication (normalS K) (normalT K) (5 : Fin 6))

theorem transportedCombination_injective : Function.Injective (transportedCombination K) :=
  (inverseSubstitution_injective K).comp
    (normalizedMultiplication_injective (normalS K) (normalT K) (5 : Fin 6)
      (normal_directions_distinct K))

/-- The transported linear coefficient of one residual generator. -/
def transportedLinear (L : normalizedCoefficients (K := K) (5 : Fin 6)) (i : Fin 6) : Poly K 6 :=
  linearCoordinateSubstitution (coordinateEquiv K).symm (linearPolynomial (L.val i))

theorem transportedLinear_homogeneous (L : normalizedCoefficients (K := K) (5 : Fin 6))
    (i : Fin 6) : (transportedLinear K L i).IsHomogeneous 1 :=
  linearCoordinateSubstitution_homogeneous _ (linearPolynomial_isHomogeneous _)

theorem transportedCombination_eq (L : normalizedCoefficients (K := K) (5 : Fin 6)) :
    transportedCombination K L = ∑ i, transportedLinear K L i * residualQuadric K i := by
  change linearCoordinateSubstitution (coordinateEquiv K).symm
    (∑ i, linearPolynomial (L.val i) *
      QuadraticIndependentCones.residualQuadric (normalS K) (normalT K) i) = _
  simp only [map_sum, map_mul, substitute_residualQuadric, transportedLinear]

theorem transportedCombination_homogeneous
    (L : normalizedCoefficients (K := K) (5 : Fin 6)) :
    (transportedCombination K L).IsHomogeneous 3 := by
  rw [transportedCombination_eq]
  exact IsHomogeneous.sum _ _ _ (fun i _ =>
    (transportedLinear_homogeneous K L i).mul (residualQuadric_homogeneous K i))

theorem transportedCombination_vanishes
    (L : normalizedCoefficients (K := K) (5 : Fin 6)) (j : Fin 6) :
    eval (pointMatrix K j) (transportedCombination K L) = 0 := by
  rw [transportedCombination_eq]
  simp

theorem transportedCombination_restrict
    (L : normalizedCoefficients (K := K) (5 : Fin 6)) :
    coneRestrict K 2 4 (transportedCombination K L) = 0 := by
  rw [transportedCombination_eq]
  simp

/-- The transported independent-cone map has its actual residual cubic codomain. -/
def transportedToResidual :
    normalizedCoefficients (K := K) (5 : Fin 6) →ₗ[K] residualPiece K 3 where
  toFun L := ⟨⟨transportedCombination K L, transportedCombination_homogeneous K L⟩,
    (mem_residualPiece K _).mpr
      ⟨transportedCombination_vanishes K L, transportedCombination_restrict K L⟩⟩
  map_add' L M := by
    apply Subtype.ext
    apply Subtype.ext
    exact (transportedCombination K).map_add L M
  map_smul' a L := by
    apply Subtype.ext
    apply Subtype.ext
    exact (transportedCombination K).map_smul a L

theorem transportedToResidual_injective : Function.Injective (transportedToResidual K) := by
  intro L M h
  apply transportedCombination_injective K
  exact congrArg (fun f => f.val.val) h

theorem transportedToResidual_surjective : Function.Surjective (transportedToResidual K) := by
  let : AddCommGroup (residualPiece K 3) := Module.addCommMonoidToAddCommGroup K
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj (transportedToResidual_injective K),
    finrank_normalizedCoefficients, finrank_residualCubics]
  norm_num

/-- Re-expand the transported linear coefficients in the original coordinate basis. -/
def multiplicationSource (L : normalizedCoefficients (K := K) (5 : Fin 6)) :
    Fin 6 → residualPiece K 2 :=
  fun j => ∑ i, eval (coordinatePoint j) (transportedLinear K L i) • residualQuadricForm K i

@[simp] theorem multiplicationSource_val
    (L : normalizedCoefficients (K := K) (5 : Fin 6)) (j : Fin 6) :
    (multiplicationSource K L j).val.val =
      ∑ i, eval (coordinatePoint j) (transportedLinear K L i) • residualQuadric K i := by
  simp [multiplicationSource, residualQuadricForm]

/-- This is the actual coordinate multiplication witness for every transported cubic. -/
theorem multiplicationSource_product (L : normalizedCoefficients (K := K) (5 : Fin 6)) :
    residualMultiplication K (multiplicationSource K L) = transportedToResidual K L := by
  apply Subtype.ext
  apply Subtype.ext
  rw [residualMultiplication_val]
  change (∑ j, X j * (multiplicationSource K L j).val.val) = transportedCombination K L
  rw [transportedCombination_eq]
  simp only [multiplicationSource_val, Finset.mul_sum, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, X j * (C (eval (coordinatePoint j) (transportedLinear K L i)) * residualQuadric K i)) =
        (∑ j, C (eval (coordinatePoint j) (transportedLinear K L i)) * X j) * residualQuadric K i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = transportedLinear K L i * residualQuadric K i := by
      rw [← linearPolynomial, linearPolynomial_eval_coordinate_of_homogeneous
        (transportedLinear K L i) (transportedLinear_homogeneous K L i)]

/-- Surjectivity of the actual residual multiplication follows from the
transported independent-cone image and the computed residual dimensions. -/
theorem residualMultiplication_surjective : Function.Surjective (residualMultiplication K) := by
  intro f
  obtain ⟨L, rfl⟩ := transportedToResidual_surjective K f
  exact ⟨multiplicationSource K L, multiplicationSource_product K L⟩

theorem residualMultiplication_source_finrank :
    finrank K (Fin 6 → residualPiece K 2) = 30 := by
  have : Module.Free K (residualPiece K 2) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (residualPiece K 2)
  rw [Module.finrank_pi_fintype]
  simp [finrank_residualQuadrics]

/-- The actual core multiplication map is bijective over every characteristic-zero field. -/
theorem residualMultiplication_bijective : Function.Bijective (residualMultiplication K) := by
  refine ⟨?_, residualMultiplication_surjective K⟩
  let : AddCommGroup (Fin 6 → residualPiece K 2) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (residualPiece K 3) := Module.addCommMonoidToAddCommGroup K
  have h := (residualMultiplication K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (residualMultiplication_surjective K), finrank_top,
    finrank_residualCubics, residualMultiplication_source_finrank] at h
  have hk : finrank K (residualMultiplication K).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

end IdealGeneration.QuadraticCoreMultiplication
