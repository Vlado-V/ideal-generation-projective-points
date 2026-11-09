module

public import IdealGeneration.QuadraticFlagLiftWitness
public import IdealGeneration.QuadraticLinearForms

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The base correction for the untouched pairs in (A.5). -/

noncomputable section
namespace IdealGeneration.QuadraticElimination.Untouched
open MvPolynomial QuadraticFlag

variable {K I J : Type*} [Field K]

/-- A linear form supported only on the base variables. -/
def baseForm [Fintype I] : (I → K) →ₗ[K] MvPolynomial (I ⊕ J) K :=
  (rename (R := K) (Sum.inl : I → I ⊕ J)).toLinearMap.comp linearPolynomialLinearMap

/-- A linear form supported only on the layer variables. -/
def layerForm [Fintype J] : (J → K) →ₗ[K] MvPolynomial (I ⊕ J) K :=
  (rename (R := K) (Sum.inr : J → I ⊕ J)).toLinearMap.comp linearPolynomialLinearMap

theorem baseForm_apply [Fintype I] (v : I → K) :
    baseForm (J := J) v = ∑ i, C (v i) * X (Sum.inl i) := by
  simp [baseForm, linearPolynomial]

theorem layerForm_apply [Fintype J] (v : J → K) :
    layerForm (I := I) v = ∑ j, C (v j) * X (Sum.inr j) := by
  simp [layerForm, linearPolynomial]

variable [Fintype I] [Fintype J]

theorem linearPolynomial_sum_elim (v : I → K) (w : J → K) :
    linearPolynomial (Sum.elim v w) = baseForm v + layerForm w := by
  simp [linearPolynomial, baseForm_apply, layerForm_apply]

/-- The product of one mixed generator by a trace form. -/
def generatorProduct (c : I → K) (a b : I → J → K) (i : I)
    (f : MvPolynomial (I ⊕ J) K) :
    MvPolynomial (I ⊕ J) K × MvPolynomial (I ⊕ J) K :=
  (firstGenerator a i * f, secondGenerator c b i * f)

theorem generatorProduct_mem_mixedImage (c : I → K) (a b : I → J → K) (i : I)
    (f : MvPolynomial (I ⊕ J) K) (hf : f.IsHomogeneous 1) :
    generatorProduct c a b i f ∈ mixedImage c a b := by
  classical
  let v : I ⊕ J → K := fun j => eval (coordinatePoint j) f
  let L : I → I ⊕ J → K := fun k => if k = i then v else 0
  have hv : linearPolynomial v = f := linearPolynomial_eval_coordinate_of_homogeneous f hf
  have hsum (g : I → MvPolynomial (I ⊕ J) K) :
      (∑ k, g k * linearPolynomial (L k)) = g i * f := by
    rw [Finset.sum_eq_single i]
    · simp [L, hv]
    · intro k _ hk
      simp [L, hk, linearPolynomial]
    · simp
  exact ⟨L, Prod.ext (hsum (firstGenerator a)) (hsum (secondGenerator c b))⟩

end IdealGeneration.QuadraticElimination.Untouched

namespace IdealGeneration.QuadraticElimination.QuadraticLiftParameters
open MvPolynomial QuadraticFlag Untouched

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable (D : QuadraticLiftParameters K P J)

/-- The base variable for a paired index. -/
def y (i : P × Bool) : MvPolynomial ((P × Bool) ⊕ J) K := X (Sum.inl i)

omit [Fintype P] in
theorem firstGenerator_eq (i : P × Bool) :
    firstGenerator D.firstCorrection i = y (J := J) i + layerForm (D.firstCorrection i) := by
  rw [layerForm_apply]
  rfl

omit [Fintype P] in
theorem secondGenerator_eq (i : P × Bool) :
    secondGenerator D.slope D.secondCorrection i =
      C (D.slope i) * y (J := J) i + layerForm (D.secondCorrection i) := by
  rw [layerForm_apply]
  rfl

omit [Fintype P] in
theorem firstGenerator_untouched (i : P × Bool) (hi : i.1 ≠ D.distinguishedPair) :
    firstGenerator D.firstCorrection i = y (J := J) i := by
  rw [D.firstGenerator_eq i]
  have ha : D.firstCorrection i = 0 := by
    funext j
    exact congrArg Prod.fst (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair
      D.normal₀ D.normal₁ i j hi)
  simp [ha]

omit [Fintype P] in
theorem secondGenerator_untouched (i : P × Bool) (hi : i.1 ≠ D.distinguishedPair) :
    secondGenerator D.slope D.secondCorrection i = C (D.slope i) * y (J := J) i := by
  rw [D.secondGenerator_eq i]
  have hb : D.secondCorrection i = 0 := by
    funext j
    exact congrArg Prod.snd (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair
      D.normal₀ D.normal₁ i j hi)
  simp [hb]

/-- The two combinations are `(K₁+cK₂)` and `(K₂+cK₃)`. -/
def liftCombination (F : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (c : K) (r : Fin 2) : MvPolynomial ((P × Bool) ⊕ J) K :=
  F r.castSucc + c • F r.succ

/-- The base term of the normalized combination is a divided difference in the slopes. -/
def baseWeight (r : Fin 2) (k : P × Bool) : K :=
  if r = 0 then D.baseHeight k * D.slope k else -D.baseHeight k

omit [Fintype P] [Fintype J] in
theorem baseCoefficient_combination (i k : P × Bool) (r : Fin 2) :
    D.baseCoefficient r.castSucc k + D.slope i * D.baseCoefficient r.succ k =
      D.baseWeight r k * (D.slope k - D.slope i) := by
  fin_cases r <;> simp [baseWeight, QuadraticLiftParameters.baseCoefficient, normalBasisValue] <;> ring

/-- The first layer coefficient of the two combined lifts. -/
def combinedFirst (i : P × Bool) (r : Fin 2) : J → K :=
  fun j => (D.layerCoefficients r.castSucc j).1 + D.slope i * (D.layerCoefficients r.succ j).1

/-- The second layer coefficient of the two combined lifts. -/
def combinedSecond (i : P × Bool) (r : Fin 2) : J → K :=
  fun j => (D.layerCoefficients r.castSucc j).2 + D.slope i * (D.layerCoefficients r.succ j).2

/-- The scalar coefficient vector of the base contribution. -/
def combinedBase (i : P × Bool) (r : Fin 2) : P × Bool → K :=
  fun k => D.baseWeight r k * (D.slope k - D.slope i)

theorem firstLift_eq_layerForm (k : Fin 3) :
    D.firstLift k = layerForm (fun j => (D.layerCoefficients k j).1) := by
  rw [firstLift, linearPolynomial_sum_elim]
  change baseForm (0 : P × Bool → K) + _ = _
  simp

theorem secondLift_eq_forms (k : Fin 3) :
    D.secondLift k = baseForm (D.baseCoefficient k) +
      layerForm (fun j => (D.layerCoefficients k j).2) :=
  linearPolynomial_sum_elim _ _

theorem firstLift_combination (i : P × Bool) (r : Fin 2) :
    liftCombination D.firstLift (D.slope i) r = layerForm (D.combinedFirst i r) := by
  rw [liftCombination, D.firstLift_eq_layerForm, D.firstLift_eq_layerForm]
  change _ = layerForm ((fun j => (D.layerCoefficients r.castSucc j).1) +
    D.slope i • (fun j => (D.layerCoefficients r.succ j).1))
  rw [map_add, map_smul]

theorem secondLift_combination (i : P × Bool) (r : Fin 2) :
    liftCombination D.secondLift (D.slope i) r =
      baseForm (D.combinedBase i r) + layerForm (D.combinedSecond i r) := by
  have hb : D.baseCoefficient r.castSucc + D.slope i • D.baseCoefficient r.succ =
      D.combinedBase i r := by
    funext k
    exact D.baseCoefficient_combination i k r
  rw [liftCombination, D.secondLift_eq_forms, D.secondLift_eq_forms, ← hb]
  change _ = _ + layerForm ((fun j => (D.layerCoefficients r.castSucc j).2) +
    D.slope i • (fun j => (D.layerCoefficients r.succ j).2))
  simp only [map_add, map_smul, smul_add]
  abel

/-- The first layer offset introduced by clearing the base quadratics. -/
def offsetFirst (r : Fin 2) : J → K := ∑ k, D.baseWeight r k • D.firstCorrection k

/-- The second layer offset introduced by clearing the base quadratics. -/
def offsetSecond (r : Fin 2) : J → K := ∑ k, D.baseWeight r k • D.secondCorrection k

/-- The base correction is an explicit sum of mixed-generator products. -/
def baseCorrectionPair (i : P × Bool) (r : Fin 2) :
    MvPolynomial ((P × Bool) ⊕ J) K × MvPolynomial ((P × Bool) ⊕ J) K :=
  ∑ k, D.baseWeight r k •
    (generatorProduct D.slope D.firstCorrection D.secondCorrection i (y k) -
      generatorProduct D.slope D.firstCorrection D.secondCorrection k (y i))

theorem baseCorrectionPair_mem (i : P × Bool) (r : Fin 2) :
    D.baseCorrectionPair i r ∈ mixedImage D.slope D.firstCorrection D.secondCorrection := by
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  apply Submodule.sub_mem <;> apply generatorProduct_mem_mixedImage <;>
    exact isHomogeneous_X K _

theorem baseCorrectionPair_fst (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    (D.baseCorrectionPair i r).1 = -y i * layerForm (D.offsetFirst r) := by
  simp only [baseCorrectionPair, Prod.fst_sum, Prod.smul_fst, Prod.fst_sub, generatorProduct]
  rw [D.firstGenerator_untouched i hi]
  simp only [D.firstGenerator_eq, offsetFirst, map_sum, map_smul]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem baseCorrectionPair_snd (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    (D.baseCorrectionPair i r).2 =
      -y i * (baseForm (D.combinedBase i r) + layerForm (D.offsetSecond r)) := by
  simp only [baseCorrectionPair, Prod.snd_sum, Prod.smul_snd, Prod.snd_sub, generatorProduct]
  rw [D.secondGenerator_untouched i hi]
  simp only [D.secondGenerator_eq, combinedBase, baseForm_apply, offsetSecond, map_sum, map_smul]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [y, map_mul, map_sub]
  ring

/-- The surviving layer coefficient vector in the first component. -/
def clearedFirst (i : P × Bool) (r : Fin 2) : J → K :=
  -D.combinedFirst i r + D.offsetFirst r

/-- The surviving layer coefficient vector in the second component. -/
def clearedSecond (i : P × Bool) (r : Fin 2) : J → K :=
  -D.combinedSecond i r + D.offsetSecond r

/-- The two raw eliminated pairs for the untouched mixed generator. -/
def rawPair (i : P × Bool) (r : Fin 2) :
    MvPolynomial ((P × Bool) ⊕ J) K × MvPolynomial ((P × Bool) ⊕ J) K :=
  (-y i * liftCombination D.firstLift (D.slope i) r,
    -y i * liftCombination D.secondLift (D.slope i) r)

/-- Clearing the base terms leaves a product of `y_i` with layer-only forms. -/
theorem rawPair_base_clearing (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    D.rawPair i r = D.baseCorrectionPair i r +
      (y i * layerForm (D.clearedFirst i r), y i * layerForm (D.clearedSecond i r)) := by
  apply Prod.ext
  · simp only [rawPair, Prod.fst_add, D.firstLift_combination,
      D.baseCorrectionPair_fst i r hi, clearedFirst, map_add, map_neg]
    ring
  · simp only [rawPair, Prod.snd_add, D.secondLift_combination,
      D.baseCorrectionPair_snd i r hi, clearedSecond, map_add, map_neg]
    ring

/-- Multiplication of a mixed generator by either normal variable contributes
no pure normal cubic. -/
def untouchedOmega (i : P × Bool) (r : Fin 2) :
    Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K)) := by
  classical
  let h : P × Bool → K := Pi.single i 1
  by_cases hr : r = 0
  · refine ⟨((0, h), (0, 0)), ?_⟩
    change normalCubicMap (0 : (Fin 3 → K) × (Fin 3 → K)) = 0
    exact normalCubicMap.map_zero
  · refine ⟨((0, 0), (0, h)), ?_⟩
    change normalCubicMap (0 : (Fin 3 → K) × (Fin 3 → K)) = 0
    exact normalCubicMap.map_zero

/-- The two actual `φ` values used in (A.5) are the raw pairs above. -/
theorem phi_untouchedOmega (i : P × Bool) (r : Fin 2) (hi : i.1 ≠ D.distinguishedPair) :
    phi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
      (secondKernelMap D.slope D.secondCorrection) (untouchedOmega (K := K) i r) =
      D.rawPair i r := by
  classical
  fin_cases r <;> apply Prod.ext <;>
    simp [phi, prePhi, untouchedOmega, lowerPart, firstKernelMap, secondKernelMap,
      D.firstGenerator_untouched i hi, D.secondGenerator_untouched i hi,
      rawPair, liftCombination, Algebra.smul_def] <;> ring

end IdealGeneration.QuadraticElimination.QuadraticLiftParameters
