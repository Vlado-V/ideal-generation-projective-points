module

public import IdealGeneration.TripleNormalSupportedExtension
public import IdealGeneration.TripleNormalConic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The twelve new layer columns in the three-normal enlargement. -/

noncomputable section
namespace IdealGeneration.TripleNormal.NewLayerBlock
open MvPolynomial Matrix
open scoped Matrix

variable {K : Type*} [Field K] (h : ℕ)

/-- The new base variables lie between the old base and the layers. -/
def newBaseVariable (b : Fin 3) : Fin (h + 3 + 4) := (b.natAdd h).castAdd 4

/-- The four layer variables follow the enlarged base. -/
def layerVariable (j : Fin 4) : Fin (h + 3 + 4) := j.natAdd (h + 3)

variable (t : Fin 3 → K)

/-- The normal coefficient vector of the product of the new mixed lift by a layer variable. -/
def column (b : Fin 3) (j : Fin 4) (i : Fin 3) : Forms K (h + 3 + 4) 2 :=
  ⟨C (conicVector (t b) i) * (X (newBaseVariable h b) * X (layerVariable h j)),
    ((isHomogeneous_X K _).mul (isHomogeneous_X K _)).C_mul _⟩

/-- Form a linear combination of the twelve vector-valued quadratic columns. -/
def vectorQuadratic : (Fin 4 → Fin 3 → K) →ₗ[K] (Fin 3 → Forms K (h + 3 + 4) 2) where
  toFun c i := ∑ j : Fin 4, ∑ b : Fin 3, c j b • column h t b j i
  map_add' c d := by
    funext i
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext i
    simp [Finset.smul_sum, smul_smul]

@[simp] theorem vectorQuadratic_apply (c : Fin 4 → Fin 3 → K) (i : Fin 3) :
    vectorQuadratic h t c i = ∑ j : Fin 4, ∑ b : Fin 3, c j b • column h t b j i := rfl

/-- Evaluate the three scalar components of a vector-valued quadratic. -/
def vectorEvaluation (x : Fin (h + 3 + 4) → K) :
    (Fin 3 → Forms K (h + 3 + 4) 2) →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i => (evaluationLinear K (h + 3 + 4) 2 x).comp (LinearMap.proj i)

@[simp] theorem vectorEvaluation_apply (x : Fin (h + 3 + 4) → K)
    (f : Fin 3 → Forms K (h + 3 + 4) 2) (i : Fin 3) :
    vectorEvaluation h x f i = eval x (f i).val := rfl

@[simp] theorem eval_column (x : Fin (h + 3 + 4) → K) (b : Fin 3) (j : Fin 4) (i : Fin 3) :
    eval x (column h t b j i).val =
      conicVector (t b) i * (x (newBaseVariable h b) * x (layerVariable h j)) := by
  simp [column]

/-- A zero new-base coordinate annihilates its column on the old trace. -/
@[simp] theorem eval_column_old (x : Fin (h + 4) → K) (b : Fin 3) (j : Fin 4) (i : Fin 3) :
    eval (embedOldTrace x) (column h t b j i).val = 0 := by
  simp [embedOldTrace, newBaseVariable]

/-- The new coordinate points have zero layer coordinates. -/
@[simp] theorem eval_column_coordinate (a b : Fin 3) (j : Fin 4) (i : Fin 3) :
    eval (extensionCoordinate h a) (column h t b j i).val = 0 := by
  simp [extensionCoordinate, layerVariable]

/-- Every free point of the new base has zero layer coordinates. -/
@[simp] theorem eval_column_free (x : Fin (h + 3) → K) (b : Fin 3) (j : Fin 4) (i : Fin 3) :
    eval (extensionFreePoint x) (column h t b j i).val = 0 := by
  simp [extensionFreePoint, layerVariable]

/-- The layer evaluation of one column has precisely one nonzero block. -/
theorem eval_column_layer (ζ : Fin 4 → K) (a j : Fin 4) (b i : Fin 3) :
    eval (extensionLayer h ζ a) (column h t b j i).val =
      if a = j then ζ a * conicVector (t b) i else 0 := by
  by_cases h' : a = j
  · subst j
    simp [extensionLayer, newBaseVariable, layerVariable, mul_comm]
  · simp [extensionLayer, newBaseVariable, layerVariable, h', Ne.symm h']

/-- The columns are zero on the embedded old trace, regardless of its points. -/
theorem vectorQuadratic_old (x : Fin (h + 4) → K) (c : Fin 4 → Fin 3 → K) :
    vectorEvaluation h (embedOldTrace x) (vectorQuadratic h t c) = 0 := by
  funext i
  simp [embedOldTrace, newBaseVariable]

/-- The columns are zero at the three new coordinate points. -/
theorem vectorQuadratic_coordinate (b : Fin 3) (c : Fin 4 → Fin 3 → K) :
    vectorEvaluation h (extensionCoordinate h b) (vectorQuadratic h t c) = 0 := by
  funext i
  simp [extensionCoordinate, layerVariable]

/-- The columns are zero at every free point on the enlarged base. -/
theorem vectorQuadratic_free (x : Fin (h + 3) → K) (c : Fin 4 → Fin 3 → K) :
    vectorEvaluation h (extensionFreePoint x) (vectorQuadratic h t c) = 0 := by
  funext i
  simp [extensionFreePoint, layerVariable]

/-- The conic vectors are the columns of the local evaluation matrix. -/
def conicMatrix : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i b => conicVector (t b) i

theorem conicMatrix_det_ne_zero (ht : Function.Injective t) : (conicMatrix t).det ≠ 0 := by
  have he : (conicMatrix t)ᵀ = Matrix.of ![conicVector (t 0), conicVector (t 1), conicVector (t 2)] := by
    ext b i
    fin_cases b <;> rfl
  rw [← Matrix.det_transpose, he]
  exact conicVector_triple_det_ne_zero _ _ _
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (ht h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (ht h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (ht h))

/-- Actual evaluation of the quadratic columns on the four new layer points. -/
def layerBlock (ζ : Fin 4 → K) : (Fin 4 → Fin 3 → K) →ₗ[K] (Fin 4 → Fin 3 → K) :=
  LinearMap.pi fun j => (vectorEvaluation h (extensionLayer h ζ j)).comp (vectorQuadratic h t)

theorem layerBlock_apply (ζ : Fin 4 → K) (c : Fin 4 → Fin 3 → K) (j : Fin 4) :
    layerBlock h t ζ c j = ζ j • (conicMatrix t).mulVec (c j) := by
  funext i
  change evaluationLinear K (h + 3 + 4) 2 (extensionLayer h ζ j) (vectorQuadratic h t c i) = _
  rw [vectorQuadratic_apply]
  simp only [map_sum, map_smul, evaluationLinear_apply, eval_column_layer]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, conicMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- Distinct conic parameters and nonzero layer heights give all twelve layer values. -/
theorem layerBlock_bijective (ζ : Fin 4 → K) (ht : Function.Injective t) (hζ : ∀ j, ζ j ≠ 0) :
    Function.Bijective (layerBlock h t ζ) := by
  have hM := Matrix.mulVec_injective_of_det_ne_zero (conicMatrix_det_ne_zero t ht)
  have hsurj : Function.Surjective (conicMatrix t).mulVec :=
    LinearMap.surjective_of_injective (f := (conicMatrix t).mulVecLin) hM
  constructor
  · intro c d he
    funext j
    have hj := congrFun he j
    rw [layerBlock_apply, layerBlock_apply] at hj
    apply hM
    simpa [smul_smul, hζ j] using congrArg (fun v : Fin 3 → K => (ζ j)⁻¹ • v) hj
  · intro v
    choose c hc using fun j => hsurj ((ζ j)⁻¹ • v j)
    refine ⟨c, funext fun j => ?_⟩
    rw [layerBlock_apply, hc, smul_smul, mul_inv_cancel₀ (hζ j), one_smul]

end IdealGeneration.TripleNormal.NewLayerBlock
