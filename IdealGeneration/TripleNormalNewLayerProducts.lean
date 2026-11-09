module

public import IdealGeneration.TripleNormalNewLayerBlock
public import IdealGeneration.TripleNormalSupportedQuadrics
public import IdealGeneration.TripleNormalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Identify the layer columns with actual products of the new residual quadrics. -/

noncomputable section
namespace IdealGeneration.TripleNormal.NewLayerBlock
open MvPolynomial NormalDegree SupportedQuadrics

variable {K : Type*} [Field K] {h p q : ℕ}

/-- The linear trace coefficient of the new mixed direction. -/
def newMixedColumn (u : Fin 3 → K) (b i : Fin 3) : Forms K (h + 3 + 4) 1 :=
  ⟨C (conicVector (u b) i) * X (newBaseVariable h b), isHomogeneous_C_mul_X _ _⟩

/-- A new conic direction requires no layer correction in the actual lift. -/
theorem newMixedForm_polynomial (ω : K) (t : Fin h → K) (u : Fin 3 → K)
    (n : Layer.Normals K) (ζ : Layer.Heights K) (hh : 6 ≤ h) (b : Fin 3) :
    (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
      (0, Pi.single (b.natAdd h) 1)).val =
      X ((newBaseVariable h b).natAdd 3) *
        pureExtend K 3 (h + 3 + 4) (Layer.normalForm (conicVector (u b))).val := by
  let A : Fin (h + 3) → Fin 3 → K := Pi.single (b.natAdd h) (conicVector (u b))
  have hA : mixedCoefficients ω (Fin.append t u) (0, Pi.single (b.natAdd h) 1) = A := by
    funext i
    by_cases hi : i = b.natAdd h
    · subst i
      simp [A]
    · simp [A, Pi.single_eq_of_ne hi]
  have hcorr : Layer.correction n ζ (Layer.baseSupport K (h + 3)) (0, A) = 0 := by
    apply Layer.correction_eq_zero_of_support n ζ _ A
    · exact Layer.baseSupport_eq_zero
    · intro i hi
      have hn : i ≠ b.natAdd h := by
        intro he
        subst i
        change h + b.val < 6 at hi
        omega
      change (Pi.single (b.natAdd h) (conicVector (u b)) : Fin (h + 3) → Fin 3 → K) i = 0
      simp [hn]
  rw [liftForm_apply, hA, quadratic_eq_coefficientQuadratic, hcorr]
  simp only [coefficientQuadratic, map_zero, zero_add, traceLinearProduct_val]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Pi.zero_apply, map_zero, Submodule.coe_zero, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single (b.natAdd h)]
  · simp [A, newBaseVariable]
  · intro i _ hi
    simp [A, Pi.single_eq_of_ne hi]
  · simp

/-- Forgetting the new base coordinates kills this entire mixed quadric. -/
theorem restrict_newMixedForm (ω : K) (t : Fin h → K) (u : Fin 3 → K)
    (n : Layer.Normals K) (ζ : Layer.Heights K) (hh : 6 ≤ h) (b : Fin 3) :
    extensionAmbientRestrictionForm h 2
      (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
        (0, Pi.single (b.natAdd h) 1)) = 0 := by
  apply Subtype.ext
  change extensionAmbientRestriction h
    (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
      (0, Pi.single (b.natAdd h) 1)).val = 0
  rw [newMixedForm_polynomial ω t u n ζ hh b, map_mul]
  simp [newBaseVariable]

/-- The new mixed quadric is the actual normal-linear product with its conic coefficient. -/
theorem newMixedForm_eq_normalLinearProduct (ω : K) (t : Fin h → K) (u : Fin 3 → K)
    (n : Layer.Normals K) (ζ : Layer.Heights K) (hh : 6 ≤ h) (b : Fin 3) :
    liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
      (0, Pi.single (b.natAdd h) 1) =
      normalLinearProduct K 3 (h + 3 + 4) 1 (newMixedColumn u b) := by
  apply Subtype.ext
  rw [newMixedForm_polynomial ω t u n ζ hh b, normalLinearProduct_val]
  simp only [pureExtend, Layer.normalForm, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_mul, rename_C, rename_X, coneExtend, newMixedColumn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (C : ConeConfiguration K 3 (h + 3 + 4) p q)
  (ω : K) (t : Fin h → K) (u : Fin 3 → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
  (points : PointPattern C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)))
  (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, Fin.append t u i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)

local notation "H" => mixedEquiv C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)) points hω ht hdet hζ

/-- The actual mixed kernel generator over a new base coordinate is exactly its
conic normal direction times that trace coordinate. -/
theorem mixedEquiv_newBase_form (hh : 6 ≤ h) (b : Fin 3) :
    (H (Pi.single (b.natAdd h) 1)).val.val =
      normalLinearProduct K 3 (h + 3 + 4) 1 (newMixedColumn u b) := by
  rw [mixedEquiv_form, newMixedForm_eq_normalLinearProduct ω t u n ζ hh]

/-- The displayed quadratic column is the normal coefficient of the actual
product by the corresponding layer variable. -/
theorem mixedEquiv_layerProduct (hh : 6 ≤ h) (b : Fin 3) (j : Fin 4) :
    X ((layerVariable h j).natAdd 3) * (H (Pi.single (b.natAdd h) 1)).val.val.val =
      (normalLinearProduct K 3 (h + 3 + 4) 2 (column h u b j)).val := by
  rw [mixedEquiv_newBase_form C ω t u n ζ points hω ht hdet hζ hh b,
    normalLinearProduct_val, normalLinearProduct_val]
  simp only [newMixedColumn, column, coneExtend, map_mul, rename_C, rename_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One actual reduced-source column is the new mixed generator times a layer variable. -/
def layerColumnSource (b : Fin 3) (j : Fin 4) : Fin (h + 3 + 4) → MixedKernel C :=
  Pi.single (layerVariable h j) (H (Pi.single (b.natAdd h) 1))

theorem mixedCoefficient_layerColumnSource (hh : 6 ≤ h) (b : Fin 3) (j : Fin 4) :
    mixedCoefficient C (layerColumnSource C ω t u n ζ points hω ht hdet hζ b j) =
      column h u b j := by
  have hp : (mixedProduct C (layerColumnSource C ω t u n ζ points hω ht hdet hζ b j)).val =
      normalLinearProduct K 3 (h + 3 + 4) 2 (column h u b j) := by
    apply Subtype.ext
    rw [mixedProduct_val, Finset.sum_eq_single (layerVariable h j)]
    · simpa only [layerColumnSource, Pi.single_eq_same] using
        mixedEquiv_layerProduct C ω t u n ζ points hω ht hdet hζ hh b j
    · intro i _ hi
      simp [layerColumnSource, Pi.single_eq_of_ne hi]
    · simp
  change linearCoefficientMap K 3 (h + 3 + 4) 2
    (mixedProduct C (layerColumnSource C ω t u n ζ points hω ht hdet hζ b j)).val = _
  rw [hp, linearCoefficientMap_product]

/-- The entire new layer block is supplied by actual mixed products. -/
def layerMixedSource : (Fin 4 → Fin 3 → K) →ₗ[K] (Fin (h + 3 + 4) → MixedKernel C) where
  toFun c := ∑ j : Fin 4, ∑ b : Fin 3,
    c j b • layerColumnSource C ω t u n ζ points hω ht hdet hζ b j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem mixedCoefficient_layerMixedSource (hh : 6 ≤ h) (c : Fin 4 → Fin 3 → K) :
    mixedCoefficient C (layerMixedSource C ω t u n ζ points hω ht hdet hζ c) =
      vectorQuadratic h u c := by
  change mixedCoefficient C (∑ j : Fin 4, ∑ b : Fin 3,
    c j b • layerColumnSource C ω t u n ζ points hω ht hdet hζ b j) = _
  rw [map_sum]
  funext i
  simp only [map_sum, map_smul, mixedCoefficient_layerColumnSource C ω t u n ζ points hω ht hdet hζ hh,
    Finset.sum_apply, Pi.smul_apply, vectorQuadratic_apply]

/-- These directions have no compatible normal triple, so their contribution
to the reduced coefficient map is exactly the new layer block. -/
theorem reducedCoefficient_layerMixedSource (hh : 6 ≤ h) (c : Fin 4 → Fin 3 → K)
    (L : Forms K 3 2 →ₗ[K] C.residualPiece 2) :
    reducedCoefficient C L (0, layerMixedSource C ω t u n ζ points hω ht hdet hζ c) =
      vectorQuadratic h u c := by
  change coefficientMap C L 0 + mixedCoefficient C
    (layerMixedSource C ω t u n ζ points hω ht hdet hζ c) = _
  rw [map_zero, zero_add, mixedCoefficient_layerMixedSource C ω t u n ζ points hω ht hdet hζ hh]

end IdealGeneration.TripleNormal.NewLayerBlock
