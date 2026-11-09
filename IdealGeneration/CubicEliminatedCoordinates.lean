module

public import IdealGeneration.CubicMiddleElimination
public import IdealGeneration.CubicNormalExpansion
public import IdealGeneration.CubicUpperSolve

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Normal coefficient equations on the actual supported cubic middle source. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open MvPolynomial AddMonoidAlgebra CubicMiddle CubicNormalExpansion CubicUpperSolve
open QuadraticNormalCoefficients NormalDegree

variable {K : Type*} [Field K] {m f : ℕ} (P : Parameters K m)
variable (free : Fin f → Fin m → K) (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

local notation "Cₚ" => P.toConeConfiguration free

/-- Coefficients of the actual residual cubic at any trace extension of the supported family. -/
def residualCoefficientEquiv : (Cₚ).residualPiece 3 ≃ₗ[K] P.coefficientKernel :=
  (P.actualKernelResidualEquiv free).symm.trans (P.coefficientActualEquiv h₂ h₆).symm

@[simp] theorem residualCoefficientEquiv_polynomial (u : (Cₚ).residualPiece 3) :
    coefficientPolynomial (P.residualCoefficientEquiv free h₂ h₆ u).val = u.val.val := by
  let e := (P.coefficientActualEquiv h₂ h₆).trans (P.actualKernelResidualEquiv free)
  exact congrArg (fun x : (Cₚ).residualPiece 3 => x.val.val) (e.apply_symm_apply u)

/-- Read the supported coefficients in each ambient multiplier slot. -/
abbrev sourceCoefficient (u : ResidualSource Cₚ) (i : Fin (2 + m)) : Coefficients K m :=
  (P.residualCoefficientEquiv free h₂ h₆ (u i)).val

/-- The actual residual multiplication written in the nested polynomial ring. -/
def sourceNestedProduct (u : ResidualSource Cₚ) : Nested K m :=
  let A := P.sourceCoefficient free h₂ h₆ u
  nestedProduct (A (Fin.castAdd m 0)) (A (Fin.castAdd m 1)) (fun i => A (Fin.natAdd 2 i))

@[simp] theorem flatten_sourceNestedProduct (u : ResidualSource Cₚ) :
    flatten K m (P.sourceNestedProduct free h₂ h₆ u) = (residualFormMap Cₚ u).val := by
  rw [sourceNestedProduct, flatten_nestedProduct]
  change _ = ∑ i : Fin (2 + m), X i * (u i).val.val
  simp only [sourceCoefficient, residualCoefficientEquiv_polynomial,
    Fin.sum_univ_add, Fin.sum_univ_two]

private theorem flatten_normalLinears (a b : Poly K m) :
    flatten K m (normalMonomial 1 0 a + normalMonomial 0 1 b) =
      X (Fin.castAdd m 0) * coneExtend K 2 m a +
      X (Fin.castAdd m 1) * coneExtend K 2 m b := by
  simp [normalMonomial_eq, mul_comm]

private theorem nestedProduct_eq_normalLinears (U V : Coefficients K m)
    (W : Fin m → Coefficients K m)
    (h₄ : productNormal4 U V = 0) (h₃ : productNormal3 U V W = 0)
    (h₂' : productNormal2 U V W = 0) :
    nestedProduct U V W =
      normalMonomial 1 0 (productNormal1 W 0) + normalMonomial 0 1 (productNormal1 W 1) := by
  simp [nestedProduct_eq, h₄, h₃, h₂', normalMonomial]

private theorem separate_normalLinears (U V : Coefficients K m) (W : Fin m → Coefficients K m)
    (a b : Poly K m)
    (h : nestedProduct U V W = normalMonomial 1 0 a + normalMonomial 0 1 b) :
    productNormal4 U V = 0 ∧ productNormal3 U V W = 0 ∧ productNormal2 U V W = 0 ∧
      productNormal1 W 0 = a ∧ productNormal1 W 1 = b := by
  have hc (p q : ℕ) := congrArg (fun F : Nested K m => coeff F (normalExponent p q)) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    apply C_injective (Fin m) K
    fin_cases i
    · simpa [nestedProduct_eq] using hc 4 0
    · simpa [nestedProduct_eq] using hc 3 1
    · simpa [nestedProduct_eq] using hc 2 2
    · simpa [nestedProduct_eq] using hc 1 3
    · simpa [nestedProduct_eq] using hc 0 4
  · funext i
    fin_cases i
    · simpa [nestedProduct_eq] using hc 3 0
    · simpa [nestedProduct_eq] using hc 2 1
    · simpa [nestedProduct_eq] using hc 1 2
    · simpa [nestedProduct_eq] using hc 0 3
  · funext i
    fin_cases i
    · simpa [nestedProduct_eq] using hc 2 0
    · simpa [nestedProduct_eq] using hc 1 1
    · simpa [nestedProduct_eq] using hc 0 2
  · simpa [nestedProduct_eq] using hc 1 0
  · simpa [nestedProduct_eq] using hc 0 1

private theorem sourceNestedProduct_eliminated (u : eliminatedSource Cₚ) :
    P.sourceNestedProduct free h₂ h₆ u.val =
      normalMonomial 1 0 (phi Cₚ u 0).val + normalMonomial 0 1 (phi Cₚ u 1).val := by
  apply (flatten K m).injective
  rw [flatten_sourceNestedProduct, flatten_normalLinears, ← phi_reconstruct Cₚ u]
  simp only [normalLinearProduct_val, Fin.sum_univ_two]

/-- Vanishing of the upper blocks is exactly membership in the actual eliminated source. -/
theorem mem_eliminatedSource_iff_upper (u : ResidualSource Cₚ) :
    let A := P.sourceCoefficient free h₂ h₆ u
    let U := A (Fin.castAdd m 0)
    let V := A (Fin.castAdd m 1)
    let W := fun i => A (Fin.natAdd 2 i)
    u ∈ eliminatedSource Cₚ ↔
      productNormal4 U V = 0 ∧ productNormal3 U V W = 0 ∧ productNormal2 U V W = 0 := by
  dsimp only
  constructor
  · intro hu
    obtain ⟨h4, h3, h2, _, _⟩ := separate_normalLinears _ _ _ _ _
      (P.sourceNestedProduct_eliminated free h₂ h₆ ⟨u, hu⟩)
    exact ⟨h4, h3, h2⟩
  · rintro ⟨h4, h3, h2⟩
    have h := congrArg (flatten K m) (nestedProduct_eq_normalLinears _ _ _ h4 h3 h2)
    change flatten K m (P.sourceNestedProduct free h₂ h₆ u) = _ at h
    rw [flatten_sourceNestedProduct, flatten_normalLinears] at h
    rw [mem_eliminatedSource, h]
    apply IsWeightedHomogeneous.add
    · simpa using (isWeightedHomogeneous_X (R := K) (normalWeight 2 m) (Fin.castAdd m 0)).mul
        (coneExtend_weighted K 2 m _)
    · simpa using (isWeightedHomogeneous_X (R := K) (normalWeight 2 m) (Fin.castAdd m 1)).mul
        (coneExtend_weighted K 2 m _)

/-- The actual `Φ` has exactly the two trace-cubic coefficients of the lower block. -/
theorem phi_eq_productNormal1 (u : eliminatedSource Cₚ) (k : Fin 2) :
    (phi Cₚ u k).val =
      productNormal1 (fun i => P.sourceCoefficient free h₂ h₆ u.val (Fin.natAdd 2 i)) k := by
  obtain ⟨_, _, _, h0, h1⟩ := separate_normalLinears _ _ _ _ _
    (P.sourceNestedProduct_eliminated free h₂ h₆ u)
  fin_cases k
  · exact h0.symm
  · exact h1.symm

end IdealGeneration.CubicSupported.Parameters
