module

public import IdealGeneration.CubicLocalLift
public import IdealGeneration.CubicSupportedKernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Linear decomposition of the local cubic solves into pure, mixed and single-edge terms. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open MvPolynomial CubicNormalExpansion

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

@[simp] theorem kernelCoordinatesEquiv_coefficientLift (C₀ : Fin 4 → K)
    (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    P.kernelCoordinatesEquiv (P.coefficientLift C₀ B z) = (C₀, B, z) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext e
  change -P.offDiagonalLift C₀ B z e.val 1 = z e
  simp [offDiagonalLift, e.property]

/-- The coefficient lift is linear in its independent data. -/
theorem coefficientLift_eq_symm (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) :
    P.coefficientLift C₀ B z = P.kernelCoordinatesEquiv.symm (C₀, B, z) := by
  apply P.kernelCoordinatesEquiv.injective
  simp

/-- The cubic with prescribed pure-normal coefficients and no other free data. -/
def pureCubic (C₀ : Fin 4 → K) : P.coefficientKernel := P.coefficientLift C₀ 0 0

private theorem upperCoefficient_add' (U V : Coefficients K m) (i j : Fin m) (k : Fin 2) :
    upperCoefficient (U + V).2.2.1 (U + V).2.2.2 i j k =
      upperCoefficient U.2.2.1 U.2.2.2 i j k + upperCoefficient V.2.2.1 V.2.2.2 i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h]
  · by_cases hi : i = j <;> simp [upperCoefficient, h, hi]

private theorem upperCoefficient_smul' (r : K) (U : Coefficients K m) (i j : Fin m) (k : Fin 2) :
    upperCoefficient (r • U).2.2.1 (r • U).2.2.2 i j k =
      r * upperCoefficient U.2.2.1 U.2.2.2 i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h, smul_eq_mul]
  · by_cases hi : i = j <;> simp [upperCoefficient, h, hi, smul_eq_mul]

/-- The trace-quadratic part of one normal-linear coefficient is linear in the cubic. -/
def traceALinear (k : Fin 2) : Coefficients K m →ₗ[K] Poly K m where
  toFun U := traceA U k
  map_add' U V := by
    simp only [traceA, traceQuadratic, upperCoefficient_add', map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r U := by
    change traceA (r • U) k = r • traceA U k
    rw [show r • traceA U k = C r * traceA U k by
      simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]]
    simp only [traceA, traceQuadratic, upperCoefficient_smul', map_mul, Finset.mul_sum, ← mul_assoc]

@[simp] theorem traceALinear_apply (k : Fin 2) (U : Coefficients K m) :
    traceALinear k U = traceA U k := rfl

/-- The deterministic lift splits into pure, mixed and independent single-edge cubics. -/
theorem coefficientLift_decompose (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) :
    P.coefficientLift C₀ B z = P.pureCubic C₀ +
      (∑ j, P.mixedCubic j (B j)) + ∑ e, z e • P.edgeCubic e := by
  classical
  apply P.kernelCoordinatesEquiv.injective
  simp only [map_add, map_sum, map_smul, pureCubic, mixedCubic, edgeCubic,
    P.kernelCoordinatesEquiv_coefficientLift]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [Prod.fst_sum]
  · funext i a
    simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, mixedArray]
  · funext e
    simp [Prod.snd_sum, Finset.sum_apply, smul_eq_mul, mul_ite]

/-- Exact normal-linear coefficient formula for an arbitrary local solve. -/
theorem traceA_coefficientLift (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (k : Fin 2) :
    traceA (P.coefficientLift C₀ B z).val k =
      traceA (P.pureCubic C₀).val k +
        (∑ j, X j * ∑ i, C (P.mixedLinear j (B j) i k) * X i) +
        ∑ e, C (z e) * (C (P.edgeLinear e k) * X e.val.val.1 * X e.val.val.2) := by
  let L := (traceALinear k).comp P.coefficientKernel.subtype
  have h := congrArg L (P.coefficientLift_decompose C₀ B z)
  simpa only [map_add, map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
    traceALinear_apply, P.traceA_mixedCubic, P.traceA_edgeCubic, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, L] using h

end IdealGeneration.CubicSupported.Parameters
