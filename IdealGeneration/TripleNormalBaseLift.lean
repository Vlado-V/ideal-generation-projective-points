module

public import IdealGeneration.TripleNormalConic
public import IdealGeneration.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Compatible mixed coefficients of the pure-normal quadratic lifts on the base. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K]

/-- The right sides of the two base equations (A.10). -/
def baseLiftRhs (ω t : K) : Forms K 3 2 →ₗ[K] (Fin 2 → K) where
  toFun Q := ![-thetaPlus ω * eval (sigmaPlus ω t) Q.val,
    -thetaMinus ω * eval (sigmaMinus ω t) Q.val]
  map_add' f g := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' a f := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The mixed coefficient of the lift at one base index. -/
def baseLiftCoefficient (ω t : K) : Forms K 3 2 →ₗ[K] (Fin 3 → K) :=
  (baseLiftMatrix ω t).mulVecLin.comp (baseLiftRhs ω t)

/-- These coefficients solve both normal evaluation equations at the base index. -/
theorem baseLiftCoefficient_solves (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (Q : Forms K 3 2) :
    (baseNormalMatrix ω t).mulVec (baseLiftCoefficient ω t Q) = baseLiftRhs ω t Q := by
  change (baseNormalMatrix ω t) *ᵥ (baseLiftMatrix ω t) *ᵥ baseLiftRhs ω t Q = _
  rw [Matrix.mulVec_mulVec, baseNormalMatrix_mul_lift ω t hω ht, Matrix.one_mulVec]

/-- The lifted quadratic vanishes over the positive base attachment. -/
theorem baseLiftCoefficient_eval_plus (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (Q : Forms K 3 2) :
    eval (thetaPlus ω • sigmaPlus ω t) Q.val +
      (thetaPlus ω • sigmaPlus ω t) ⬝ᵥ baseLiftCoefficient ω t Q = 0 := by
  have h := congrFun (baseLiftCoefficient_solves ω t hω ht Q) 0
  change sigmaPlus ω t ⬝ᵥ baseLiftCoefficient ω t Q =
    -thetaPlus ω * eval (sigmaPlus ω t) Q.val at h
  have he : eval (thetaPlus ω • sigmaPlus ω t) Q.val =
      thetaPlus ω ^ 2 * eval (sigmaPlus ω t) Q.val := by
    change eval (fun i => thetaPlus ω * sigmaPlus ω t i) Q.val = _
    exact homogeneous_eval_scale Q.property (sigmaPlus ω t) (thetaPlus ω)
  rw [he, smul_dotProduct, h, smul_eq_mul]
  ring

/-- The lifted quadratic vanishes over the negative base attachment. -/
theorem baseLiftCoefficient_eval_minus (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (Q : Forms K 3 2) :
    eval (thetaMinus ω • sigmaMinus ω t) Q.val +
      (thetaMinus ω • sigmaMinus ω t) ⬝ᵥ baseLiftCoefficient ω t Q = 0 := by
  have h := congrFun (baseLiftCoefficient_solves ω t hω ht Q) 1
  change sigmaMinus ω t ⬝ᵥ baseLiftCoefficient ω t Q =
    -thetaMinus ω * eval (sigmaMinus ω t) Q.val at h
  have he : eval (thetaMinus ω • sigmaMinus ω t) Q.val =
      thetaMinus ω ^ 2 * eval (sigmaMinus ω t) Q.val := by
    change eval (fun i => thetaMinus ω * sigmaMinus ω t i) Q.val = _
    exact homogeneous_eval_scale Q.property (sigmaMinus ω t) (thetaMinus ω)
  rw [he, smul_dotProduct, h, smul_eq_mul]
  ring

/-- The base part of the lift is a family of local coefficient sections. -/
def baseLiftCoefficients {h : ℕ} (ω : K) (t : Fin h → K) :
    Forms K 3 2 →ₗ[K] (Fin h → Fin 3 → K) :=
  LinearMap.pi fun i => baseLiftCoefficient ω (t i)

/-- Adding base indices keeps every old local coefficient. -/
theorem baseLiftCoefficients_append {h e : ℕ} (ω : K) (t : Fin h → K) (u : Fin e → K)
    (Q : Forms K 3 2) (i : Fin h) :
    baseLiftCoefficients ω (Fin.append t u) Q (i.castAdd e) = baseLiftCoefficients ω t Q i := by
  change baseLiftCoefficient ω (Fin.append t u (i.castAdd e)) Q = baseLiftCoefficient ω (t i) Q
  rw [Fin.append_left]

end IdealGeneration.TripleNormal
