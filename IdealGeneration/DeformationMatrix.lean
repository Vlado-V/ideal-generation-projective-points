module

public import IdealGeneration.RankOpen
public import IdealGeneration.DeformationNormalization
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial matrix evaluation and its first coefficient

The coefficient shift gives an exact first-order expansion of every polynomial
matrix. Its evaluation is a polynomial family of genuine linear maps.
-/

noncomputable section
namespace IdealGeneration.DeformationMatrix

open Polynomial Matrix

variable {k m n : Type*} [Field k] [Fintype n]

/-- A polynomial matrix evaluated as a linear map of coordinate spaces. -/
def evalMap (A : Matrix m n k[X]) (t : k) : (n → k) →ₗ[k] (m → k) :=
  (A.map (Polynomial.eval t)).mulVecLin

@[simp] theorem evalMap_apply (A : Matrix m n k[X]) (t : k) (v : n → k) (i : m) :
    evalMap A t v i = ∑ j, (A i j).eval t * v j := rfl

/-- The polynomial matrix with its coefficients shifted down by one degree. -/
def shifted (A : Matrix m n k[X]) : Matrix m n k[X] := A.map Polynomial.divX

/-- The linear map given by the first coefficient of the matrix. -/
def firstMap (A : Matrix m n k[X]) : (n → k) →ₗ[k] (m → k) := evalMap (shifted A) 0

theorem polynomial_eval_expansion (p : k[X]) (t : k) :
    p.eval t = p.eval 0 + t * p.divX.eval t := by
  have h := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add p)
  simpa [Polynomial.coeff_zero_eq_eval_zero, add_comm] using h.symm

/-- Exact expansion into the value at zero and the shifted family. -/
theorem evalMap_eq_zero_add (A : Matrix m n k[X]) (t : k) :
    evalMap A t = evalMap A 0 + t • evalMap (shifted A) t := by
  ext v i
  simp only [evalMap_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [polynomial_eval_expansion]
  simp only [shifted, Matrix.map_apply]
  ring

/-- At zero the shifted family is the degree-one coefficient map. -/
@[simp] theorem firstMap_apply (A : Matrix m n k[X]) (v : n → k) (i : m) :
    firstMap A v i = ∑ j, (A i j).coeff 1 * v j := by
  simp only [firstMap, evalMap_apply, shifted, Matrix.map_apply,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, zero_add]

/-- The coefficient map is the actual formal derivative at the special parameter. -/
theorem firstMap_eq_derivative (A : Matrix m n k[X]) :
    firstMap A = (A.map (fun p => p.derivative.eval 0)).mulVecLin := by
  ext v i
  simp only [firstMap_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.map_apply, ← IdealGeneration.DeformationNormalization.first_coefficient_eq_derivative]

/-- Regard a univariate polynomial as a polynomial in one coordinate. -/
def polynomialInOneCoordinate (p : k[X]) : MvPolynomial (Fin 1) k :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X 0)

@[simp] theorem eval_polynomialInOneCoordinate (p : k[X]) (a : Fin 1 → k) :
    MvPolynomial.eval a (polynomialInOneCoordinate p) = p.eval (a 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polynomialInOneCoordinate, Polynomial.eval₂_add,
      map_add, Polynomial.eval_add] at *; exact congrArg₂ (· + ·) hp hq
  | monomial r c => simp [polynomialInOneCoordinate]

/-- Univariate polynomial evaluation has polynomial dependence on its parameter. -/
theorem polynomial_eval_isPolynomialFamily (p : k[X]) :
    IsPolynomialFamily (fun a : Fin 1 → k => p.eval (a 0)) := by
  simpa only [eval_polynomialInOneCoordinate] using
    (isPolynomialFamily_eval (polynomialInOneCoordinate p))

/-- Coordinatewise polynomial dependence gives polynomial dependence of a vector. -/
theorem isPolynomialFamily_pi {ι I : Type*} [Fintype I]
    (f : (ι → k) → I → k)
    (hf : ∀ i, IsPolynomialFamily (fun a => f a i)) : IsPolynomialFamily f := by
  classical
  have hterm (i : I) : IsPolynomialFamily (fun a : ι → k =>
      f a i • (Pi.single i 1 : I → k)) :=
    (hf i).smul (isPolynomialFamily_const (Pi.single i 1))
  have hsum := IsPolynomialFamily.sum hterm
  have heq : (fun a : ι → k => ∑ i, f a i • (Pi.single i 1 : I → k)) = f := by
    funext a i
    simp [Pi.single_apply]
  exact heq ▸ hsum

/-- The evaluation maps of an arbitrary polynomial matrix form a polynomial family. -/
theorem evalMap_isPolynomialFamily [Fintype m] (A : Matrix m n k[X]) :
    IsPolynomialFamily (fun a : Fin 1 → k => evalMap A (a 0)) := by
  apply isPolynomialFamily_linearMap
  intro v
  apply isPolynomialFamily_pi
  intro i
  have hterm (j : n) : IsPolynomialFamily (fun a : Fin 1 → k =>
      (A i j).eval (a 0) * v j) := by
    simpa only [smul_eq_mul] using
      (polynomial_eval_isPolynomialFamily (A i j)).smul (isPolynomialFamily_const (v j))
  simpa only [evalMap_apply] using IsPolynomialFamily.sum hterm

/-- Specialize the single parameter variable to the univariate indeterminate. -/
def parameterPolynomial (f : MvPolynomial (Fin 1) k) : k[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) f

/-- Univariate specialization has the same value at every scalar parameter. -/
theorem eval_parameterPolynomial (f : MvPolynomial (Fin 1) k) (t : k) :
    (parameterPolynomial f).eval t = MvPolynomial.eval (fun _ => t) f := by
  change (Polynomial.evalRingHom t)
    (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) f) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id k := by
    ext c
    simp
  rw [hc]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, MvPolynomial.eval₂_id]

/-- Nonvanishing at zero ensures that the univariate parameter polynomial is nonzero. -/
theorem parameterPolynomial_ne_zero (f : MvPolynomial (Fin 1) k)
    (hf : MvPolynomial.eval 0 f ≠ 0) : parameterPolynomial f ≠ 0 := by
  intro hp
  have h := eval_parameterPolynomial f 0
  rw [hp, Polynomial.eval_zero] at h
  exact hf h.symm

/-- A one-parameter polynomial condition nonzero at zero has finitely many zeros. -/
theorem finite_zero_parameters (f : MvPolynomial (Fin 1) k)
    (hf : MvPolynomial.eval 0 f ≠ 0) :
    Set.Finite {t : k | MvPolynomial.eval (fun _ => t) f = 0} := by
  have h := Polynomial.finite_setOfPred_isRoot (parameterPolynomial_ne_zero f hf)
  simpa only [Polynomial.IsRoot, eval_parameterPolynomial] using h

end IdealGeneration.DeformationMatrix
