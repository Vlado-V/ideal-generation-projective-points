module

public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial evaluation along an affine line

The line parameter is an actual univariate polynomial variable.  The lemmas
identify both the value at zero and the normal component of its first
coefficient.
-/

noncomputable section
namespace IdealGeneration.DifferentialLine

variable {K : Type*} [Field K] {ι : Type*} {n : ℕ}

/-- Substitute `y + t v`, retaining the line parameter as an indeterminate. -/
def lineSubstitution (y v : ι → K) :
    MvPolynomial ι K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval
    (fun i => Polynomial.C (y i) + Polynomial.X * Polynomial.C (v i))

@[simp] theorem lineSubstitution_X (y v : ι → K) (i : ι) :
    lineSubstitution y v (MvPolynomial.X i) =
      Polynomial.C (y i) + Polynomial.X * Polynomial.C (v i) := by
  simp [lineSubstitution, MvPolynomial.aeval_def]

@[simp] theorem lineSubstitution_C (y v : ι → K) (c : K) :
    lineSubstitution y v (MvPolynomial.C c) = Polynomial.C c := by
  simp [lineSubstitution]

/-- Specializing the retained parameter gives ordinary affine-line evaluation. -/
theorem eval_lineSubstitution (y v : ι → K) (p : MvPolynomial ι K) (t : K) :
    (lineSubstitution y v p).eval t =
      MvPolynomial.eval (fun i => y i + t * v i) p := by
  change (Polynomial.evalRingHom t)
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (y i) + Polynomial.X * Polynomial.C (v i)) p) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    ext c
    simp
  rw [hc]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, MvPolynomial.eval₂_id]

@[simp] theorem eval_zero_lineSubstitution (y v : ι → K) (p : MvPolynomial ι K) :
    (lineSubstitution y v p).eval 0 = MvPolynomial.eval y p := by
  simpa using eval_lineSubstitution y v p 0

/-- The constant coefficient is evaluation at the initial point. -/
@[simp] theorem coeff_zero_lineSubstitution (y v : ι → K) (p : MvPolynomial ι K) :
    (lineSubstitution y v p).coeff 0 = MvPolynomial.eval y p := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_zero_lineSubstitution]

/-- A coordinate vanishing at the initial point gives the normal first response. -/
theorem coeff_one_coordinate_mul (y v : ι → K) (i : ι)
    (p : MvPolynomial ι K) (hy : y i = 0) :
    (lineSubstitution y v (MvPolynomial.X i * p)).coeff 1 =
      v i * MvPolynomial.eval y p := by
  rw [map_mul, lineSubstitution_X, hy]
  simp only [Polynomial.C_0, zero_add]
  rw [mul_assoc, Polynomial.coeff_X_mul]
  simp

/-- The normal response for the first coordinate convention used by (3.1). -/
theorem coeff_one_normal_mul (y v : Fin (n + 1) → K)
    (p : Poly K (n + 1)) (hy : y 0 = 0) :
    (lineSubstitution y v (MvPolynomial.X 0 * p)).coeff 1 =
      v 0 * MvPolynomial.eval y p :=
  coeff_one_coordinate_mul y v 0 p hy

/-- Remove the constant coefficient and shift all remaining coefficients down. -/
def shiftPolynomial : Polynomial K →ₗ[K] Polynomial K where
  toFun := Polynomial.divX
  map_add' := fun _ _ => Polynomial.divX_add
  map_smul' c p := by
    simp [Polynomial.smul_eq_C_mul]

@[simp] theorem shiftPolynomial_apply (p : Polynomial K) :
    shiftPolynomial p = p.divX := rfl

/-- Actual line evaluation as a linear map on all polynomials. -/
def evalLine (y v : ι → K) (t : K) : MvPolynomial ι K →ₗ[K] K :=
  (Polynomial.leval t).comp (lineSubstitution y v).toLinearMap

@[simp] theorem evalLine_apply (y v : ι → K) (t : K) (p : MvPolynomial ι K) :
    evalLine y v t p = MvPolynomial.eval (fun i => y i + t * v i) p :=
  eval_lineSubstitution y v p t

/-- The first-order quotient of actual line evaluation. -/
def quotientLine (y v : ι → K) (t : K) : MvPolynomial ι K →ₗ[K] K :=
  (Polynomial.leval t).comp (shiftPolynomial.comp (lineSubstitution y v).toLinearMap)

@[simp] theorem quotientLine_apply (y v : ι → K) (t : K) (p : MvPolynomial ι K) :
    quotientLine y v t p = (lineSubstitution y v p).divX.eval t := rfl

@[simp] theorem quotientLine_zero (y v : ι → K) (p : MvPolynomial ι K) :
    quotientLine y v 0 p = (lineSubstitution y v p).coeff 1 := by
  simp [quotientLine_apply, ← Polynomial.coeff_zero_eq_eval_zero]

/-- Exact first-order expansion on the whole polynomial ring. -/
theorem evalLine_expansion (y v : ι → K) (t : K) :
    evalLine y v t = evalLine y v 0 + t • quotientLine y v t := by
  apply LinearMap.ext
  intro p
  exact DeformationMatrix.polynomial_eval_expansion (lineSubstitution y v p) t

/-- Line substitution is linear on each homogeneous degree. -/
def lineForm (y v : Fin n → K) (d : ℕ) : Forms K n d →ₗ[K] Polynomial K :=
  (lineSubstitution y v).toLinearMap.comp (Forms K n d).subtype

@[simp] theorem lineForm_apply (y v : Fin n → K) (d : ℕ) (f : Forms K n d) :
    lineForm y v d f = lineSubstitution y v f.val := rfl

/-- Evaluation along a line depends polynomially on the parameter. -/
theorem lineForm_isPolynomialFamily (y v : Fin n → K) (d : ℕ) :
    IsPolynomialFamily (fun a : Fin 1 → K =>
      (Polynomial.leval (a 0)).comp (lineForm y v d)) := by
  apply isPolynomialFamily_linearMap
  intro f
  exact DeformationMatrix.polynomial_eval_isPolynomialFamily (lineForm y v d f)

/-- Shifting the polynomial coefficients produces the exact first-order remainder. -/
def shiftedLineForm (y v : Fin n → K) (d : ℕ) : Forms K n d →ₗ[K] Polynomial K :=
  shiftPolynomial.comp (lineForm y v d)

@[simp] theorem shiftedLineForm_apply (y v : Fin n → K) (d : ℕ)
    (f : Forms K n d) :
    shiftedLineForm y v d f = (lineForm y v d f).divX := rfl

/-- The shifted line evaluation also depends polynomially on the parameter. -/
theorem shiftedLineForm_isPolynomialFamily (y v : Fin n → K) (d : ℕ) :
    IsPolynomialFamily (fun a : Fin 1 → K =>
      (Polynomial.leval (a 0)).comp (shiftedLineForm y v d)) := by
  apply isPolynomialFamily_linearMap
  intro f
  exact DeformationMatrix.polynomial_eval_isPolynomialFamily (shiftedLineForm y v d f)

/-- Exact first-order expansion for affine-line evaluation on homogeneous forms. -/
theorem lineForm_expansion (y v : Fin n → K) (d : ℕ) (t : K) :
    (Polynomial.leval t).comp (lineForm y v d) =
      (Polynomial.leval 0).comp (lineForm y v d) +
      t • (Polynomial.leval t).comp (shiftedLineForm y v d) := by
  ext f
  exact DeformationMatrix.polynomial_eval_expansion (lineForm y v d f) t

end IdealGeneration.DifferentialLine
