module

public import IdealGeneration.CubicSupportedCoordinates
public import IdealGeneration.QuadraticNormalCoefficients
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The supported cubic in the polynomial ring over its trace coordinates. -/

noncomputable section

namespace IdealGeneration.CubicNormalExpansion

open MvPolynomial CubicSupported QuadraticNormalCoefficients

/-- The two normal variables over the trace polynomial ring. -/
abbrev Nested (K : Type*) [Field K] (m : ℕ) := MvPolynomial Bool (Poly K m)

/-- The normal coordinates come first, followed by the trace coordinates. -/
def variableEquiv (m : ℕ) : Bool ⊕ Fin m ≃ Fin (2 + m) :=
  (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl (Fin m))).trans finSumFinEquiv

@[simp] theorem variableEquiv_false (m : ℕ) :
    variableEquiv m (.inl false) = Fin.castAdd m 0 := rfl

@[simp] theorem variableEquiv_true (m : ℕ) :
    variableEquiv m (.inl true) = Fin.castAdd m 1 := rfl

@[simp] theorem variableEquiv_trace (m : ℕ) (i : Fin m) :
    variableEquiv m (.inr i) = Fin.natAdd 2 i := rfl

variable (K : Type*) [Field K] (m : ℕ)

/-- Flatten the nested polynomial ring into the actual normal/trace coordinates. -/
def flatten : Nested K m ≃ₐ[K] Poly K (2 + m) :=
  (sumAlgEquiv K Bool (Fin m)).symm.trans (renameEquiv K (variableEquiv m))

@[simp] theorem flatten_X_false : flatten K m (X false) = X (Fin.castAdd m 0) := by
  simp [flatten]

@[simp] theorem flatten_X_true : flatten K m (X true) = X (Fin.castAdd m 1) := by
  simp [flatten]

@[simp] theorem flatten_C (p : Poly K m) :
    flatten K m (C p) = coneExtend K 2 m p := by
  let embed : Poly K m →ₐ[K] Nested K m := IsScalarTower.toAlgHom K _ _
  have h : (flatten K m).toAlgHom.comp embed = coneExtend K 2 m := by
    apply MvPolynomial.algHom_ext
    intro i
    change flatten K m (C (X i)) = coneExtend K 2 m (X i)
    simp [flatten]
  exact congrArg (fun f : Poly K m →ₐ[K] Poly K (2 + m) => f p) h

variable {K m}

/-- The trace-linear coefficient of one quadratic normal monomial. -/
def traceB (u : Coefficients K m) (q : Fin 3) : Poly K m :=
  ∑ i, C (u.2.1 i q) * X i

/-- The trace-quadratic coefficient of one linear normal monomial. -/
def traceA (u : Coefficients K m) (k : Fin 2) : Poly K m :=
  traceQuadratic (fun i j => C (upperCoefficient u.2.2.1 u.2.2.2 i j k)) X

@[simp] theorem coneExtend_traceB (u : Coefficients K m) (q : Fin 3) :
    coneExtend K 2 m (traceB u q) =
      ∑ i, C (u.2.1 i q) * X (Fin.natAdd 2 i) := by
  simp [traceB, coneExtend, map_sum]

@[simp] theorem coneExtend_traceA (u : Coefficients K m) (k : Fin 2) :
    coneExtend K 2 m (traceA u k) =
      traceQuadratic (fun i j => upperCoefficient (fun i l => C (u.2.2.1 i l))
        (fun e l => C (u.2.2.2 e l)) i j k) (fun i => X (Fin.natAdd 2 i)) := by
  simp only [traceA, traceQuadratic, coneExtend, map_sum, map_mul, rename_C, rename_X]
  simp only [map_upperCoefficient]

/-- The nine normal monomials of the supported cubic, with their trace coefficients. -/
def nestedCubic (u : Coefficients K m) : Nested K m :=
  normalMonomial 3 0 (C (u.1 0)) + normalMonomial 2 1 (C (u.1 1)) +
  normalMonomial 1 2 (C (u.1 2)) + normalMonomial 0 3 (C (u.1 3)) +
  normalMonomial 2 0 (traceB u 0) + normalMonomial 1 1 (traceB u 1) +
  normalMonomial 0 2 (traceB u 2) + normalMonomial 1 0 (traceA u 0) +
  normalMonomial 0 1 (traceA u 1)

/-- The nested expression represents the actual supported polynomial. -/
@[simp] theorem flatten_nestedCubic (u : Coefficients K m) :
    flatten K m (nestedCubic u) = coefficientPolynomial u := by
  let s : Poly K (2 + m) := X (Fin.castAdd m 0)
  let t : Poly K (2 + m) := X (Fin.castAdd m 1)
  let y : Fin m → Poly K (2 + m) := fun i => X (Fin.natAdd 2 i)
  have hC (r : K) : coneExtend K 2 m (C r) = C r := by simp [coneExtend]
  have hB : coneExtend K 2 m (traceB u 0) * s ^ 2 +
      coneExtend K 2 m (traceB u 1) * s * t + coneExtend K 2 m (traceB u 2) * t ^ 2 =
      ∑ i, y i * normalQuadratic (fun q => C (u.2.1 i q)) s t := by
    simp only [coneExtend_traceB, Finset.sum_mul, ← Finset.sum_add_distrib, normalQuadratic]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [nestedCubic, normalMonomial_eq, map_add, map_mul, map_pow, flatten_C,
    flatten_X_false, flatten_X_true, pow_zero, pow_one, mul_one, hC, coneExtend_traceA,
    coefficientPolynomial_apply, polynomial, cubicValue, normalCubic]
  rw [← hB]
  ring

/-- Multiplication by the two normal coordinates and by all trace coordinates. -/
def nestedProduct (U V : Coefficients K m) (W : Fin m → Coefficients K m) : Nested K m :=
  X false * nestedCubic U + X true * nestedCubic V + ∑ i, C (X i) * nestedCubic (W i)

/-- The nested multiplication is the actual polynomial multiplication. -/
@[simp] theorem flatten_nestedProduct (U V : Coefficients K m) (W : Fin m → Coefficients K m) :
    flatten K m (nestedProduct U V W) =
      X (Fin.castAdd m 0) * coefficientPolynomial U +
      X (Fin.castAdd m 1) * coefficientPolynomial V +
      ∑ i, X (Fin.natAdd 2 i) * coefficientPolynomial (W i) := by
  simp [nestedProduct, map_sum]

/-- The scalar coefficients of the five normal quartic monomials. -/
def productNormal4 (U V : Coefficients K m) : Fin 5 → K :=
  ![U.1 0, U.1 1 + V.1 0, U.1 2 + V.1 1, U.1 3 + V.1 2, V.1 3]

/-- The trace-linear coefficients of the four normal cubic monomials. -/
def productNormal3 (U V : Coefficients K m) (W : Fin m → Coefficients K m)
    (q : Fin 4) : Poly K m :=
  ![traceB U 0, traceB U 1 + traceB V 0, traceB U 2 + traceB V 1, traceB V 2] q +
    ∑ i, X i * C ((W i).1 q)

/-- The trace-quadratic coefficients of the three normal quadratic monomials. -/
def productNormal2 (U V : Coefficients K m) (W : Fin m → Coefficients K m)
    (q : Fin 3) : Poly K m :=
  ![traceA U 0, traceA U 1 + traceA V 0, traceA V 1] q + ∑ i, X i * traceB (W i) q

/-- The trace-cubic coefficients of the two normal-linear monomials. -/
def productNormal1 (W : Fin m → Coefficients K m) (k : Fin 2) : Poly K m :=
  ∑ i, X i * traceA (W i) k

private theorem X_false_mul_normalMonomial {R : Type*} [CommRing R]
    (p q : ℕ) (r : R) : X false * normalMonomial p q r = normalMonomial (p + 1) q r := by
  simp only [normalMonomial_eq, pow_succ]
  ring

private theorem X_true_mul_normalMonomial {R : Type*} [CommRing R]
    (p q : ℕ) (r : R) : X true * normalMonomial p q r = normalMonomial p (q + 1) r := by
  simp only [normalMonomial_eq, pow_succ]
  ring

private theorem C_mul_normalMonomial {R : Type*} [CommRing R]
    (p q : ℕ) (a r : R) : C a * normalMonomial p q r = normalMonomial p q (a * r) := by
  simp only [normalMonomial_eq, map_mul]
  ring

/-- The full degree-by-degree expansion of the actual product. -/
theorem nestedProduct_eq (U V : Coefficients K m) (W : Fin m → Coefficients K m) :
    nestedProduct U V W =
      normalMonomial 4 0 (C (productNormal4 U V 0)) +
      normalMonomial 3 1 (C (productNormal4 U V 1)) +
      normalMonomial 2 2 (C (productNormal4 U V 2)) +
      normalMonomial 1 3 (C (productNormal4 U V 3)) +
      normalMonomial 0 4 (C (productNormal4 U V 4)) +
      normalMonomial 3 0 (productNormal3 U V W 0) +
      normalMonomial 2 1 (productNormal3 U V W 1) +
      normalMonomial 1 2 (productNormal3 U V W 2) +
      normalMonomial 0 3 (productNormal3 U V W 3) +
      normalMonomial 2 0 (productNormal2 U V W 0) +
      normalMonomial 1 1 (productNormal2 U V W 1) +
      normalMonomial 0 2 (productNormal2 U V W 2) +
      normalMonomial 1 0 (productNormal1 W 0) +
      normalMonomial 0 1 (productNormal1 W 1) := by
  simp only [nestedProduct, nestedCubic, mul_add, X_false_mul_normalMonomial,
    X_true_mul_normalMonomial, C_mul_normalMonomial, Finset.sum_add_distrib]
  simp [productNormal4, productNormal3, productNormal2, productNormal1, normalMonomial, map_sum]
  abel

end IdealGeneration.CubicNormalExpansion
