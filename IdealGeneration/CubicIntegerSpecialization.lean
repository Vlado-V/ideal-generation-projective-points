module

public import IdealGeneration.CubicParameterCompatibility
public import IdealGeneration.CubicRationalFormula

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Specialization of integer certificates to polynomials in the new coordinates. -/

noncomputable section
namespace IdealGeneration.CubicParameterCompatibility

open MvPolynomial

variable (K : Type*) [Field K] {New Old : Type*}

/-- Cast an integer certificate and view it as a polynomial in the new variables. -/
def intSumPolynomial (P : MvPolynomial (New ⊕ Old) ℤ) :
    MvPolynomial New (MvPolynomial Old K) :=
  sumAlgEquiv K New Old (MvPolynomial.map (Int.castRingHom K) P)

/-- Specializing the old variables and then evaluating the new ones is exact. -/
theorem eval_specialize_intSumPolynomial (x : Old → K) (y : New → K)
    (P : MvPolynomial (New ⊕ Old) ℤ) :
    eval y (specialize x (intSumPolynomial K P)) =
      CubicRationalFormula.evalPolynomial (Sum.elim y x) P := by
  rw [intSumPolynomial, eval_specialize_sumPolynomial]
  change eval₂Hom (RingHom.id K) (Sum.elim y x) (MvPolynomial.map (Int.castRingHom K) P) = _
  rw [eval₂Hom_map_hom, RingHom.id_comp]
  rfl

/-- A successful witness makes the polynomial in the new coordinates nonzero at that old chart. -/
theorem specialize_intSumPolynomial_ne_zero_of_eval (x : Old → K) (y : New → K)
    (P : MvPolynomial (New ⊕ Old) ℤ)
    (h : CubicRationalFormula.evalPolynomial (Sum.elim y x) P ≠ 0) :
    specialize x (intSumPolynomial K P) ≠ 0 := by
  intro hz
  apply h
  rw [← eval_specialize_intSumPolynomial K x y P, hz, map_zero]

end IdealGeneration.CubicParameterCompatibility
