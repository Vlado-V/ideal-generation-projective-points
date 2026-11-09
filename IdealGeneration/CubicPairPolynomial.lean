module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial columns of the cubic pair block

Trace coordinates are `0,5,6,10,11` in positions `0,...,4`. Positions `5,6`
carry the two direction weights. Lift centers `10,11,12,13` have positions
`0,...,3` in the coefficient array.
-/

namespace IdealGeneration.CubicPair

/-- The five old-coordinate coefficients of the three basis lifts at four centers. -/
abbrev PairLiftCoefficients (R : Type*) := Fin 4 → Fin 3 → Fin 5 → Fin 2 → R

section Values

variable {R : Type*} [CommRing R]

/-- Restriction of one basis lift to the five old trace coordinates. -/
def basisLiftValue (coeff : PairLiftCoefficients R) (center : Fin 4)
    (q : Fin 3) (x : Fin 7 → R) (k : Fin 2) : R :=
  ∑ j : Fin 5, coeff center q j k * x (Fin.castAdd 2 j)

/-- A half-face column with normal form `τ*s-t`. -/
def halfFaceValue (t : R) (i c : Fin 7) (x : Fin 7 → R) (k : Fin 2) : R :=
  ![t, -1] k * x i * x c

/-- The 26 weighted column values in the order specified in Appendix C.3.
The two slope arguments belong to the single edges `{11,12}` and `{10,13}`. -/
def functionColumn (coeff : PairLiftCoefficients R) (t1 t2 : R)
    (c : Fin 26) (x : Fin 7 → R) (k : Fin 2) : R :=
  let L := fun center q => basisLiftValue coeff center q x k
  let w1 := fun q => x 4 * (L 2 q - L 1 q)
  let w2 := fun q => x 4 * (L 3 q - L 1 q)
  let b1 := fun q => x 3 * (L 2 q - L 0 q)
  let b2 := fun q => x 3 * (L 3 q - L 0 q)
  let columns : Fin 26 → R :=
    ![w1 0, w1 1, w1 2,
      x 4 * (t1 * L 2 0 - L 2 1), x 4 * (t1 * L 2 1 - L 2 2),
      b1 0, b1 1, b1 2,
      halfFaceValue t1 4 4 x k, halfFaceValue t1 4 3 x k,
      halfFaceValue t1 4 0 x k, halfFaceValue t1 4 1 x k, halfFaceValue t1 4 2 x k,
      w2 0, w2 1, w2 2, b2 0, b2 1, b2 2,
      x 3 * (t2 * L 3 0 - L 3 1), x 3 * (t2 * L 3 1 - L 3 2),
      halfFaceValue t2 3 3 x k, halfFaceValue t2 3 4 x k,
      halfFaceValue t2 3 0 x k, halfFaceValue t2 3 1 x k, halfFaceValue t2 3 2 x k]
  (if c.val < 13 then x 5 else x 6) * columns c

/-- The formulas commute with every coefficient ring homomorphism. -/
theorem map_functionColumn {S : Type*} [CommRing S] (f : R →+* S)
    (coeff : PairLiftCoefficients R) (t1 t2 : R) (c : Fin 26)
    (x : Fin 7 → R) (k : Fin 2) :
    f (functionColumn coeff t1 t2 c x k) =
      functionColumn (fun a q j l => f (coeff a q j l)) (f t1) (f t2) c
        (fun i => f (x i)) k := by
  fin_cases c <;> fin_cases k <;>
    simp [functionColumn, halfFaceValue, basisLiftValue, map_sum]

end Values

noncomputable section Polynomials

open MvPolynomial
variable {K : Type*} [Field K]

/-- The actual vector-valued homogeneous cubic column in five trace variables
and two direction weights. -/
def polynomialColumn (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (k : Fin 2) : MvPolynomial (Fin 7) K :=
  functionColumn (fun a q j l => C (coeff a q j l)) (C t1) (C t2) c X k

/-- Evaluating the actual polynomials gives the numerical column formulas. -/
theorem eval_polynomialColumn (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (x : Fin 7 → K) (k : Fin 2) :
    eval x (polynomialColumn coeff t1 t2 c k) = functionColumn coeff t1 t2 c x k := by
  simpa only [polynomialColumn, eval_C, eval_X] using
    (map_functionColumn (eval x) (fun a q j l => C (coeff a q j l))
      (C t1) (C t2) c X k)

/-- Every component of every weighted pair column is homogeneous of degree three. -/
theorem polynomialColumn_isHomogeneous (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (c : Fin 26) (k : Fin 2) :
    (polynomialColumn coeff t1 t2 c k).IsHomogeneous 3 := by
  let pc : PairLiftCoefficients (MvPolynomial (Fin 7) K) :=
    fun a q j l => C (coeff a q j l)
  have hL (a : Fin 4) (q : Fin 3) :
      (basisLiftValue pc a q X k).IsHomogeneous 1 := by
    exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  have hmotion (i : Fin 7) (a b : Fin 4) (q : Fin 3) :
      (X i * (basisLiftValue pc a q X k - basisLiftValue pc b q X k)).IsHomogeneous 2 :=
    (isHomogeneous_X K i).mul ((hL a q).sub (hL b q))
  have hextra (i : Fin 7) (a : Fin 4) (t : K) (q r : Fin 3) :
      (X i * (C t * basisLiftValue pc a q X k -
        basisLiftValue pc a r X k)).IsHomogeneous 2 :=
    (isHomogeneous_X K i).mul (((hL a q).C_mul t).sub (hL a r))
  have hhalf (t : K) (i j : Fin 7) :
      (halfFaceValue (C t) i j X k).IsHomogeneous 2 := by
    have hs : (![C t, -(1 : MvPolynomial (Fin 7) K)] k).IsHomogeneous 0 := by
      fin_cases k
      · exact isHomogeneous_C _ _
      · exact (isHomogeneous_one (Fin 7) K).neg
    exact (hs.mul (isHomogeneous_X K i)).mul (isHomogeneous_X K j)
  fin_cases c
  · exact (isHomogeneous_X K 5).mul (hmotion 4 2 1 0)
  · exact (isHomogeneous_X K 5).mul (hmotion 4 2 1 1)
  · exact (isHomogeneous_X K 5).mul (hmotion 4 2 1 2)
  · exact (isHomogeneous_X K 5).mul (hextra 4 2 t1 0 1)
  · exact (isHomogeneous_X K 5).mul (hextra 4 2 t1 1 2)
  · exact (isHomogeneous_X K 5).mul (hmotion 3 2 0 0)
  · exact (isHomogeneous_X K 5).mul (hmotion 3 2 0 1)
  · exact (isHomogeneous_X K 5).mul (hmotion 3 2 0 2)
  · exact (isHomogeneous_X K 5).mul (hhalf t1 4 4)
  · exact (isHomogeneous_X K 5).mul (hhalf t1 4 3)
  · exact (isHomogeneous_X K 5).mul (hhalf t1 4 0)
  · exact (isHomogeneous_X K 5).mul (hhalf t1 4 1)
  · exact (isHomogeneous_X K 5).mul (hhalf t1 4 2)
  · exact (isHomogeneous_X K 6).mul (hmotion 4 3 1 0)
  · exact (isHomogeneous_X K 6).mul (hmotion 4 3 1 1)
  · exact (isHomogeneous_X K 6).mul (hmotion 4 3 1 2)
  · exact (isHomogeneous_X K 6).mul (hmotion 3 3 0 0)
  · exact (isHomogeneous_X K 6).mul (hmotion 3 3 0 1)
  · exact (isHomogeneous_X K 6).mul (hmotion 3 3 0 2)
  · exact (isHomogeneous_X K 6).mul (hextra 3 3 t2 0 1)
  · exact (isHomogeneous_X K 6).mul (hextra 3 3 t2 1 2)
  · exact (isHomogeneous_X K 6).mul (hhalf t2 3 3)
  · exact (isHomogeneous_X K 6).mul (hhalf t2 3 4)
  · exact (isHomogeneous_X K 6).mul (hhalf t2 3 0)
  · exact (isHomogeneous_X K 6).mul (hhalf t2 3 1)
  · exact (isHomogeneous_X K 6).mul (hhalf t2 3 2)

/-- Arbitrarily selected component evaluations of a vector-valued polynomial. -/
def pairPolynomialEvaluation (points : Fin 26 → Fin 7 → K)
    (components : Fin 26 → Fin 2) :
    (Fin 2 → MvPolynomial (Fin 7) K) →ₗ[K] (Fin 26 → K) where
  toFun f r := eval (points r) (f (components r))
  map_add' f g := by ext r; simp
  map_smul' a f := by ext r; simp

/-- A nonsingular numerical evaluation certifies independence of all 26
polynomial columns built from the same lift coefficients. -/
theorem polynomialColumn_linearIndependent_of_matrix
    (coeff : PairLiftCoefficients K) (t1 t2 : K)
    (points : Fin 26 → Fin 7 → K) (components : Fin 26 → Fin 2)
    (A : Matrix (Fin 26) (Fin 26) K)
    (hA : ∀ r c, functionColumn coeff t1 t2 c (points r) (components r) = A r c)
    (hdet : A.det ≠ 0) :
    LinearIndependent K (polynomialColumn coeff t1 t2) := by
  apply LinearIndependent.of_comp (pairPolynomialEvaluation points components)
  have heq : pairPolynomialEvaluation points components ∘
      polynomialColumn coeff t1 t2 = A.col := by
    funext c r
    exact (eval_polynomialColumn coeff t1 t2 c (points r) (components r)).trans (hA r c)
  rw [heq]
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

end Polynomials
end IdealGeneration.CubicPair
