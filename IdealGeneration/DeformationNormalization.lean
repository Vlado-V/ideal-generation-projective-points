module

public import IdealGeneration.Deformation
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Inductions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normalizing polynomial first variations

For an arbitrary polynomial block matrix, vanishing of the two off-diagonal
blocks and the lower-right block at zero gives the exact normal form used in
`Deformation`. The lower-right first-order block is its actual formal
derivative evaluated at zero. No divisibility or higher-order remainder
hypothesis has to be supplied separately.

These results start after constant bases adapted to the image and kernel
of the original matrix have been chosen.
-/

noncomputable section
namespace IdealGeneration.DeformationNormalization

open Polynomial Matrix IdealGeneration.Deformation

variable {k : Type*} [Field k]

/-- A polynomial vanishing at zero is exactly `X` times its coefficient shift. -/
theorem factor_X_of_eval_zero (p : k[X]) (hp : p.eval 0 = 0) :
    p = X * p.divX := by
  have hc : p.coeff 0 = 0 := by rwa [coeff_zero_eq_eval_zero]
  simpa only [hc, map_zero, add_zero] using (X_mul_divX_add p).symm

/-- The exact first-order expansion with an explicit polynomial remainder. -/
theorem first_order_expansion (p : k[X]) (hp : p.eval 0 = 0) :
    p = X * C (p.coeff 1) + X ^ 2 * p.divX.divX := by
  have hshift : p.divX = X * p.divX.divX + C (p.coeff 1) := by
    simpa only [coeff_divX, zero_add] using (X_mul_divX_add p.divX).symm
  calc
    p = X * p.divX := factor_X_of_eval_zero p hp
    _ = X * (X * p.divX.divX + C (p.coeff 1)) := congrArg (X * ·) hshift
    _ = X * C (p.coeff 1) + X ^ 2 * p.divX.divX := by ring

/-- The degree-one coefficient is the actual formal derivative at zero. -/
theorem first_coefficient_eq_derivative (p : k[X]) :
    p.coeff 1 = p.derivative.eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

variable {a b m n : Type*}

/-- The first-order coefficient matrix. -/
def firstCoefficient (S : Matrix a b k[X]) : Matrix a b k :=
  S.map (fun p => p.coeff 1)

/-- The entrywise formal derivative evaluated at the special parameter. -/
def derivativeAtZero (S : Matrix a b k[X]) : Matrix a b k :=
  S.map (fun p => p.derivative.eval 0)

/-- The coefficient matrix and derivative matrix agree over every field. -/
theorem firstCoefficient_eq_derivativeAtZero (S : Matrix a b k[X]) :
    firstCoefficient S = derivativeAtZero S := by
  ext i j
  exact first_coefficient_eq_derivative (S i j)

/-- The canonical exact normalization of arbitrary blocks with the stated zero values. -/
theorem block_normalization (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (S : Matrix a b k[X])
    (hQ : Q.map (eval 0) = 0) (hR : R.map (eval 0) = 0)
    (hS : S.map (eval 0) = 0) :
    fromBlocks P Q R S = rectangularFamily P (Q.map divX) (R.map divX)
      (firstCoefficient S) (S.map (fun p => p.divX.divX)) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      exact factor_X_of_eval_zero (Q i j) (congrFun (congrFun hQ i) j)
  | inr i =>
    cases j with
    | inl j =>
      exact factor_X_of_eval_zero (R i j) (congrFun (congrFun hR i) j)
    | inr j =>
      exact first_order_expansion (S i j) (congrFun (congrFun hS i) j)

/-- Normalization expressed using the actual derivative instead of coefficient notation. -/
theorem block_normalization_derivative (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (S : Matrix a b k[X])
    (hQ : Q.map (eval 0) = 0) (hR : R.map (eval 0) = 0)
    (hS : S.map (eval 0) = 0) :
    fromBlocks P Q R S = rectangularFamily P (Q.map divX) (R.map divX)
      (derivativeAtZero S) (S.map (fun p => p.divX.divX)) := by
  rw [← firstCoefficient_eq_derivativeAtZero]
  exact block_normalization P Q R S hQ hR hS

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A nonzero minor of the actual derivative lifts to a polynomial minor of the full matrix. -/
theorem derivative_minor_ne_zero (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (S : Matrix a b k[X])
    (hQ : Q.map (eval 0) = 0) (hR : R.map (eval 0) = 0)
    (hS : S.map (eval 0) = 0)
    (hP : (P.map (eval 0)).det ≠ 0) (rows : n → a) (cols : n → b)
    (hJ : ((derivativeAtZero S).submatrix rows cols).det ≠ 0) :
    ((fromBlocks P Q R S).submatrix (Sum.map id rows) (Sum.map id cols)).det ≠ 0 := by
  rw [block_normalization_derivative P Q R S hQ hR hS]
  exact first_variation_minor_ne_zero _ _ _ _ _ rows cols hP hJ

/-- The first-variation rank principle for arbitrary already-adapted polynomial blocks. -/
theorem exists_maximal_rank_of_derivative [Infinite k] [Fintype a] [Fintype b]
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (S : Matrix a b k[X])
    (hQ : Q.map (eval 0) = 0) (hR : R.map (eval 0) = 0)
    (hS : S.map (eval 0) = 0)
    (hP : (P.map (eval 0)).det ≠ 0) (rows : n → a) (cols : n → b)
    (hJ : ((derivativeAtZero S).submatrix rows cols).det ≠ 0)
    (hsize : Fintype.card n = min (Fintype.card a) (Fintype.card b)) :
    ∃ ε : k, ε ≠ 0 ∧ ((fromBlocks P Q R S).map (eval ε)).rank =
      min (Fintype.card (m ⊕ a)) (Fintype.card (m ⊕ b)) := by
  rw [block_normalization_derivative P Q R S hQ hR hS]
  exact exists_maximal_rank_parameter _ _ _ _ _ rows cols hP hJ hsize

/-- The full matrix has maximal rank away from finitely many parameters. -/
theorem finite_nonmaximal_rank_parameters [Fintype a] [Fintype b]
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (S : Matrix a b k[X])
    (hQ : Q.map (eval 0) = 0) (hR : R.map (eval 0) = 0)
    (hS : S.map (eval 0) = 0)
    (hP : (P.map (eval 0)).det ≠ 0) (rows : n → a) (cols : n → b)
    (hJ : ((derivativeAtZero S).submatrix rows cols).det ≠ 0)
    (hsize : Fintype.card n = min (Fintype.card a) (Fintype.card b)) :
    Set.Finite {ε : k | ((fromBlocks P Q R S).map (eval ε)).rank <
      min (Fintype.card (m ⊕ a)) (Fintype.card (m ⊕ b))} := by
  classical
  let N := (fromBlocks P Q R S).submatrix (Sum.map id rows) (Sum.map id cols)
  have hN : N.det ≠ 0 := derivative_minor_ne_zero P Q R S hQ hR hS hP rows cols hJ
  have hfinite : Set.Finite {ε : k | (N.map (eval ε)).det = 0} := by
    simpa only [IsRoot, eval_determinant] using finite_setOfPred_isRoot hN
  apply hfinite.subset
  intro ε hbad
  change (N.map (eval ε)).det = 0
  by_contra hdet
  have hle := rank_submatrix_le ((fromBlocks P Q R S).map (eval ε))
    (Sum.map id rows) (Sum.map id cols)
  have heq : (((fromBlocks P Q R S).map (eval ε)).submatrix
      (Sum.map id rows) (Sum.map id cols)) = N.map (eval ε) := rfl
  rw [heq, rank_of_det_ne_zero hdet, Fintype.card_sum] at hle
  simp only [Set.mem_ofPred_eq, Fintype.card_sum] at hbad
  omega

end IdealGeneration.DeformationNormalization
