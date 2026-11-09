module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# First variation in a square block normal form

After choosing bases adapted to the image and kernel at zero, a polynomial
matrix has blocks `P`, `X Q`, `X R`, and `X J + X² H`. The constant matrix of
`P` is the original isomorphism onto the image, and `J` is the induced first
variation from kernel to cokernel. We prove that if both square diagonal
blocks are nonsingular, the full determinant is a nonzero polynomial, with
its first nonzero coefficient at the predicted order. In particular the
family is nonsingular outside finitely many parameters.

The rectangular extension lifts every nonzero square minor of the induced
first variation, giving the general rank gain in this block normal form.
The change of bases taking an arbitrary family to this form is not included.
-/

noncomputable section

namespace IdealGeneration.Deformation

open Polynomial Matrix

variable {k m n : Type*} [Field k] [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- A polynomial family in bases adapted to its kernel and image at zero. -/
def blockFamily (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) :
    Matrix (m ⊕ n) (m ⊕ n) k[X] :=
  fromBlocks P ((X : k[X]) • Q) ((X : k[X]) • R) ((X : k[X]) • J.map C + (X : k[X]) ^ 2 • H)

/-- The polynomial matrix obtained by dividing each lower row by `X`. -/
def normalized (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) :
    Matrix (m ⊕ n) (m ⊕ n) k[X] :=
  fromBlocks P ((X : k[X]) • Q) R (J.map C + (X : k[X]) • H)

/-- Exact determinant factorization before specializing the parameter. -/
theorem determinant_factorization (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) :
    (blockFamily P Q R J H).det = (X : k[X]) ^ Fintype.card n * (normalized P Q R J H).det := by
  let weights : m ⊕ n → k[X] := Sum.elim (fun _ => 1) (fun _ => X)
  have hfactor : blockFamily P Q R J H =
      Matrix.of (fun i j => weights i * normalized P Q R J H i j) := by
    ext i j
    cases i <;> cases j <;>
      simp [blockFamily, normalized, weights, fromBlocks, pow_two, mul_add, mul_assoc]
  rw [hfactor, det_mul_column]
  simp [weights, Fintype.prod_sum_type]

/-- At zero the normalized determinant is the product of the two diagonal determinants. -/
theorem normalized_constant (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) :
    ((normalized P Q R J H).det).eval 0 = (P.map (eval 0)).det * J.det := by
  have hEval : (normalized P Q R J H).map (eval 0) =
      fromBlocks (P.map (eval 0)) 0 (R.map (eval 0)) J := by
    ext i j
    cases i <;> cases j <;> simp [normalized, fromBlocks]
  have hm := (evalRingHom (0 : k)).map_det (normalized P Q R J H)
  simp only [RingHom.mapMatrix_apply, coe_evalRingHom] at hm
  rw [hm, hEval, det_fromBlocks_zero₁₂]

/-- The coefficient predicted by first variation is exactly the product of determinants. -/
theorem first_variation_coefficient (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) :
    ((blockFamily P Q R J H).det).coeff (Fintype.card n) =
      (P.map (eval 0)).det * J.det := by
  rw [determinant_factorization]
  have hc : ((X : k[X]) ^ Fintype.card n * (normalized P Q R J H).det).coeff
      (Fintype.card n) = (normalized P Q R J H).det.coeff 0 := by
    simpa only [zero_add] using
      coeff_X_pow_mul ((normalized P Q R J H).det) (Fintype.card n) 0
  rw [hc, coeff_zero_eq_eval_zero]
  exact normalized_constant P Q R J H

/-- The square full-rank first variation gives a nonzero determinant polynomial. -/
theorem determinant_ne_zero (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X])
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : J.det ≠ 0) :
    (blockFamily P Q R J H).det ≠ 0 := by
  intro h
  have hc := first_variation_coefficient P Q R J H
  rw [h, coeff_zero] at hc
  exact mul_ne_zero hP hJ hc.symm

/-- Evaluation of a polynomial matrix commutes with taking its determinant. -/
theorem eval_determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k[X]) (ε : k) :
    M.det.eval ε = (M.map (eval ε)).det := by
  simpa only [RingHom.mapMatrix_apply, coe_evalRingHom] using
    (evalRingHom ε).map_det M

/-- Only finitely many parameter values fail to be nonsingular. -/
theorem finite_singular_parameters (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X])
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : J.det ≠ 0) :
    Set.Finite {ε : k | ((blockFamily P Q R J H).map (eval ε)).det = 0} := by
  have h := finite_setOfPred_isRoot (determinant_ne_zero P Q R J H hP hJ)
  simpa only [IsRoot, eval_determinant] using h

/-- Every parameter outside the finite exceptional set gives an injective map. -/
theorem injective_of_det_eval_ne_zero (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X]) (ε : k)
    (hε : ((blockFamily P Q R J H).det).eval ε ≠ 0) :
    Function.Injective ((blockFamily P Q R J H).map (eval ε)).mulVec := by
  apply mulVec_injective_of_det_ne_zero
  rwa [eval_determinant] at hε

/-- A nonzero polynomial has a nonzero value at a nonzero parameter over an infinite field. -/
theorem exists_nonzero_parameter [Infinite k] (p : k[X]) (hp : p ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧ p.eval ε ≠ 0 := by
  have hprod : (X : k[X]) * p ≠ 0 := mul_ne_zero X_ne_zero hp
  have hex : ∃ ε : k, ((X : k[X]) * p).eval ε ≠ 0 := by
    by_contra h
    push Not at h
    exact hprod (zero_of_eval_zero _ h)
  obtain ⟨ε, hε⟩ := hex
  refine ⟨ε, ?_⟩
  simpa only [eval_mul, eval_X, ne_eq, mul_eq_zero, not_or] using hε

/-- A good nonzero specialization exists over any infinite field. -/
theorem exists_injective_parameter [Infinite k]
    (P : Matrix m m k[X]) (Q : Matrix m n k[X])
    (R : Matrix n m k[X]) (J : Matrix n n k) (H : Matrix n n k[X])
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : J.det ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧
      Function.Injective ((blockFamily P Q R J H).map (eval ε)).mulVec := by
  obtain ⟨ε, hε, hdet⟩ := exists_nonzero_parameter _
    (determinant_ne_zero P Q R J H hP hJ)
  exact ⟨ε, hε, injective_of_det_eval_ne_zero P Q R J H ε hdet⟩

/-- The same adapted normal form with a rectangular first-variation block. -/
def rectangularFamily {a b : Type*} (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (J : Matrix a b k) (H : Matrix a b k[X]) :
    Matrix (m ⊕ a) (m ⊕ b) k[X] :=
  fromBlocks P ((X : k[X]) • Q) ((X : k[X]) • R)
    ((X : k[X]) • J.map C + (X : k[X]) ^ 2 • H)

/-- Each nonzero first-variation minor lifts to a nonzero polynomial minor of the full family. -/
theorem first_variation_minor_ne_zero {a b : Type*}
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (J : Matrix a b k) (H : Matrix a b k[X])
    (rows : n → a) (cols : n → b)
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : (J.submatrix rows cols).det ≠ 0) :
    ((rectangularFamily P Q R J H).submatrix
      (Sum.map id rows) (Sum.map id cols)).det ≠ 0 := by
  have heq : (rectangularFamily P Q R J H).submatrix
      (Sum.map id rows) (Sum.map id cols) =
      blockFamily P (Q.submatrix id cols) (R.submatrix rows id)
        (J.submatrix rows cols) (H.submatrix rows cols) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [heq]
  exact determinant_ne_zero _ _ _ _ _ hP hJ

/-- The lifted first-variation minor is nonsingular at some nonzero parameter. -/
theorem exists_nonsingular_minor_parameter [Infinite k] {a b : Type*}
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (J : Matrix a b k) (H : Matrix a b k[X])
    (rows : n → a) (cols : n → b)
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : (J.submatrix rows cols).det ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧
      (((rectangularFamily P Q R J H).submatrix
        (Sum.map id rows) (Sum.map id cols)).map (eval ε)).det ≠ 0 := by
  obtain ⟨ε, hε, hdet⟩ := exists_nonzero_parameter _
    (first_variation_minor_ne_zero P Q R J H rows cols hP hJ)
  exact ⟨ε, hε, by rwa [eval_determinant] at hdet⟩

/-- A first-variation minor gives the predicted additive lower bound on rank. -/
theorem exists_rank_gain_parameter [Infinite k] {a b : Type*} [Fintype a] [Fintype b]
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (J : Matrix a b k) (H : Matrix a b k[X])
    (rows : n → a) (cols : n → b)
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : (J.submatrix rows cols).det ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧ Fintype.card m + Fintype.card n ≤
      ((rectangularFamily P Q R J H).map (eval ε)).rank := by
  obtain ⟨ε, hε, hdet⟩ := exists_nonsingular_minor_parameter P Q R J H rows cols hP hJ
  refine ⟨ε, hε, ?_⟩
  have hle := rank_submatrix_le ((rectangularFamily P Q R J H).map (eval ε))
    (Sum.map id rows) (Sum.map id cols)
  have heq : (((rectangularFamily P Q R J H).map (eval ε)).submatrix
      (Sum.map id rows) (Sum.map id cols)) =
      (((rectangularFamily P Q R J H).submatrix
        (Sum.map id rows) (Sum.map id cols)).map (eval ε)) := rfl
  rw [heq, rank_of_det_ne_zero hdet, Fintype.card_sum] at hle
  exact hle

/-- A maximal-size first-variation minor gives maximal rank at a nonzero parameter. -/
theorem exists_maximal_rank_parameter [Infinite k] {a b : Type*}
    [Fintype a] [Fintype b]
    (P : Matrix m m k[X]) (Q : Matrix m b k[X])
    (R : Matrix a m k[X]) (J : Matrix a b k) (H : Matrix a b k[X])
    (rows : n → a) (cols : n → b)
    (hP : (P.map (eval 0)).det ≠ 0) (hJ : (J.submatrix rows cols).det ≠ 0)
    (hsize : Fintype.card n = min (Fintype.card a) (Fintype.card b)) :
    ∃ ε : k, ε ≠ 0 ∧
      ((rectangularFamily P Q R J H).map (eval ε)).rank =
        min (Fintype.card (m ⊕ a)) (Fintype.card (m ⊕ b)) := by
  obtain ⟨ε, hε, hlower⟩ := exists_rank_gain_parameter P Q R J H rows cols hP hJ
  refine ⟨ε, hε, ?_⟩
  apply le_antisymm
  · exact le_min (rank_le_card_height _) (rank_le_card_width _)
  · simp only [Fintype.card_sum]
    omega

end IdealGeneration.Deformation
