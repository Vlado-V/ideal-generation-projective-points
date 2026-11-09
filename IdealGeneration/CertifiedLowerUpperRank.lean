module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace CertifiedRank

variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype n] [LinearOrder n]

/-- A checked lower-upper factorization of any square minor proves full column rank. -/
theorem full_column_rank_of_lower_upper
    (A : Matrix m n K) (rows : n → m) (cols : n → n)
    (L U : Matrix n n K)
    (hLU : A.submatrix rows cols = L * U)
    (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
    (hLd : ∀ i, L i i ≠ 0) (hUd : ∀ i, U i i ≠ 0) :
    A.rank = Fintype.card n := by
  have hLdet : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L hL]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hLd i
  have hUdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hUd i
  have hdet : (A.submatrix rows cols).det ≠ 0 := by
    rw [hLU, Matrix.det_mul]
    exact mul_ne_zero hLdet hUdet
  apply le_antisymm A.rank_le_card_width
  calc
    Fintype.card n = (A.submatrix rows cols).rank :=
      (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ A.rank := Matrix.rank_submatrix_le A rows cols

end CertifiedRank

#print axioms CertifiedRank.full_column_rank_of_lower_upper
