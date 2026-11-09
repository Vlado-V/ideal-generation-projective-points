module

public import IdealGeneration.CubicRootCert.Assembled
public import IdealGeneration.CertifiedPackedBounds

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.C2RootCertificate

open CertifiedRank

private theorem coefficients_lt {row : SparseRow 160 Nat} (h : SparseRowBound row) :
    ∀ e ∈ row, e.2 < 1009 :=
  fun e he => of_decide_eq_true ((List.all_eq_true.mp h.2) e he)

/-- The packed checks establish the selected minor's LU factorization. -/
theorem factorization : residueMatrix 1009 lowerRows * residueMatrix 1009 upperRows =
    residueMatrix 1009 targetRows := by
  refine checked_packed_product (n := 160) 1009 (2 ^ 40) (2 ^ 30) (160 * 1009)
    (by decide +kernel) (by decide +kernel) lowerRows upperRows targetRows packedUpper quotientRows
    packed_upper_rows ?_ ?_ quotientRows_length quotientRows_all_lt packed_checks
  · intro i j
    have h := rowValue_multiplyRow_le_dimension_sq_mul (lowerRows i) upperRows j 1009
      (row_facts i).lowerBound.1 (coefficients_lt (row_facts i).lowerBound)
      (fun k => (row_facts k).upperBound.1) (fun k => coefficients_lt (row_facts k).upperBound)
    exact h.trans_lt (by decide +kernel : 160 ^ 2 * 1009 ^ 2 < 2 ^ 40)
  · intro i j
    exact rowValue_le_dimension_mul (targetRows i) j 1009
      (row_facts i).targetBound.1 (coefficients_lt (row_facts i).targetBound)

/-- The certified square matrix is a minor of the concrete root transpose. -/
theorem target_is_minor : residueMatrix 1009 targetRows =
    rootMatrix.transpose.submatrix minorRows minorColumns := by
  have ht : residueMatrix 1009 rootColumns = rootMatrix.transpose :=
    (Matrix.transpose_transpose (residueMatrix 1009 rootColumns)).symm
  exact (residueMatrix_reindex 1009 rootColumns minorRows inverseMinorColumns minorColumns
    (fun i => (row_facts i).columnLeftInverse) (fun i => (row_facts i).columnRightInverse)).trans
    (congrArg (fun A : Matrix (Fin 177) (Fin 160) (ZMod 1009) =>
      A.submatrix minorRows minorColumns) ht)

#print axioms factorization
#print axioms target_is_minor

end IdealGeneration.CubicSupported.C2RootCertificate
