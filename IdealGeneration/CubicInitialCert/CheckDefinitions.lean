module

public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CubicInitialCert.LowerRows
public import IdealGeneration.CubicInitialCert.UpperRows
public import IdealGeneration.CubicInitialCert.TargetRows
public import IdealGeneration.CubicInitialCert.SelectedIndices
public import IdealGeneration.CubicInitialCert.PackedUpper
public import IdealGeneration.CubicInitialCert.PackedQuotients

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace CertifiedRank.C2.PackedCertificate

/-- The size and coefficient bounds checked for each sparse row. -/
abbrev SparseRowBound (row : SparseRow 542 Nat) : Prop :=
  row.length ≤ 542 ∧ (row.all fun e => decide (e.2 < 1009)) = true

/-- Finite facts used in the packed product and triangular rank certificate. -/
structure PackedRowFacts (i : Fin 542) : Prop where
  lowerBound : SparseRowBound (lowerRows i)
  upperBound : SparseRowBound (upperRows i)
  targetBound : SparseRowBound (targetRows i)
  lowerSupport : (lowerRows i).all (fun e => decide (e.1 ≤ i)) = true
  upperSupport : (upperRows i).all (fun e => decide (i ≤ e.1)) = true
  lowerDiagonal : rowValue (lowerRows i) i % 1009 ≠ 0
  upperDiagonal : rowValue (upperRows i) i % 1009 ≠ 0
  columnLeftInverse : inverseSelectedColumns (selectedColumns i) = i
  columnRightInverse : selectedColumns (inverseSelectedColumns i) = i

end CertifiedRank.C2.PackedCertificate
