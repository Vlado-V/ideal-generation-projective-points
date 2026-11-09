module

public import IdealGeneration.CubicRootCert.Factorization
public import IdealGeneration.CertifiedLowerUpperRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

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

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

private instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

/-- The concrete Appendix C.2 combined root matrix has full row rank. -/
theorem root_matrix_rank : rootMatrix.rank = 160 := by
  have hr := full_column_rank_of_lower_upper rootMatrix.transpose minorRows minorColumns
    (residueMatrix 1009 lowerRows) (residueMatrix 1009 upperRows)
    (target_is_minor.symm.trans factorization.symm)
    (lower_of_support 1009 lowerRows (fun i => (row_facts i).lowerSupport))
    (upper_of_support 1009 upperRows (fun i => (row_facts i).upperSupport))
    (diagonal_ne_zero 1009 lowerRows (fun i => (row_facts i).lowerDiagonal))
    (diagonal_ne_zero 1009 upperRows (fun i => (row_facts i).upperDiagonal))
  calc
    rootMatrix.rank = rootMatrix.transpose.rank := (Matrix.rank_transpose rootMatrix).symm
    _ = Fintype.card (Fin 160) := hr
    _ = 160 := Fintype.card_fin 160

#print axioms root_matrix_rank

end IdealGeneration.CubicSupported.C2RootCertificate
