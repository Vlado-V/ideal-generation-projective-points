module

public import IdealGeneration.CubicInitialMatrixData
public import IdealGeneration.CubicInitialCert.SelectedIndices

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option Elab.async false

namespace CertifiedRank.C2

/-- The selected minor, with columns reindexed using the inverse permutation. -/
noncomputable def targetRows (i : Fin 542) : SparseRow 542 Nat :=
  (originalRows (selectedRows i)).map fun e => (inverseSelectedColumns e.1, e.2)

end CertifiedRank.C2
