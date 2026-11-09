module

public import IdealGeneration.TripleNormalInitialCubicTarget
public import IdealGeneration.CertifiedPackedRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Kernel-checked arithmetic for the A.4 cubic minor. The nine batches each
check 32 rows of the exact factorization. -/

namespace IdealGeneration.TripleNormalInitial.CubicLU
open CertifiedRank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
set_option Elab.async false

theorem packedUpper_correct : ∀ i, packedUpper i = packSparse (2 ^ 40) (upperRows i) := by
  decide +kernel

abbrev packedCheck (i : Fin 288) : Prop :=
  packedProduct (lowerRows i) packedUpper = packSparse (2 ^ 40) (targetRows i) +
    1009 * Nat.ofDigits (2 ^ 40) (quotientRows i)

theorem packedCheck_block0 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((0 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block1 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((1 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block2 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((2 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block3 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((3 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block4 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((4 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block5 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((5 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block6 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((6 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block7 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((7 : Fin 9), j)) := by
  decide +kernel

theorem packedCheck_block8 : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv ((8 : Fin 9), j)) := by
  decide +kernel

theorem lowerSupport : ∀ i, (lowerRows i).all (fun e => decide (e.1 ≤ i)) = true := by
  decide +kernel

theorem upperSupport : ∀ i, (upperRows i).all (fun e => decide (i ≤ e.1)) = true := by
  decide +kernel

theorem lowerDiagonal : ∀ i, rowValue (lowerRows i) i % 1009 ≠ 0 := by
  decide +kernel

theorem upperDiagonal : ∀ i, rowValue (upperRows i) i % 1009 ≠ 0 := by
  decide +kernel

end IdealGeneration.TripleNormalInitial.CubicLU
