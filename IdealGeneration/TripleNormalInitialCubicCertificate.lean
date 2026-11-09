module

public import IdealGeneration.TripleNormalInitialCubicChecks
public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CertifiedPackedBounds
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A Lean-kernel check of the sparse lower-upper factorization of the actual
selected cubic coefficient matrix. -/

noncomputable section
namespace IdealGeneration.TripleNormalInitial
open CertifiedRank CubicLU Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option exponentiation.threshold 1024
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem prime1009 : Nat.Prime 1009 := by norm_num
local instance : Fact (Nat.Prime 1009) := ⟨prime1009⟩

private theorem packedCheck_blocks (b : Fin 9) : ∀ j : Fin 32,
    packedCheck (finProdFinEquiv (b, j)) := by
  fin_cases b
  · exact packedCheck_block0
  · exact packedCheck_block1
  · exact packedCheck_block2
  · exact packedCheck_block3
  · exact packedCheck_block4
  · exact packedCheck_block5
  · exact packedCheck_block6
  · exact packedCheck_block7
  · exact packedCheck_block8

private theorem packedCheck_all (i : Fin 288) : packedCheck i := by
  obtain ⟨⟨b, j⟩, rfl⟩ := (finProdFinEquiv : Fin 9 × Fin 32 ≃ Fin 288).surjective i
  exact packedCheck_blocks b j

/-- The checked modular product is the exact target matrix. -/
theorem cubicLU_eq : residueMatrix 1009 lowerRows * residueMatrix 1009 upperRows =
    residueMatrix 1009 targetRows := by
  apply checked_packed_product 1009 (2 ^ 40) (2 ^ 19) 1009 (by decide) (by decide)
    lowerRows upperRows targetRows packedUpper quotientRows packedUpper_correct
  · intro i j
    exact (rowValue_multiplyRow_le_dimension_sq_mul (lowerRows i) upperRows j 1024
      (lowerRows_length_le i) (lowerRows_coeff_lt i) upperRows_length_le upperRows_coeff_lt).trans_lt
      (by decide)
  · intro i j
    rw [targetRows_value]
    change (slotMiddleMod (rowPermutation i) (packedColumnOrder.symm j)).val ≤ 1009
    exact (ZMod.val_lt (slotMiddleMod (rowPermutation i) (packedColumnOrder.symm j))).le
  · exact quotientRows_length
  · exact quotientRows_lt
  · exact packedCheck_all

theorem targetMatrix_det_ne_zero : (residueMatrix 1009 targetRows).det ≠ 0 := by
  rw [← cubicLU_eq, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ (lower_of_support 1009 lowerRows lowerSupport),
    Matrix.det_of_isUpperTriangular (upper_of_support 1009 upperRows upperSupport)]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => diagonal_ne_zero 1009 lowerRows lowerDiagonal i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => diagonal_ne_zero 1009 upperRows upperDiagonal i))

/-- The original pivot-row minor is nonsingular in the paper's column order. -/
theorem orderedMiddleMod_det_ne_zero : orderedMiddleMod.det ≠ 0 := by
  intro hz
  apply targetMatrix_det_ne_zero
  rw [targetMatrix_eq]
  change (orderedMiddleMod.reindex rowEquiv.symm columnEquiv.symm).det = 0
  rw [Matrix.det_reindex, hz, mul_zero]

end IdealGeneration.TripleNormalInitial
