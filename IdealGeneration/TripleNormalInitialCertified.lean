module

public import IdealGeneration.TripleNormalInitialWitness
public import IdealGeneration.TripleNormalInitialEvaluation
public import IdealGeneration.TripleNormalInitialCubicCertificate
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Connect the verified scalar charts and the selected cubic coefficient minor. -/
noncomputable section
namespace IdealGeneration.TripleNormalInitial
open Matrix

private theorem modulus_prime : Nat.Prime 1009 := by norm_num

private theorem normalEvaluation_mod :
    normalEvaluationPolynomial.map modEval = normalEvaluationMod := by
  let : Fact (Nat.Prime 1009) := ⟨modulus_prime⟩
  exact normalEvaluationPolynomial_map (374 : ModField)

private theorem traceEvaluation_mod :
    traceEvaluationPolynomial.map modEval = traceEvaluationMod := by
  let : Fact (Nat.Prime 1009) := ⟨modulus_prime⟩
  exact traceEvaluationPolynomial_map (374 : ModField)

private theorem normalPivot_mod : normalPivotPolynomial.map modEval = normalPivotMod :=
  congrArg (fun M => M.submatrix id Sum.inl) normalEvaluation_mod

private theorem tracePivot_mod : tracePivotPolynomial.map modEval = tracePivotMod :=
  congrArg (fun M => M.submatrix id Sum.inl) traceEvaluation_mod

/-- The evaluated kernel bases are the normalized charts of the symbolic pivot matrices. -/
def certificateOfCubicMinor (hm : orderedMiddleMod.det ≠ 0) :
    ModularCertificate paperColumnOrder :=
  modularCertificateOfKernelColumns paperColumnOrder
    normalPivotInverseMod tracePivotInverseMod normalKernelMod traceKernelMod
    (normalPivot_mod.symm ▸ normalPivotInverseMod_mul)
    (tracePivot_mod.symm ▸ tracePivotInverseMod_mul)
    (normalEvaluation_mod.symm ▸ normalEvaluationMod_mul_kernel)
    (traceEvaluation_mod.symm ▸ traceEvaluationMod_mul_kernel)
    (by ext i j; simp [Matrix.one_apply])
    (by ext i j; simp [Matrix.one_apply])
    hm

/-- The exact table configuration has all of the modular witness data. -/
def initialCertificate : ModularCertificate paperColumnOrder :=
  certificateOfCubicMinor orderedMiddleMod_det_ne_zero

end IdealGeneration.TripleNormalInitial
