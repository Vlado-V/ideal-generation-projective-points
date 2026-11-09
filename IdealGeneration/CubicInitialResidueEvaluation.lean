module

public import IdealGeneration.CubicInitialGeometry
public import IdealGeneration.CertifiedDenseProduct

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Computable residue rows of the actual evaluation matrices. -/

namespace IdealGeneration.CubicInitial
open Matrix ConeMonomialChart

/-- Evaluation of a single monomial, represented by its natural residue. -/
def residueEvaluationEntry {n : ℕ} (point : Fin n → ℕ) (code : ℕ) : ℕ :=
  (List.ofFn fun j => point j ^ exponentDigit code j).prod % 1009

theorem cast_residueEvaluationEntry {n : ℕ} (point : Fin n → ℕ) (code : ℕ) :
    (residueEvaluationEntry point code : ZMod 1009) =
      ∏ j, (point j : ZMod 1009) ^ exponent code j := by
  rw [residueEvaluationEntry, ZMod.natCast_mod, List.prod_ofFn, Nat.cast_prod]
  simp only [Nat.cast_pow, exponent_apply]

def normalResidueEvaluation : Matrix (Fin 108) (Fin 144) ℕ :=
  fun i j => residueEvaluationEntry (pointCoordinate i) normalCodes[j.val]!

def traceResidueEvaluation : Matrix (Fin 165) (Fin 220) ℕ :=
  fun i j => residueEvaluationEntry (traceCoordinate i) traceCodes[j.val]!

theorem normalResidueEvaluation_map :
    normalResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) =
      normalEvaluationMatrix (ZMod 1009) := by
  ext i j
  exact cast_residueEvaluationEntry (pointCoordinate i) normalCodes[j.val]!

theorem traceResidueEvaluation_map :
    traceResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) =
      traceEvaluationMatrix (ZMod 1009) := by
  ext i j
  exact cast_residueEvaluationEntry (traceCoordinate i) traceCodes[j.val]!

theorem normalResidueEvaluation_lt (i : Fin 108) (j : Fin 144) :
    normalResidueEvaluation i j < 1009 := Nat.mod_lt _ (by decide)

theorem traceResidueEvaluation_lt (i : Fin 165) (j : Fin 220) :
    traceResidueEvaluation i j < 1009 := Nat.mod_lt _ (by decide)

end IdealGeneration.CubicInitial
