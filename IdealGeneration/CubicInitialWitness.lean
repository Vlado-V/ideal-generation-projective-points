module

public import IdealGeneration.CubicInitialGeometry
public import IdealGeneration.ConeJointMatrix
public import IdealGeneration.GenericRectangularDescent
public import IdealGeneration.ConeA1Bridge
public import IdealGeneration.CriticalOpen
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual cubic base configuration obtained from the coefficient certificate. -/

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 800000
namespace IdealGeneration.CubicInitial
open ConeMonomialChart ConeParameterSpace ConeMiddleFamily Module

local instance witnessPrime : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [CharZero K]

/-- The same marked cone works over every characteristic-zero field after
checking the coefficient stack modulo 1009. -/
theorem middle_injective_of_modular_stack
    (h : Function.Injective
      (jointMatrix normalExponent traceExponent quarticExponent
        (normalEvaluationMatrix (ZMod 1009)) (traceEvaluationMatrix (ZMod 1009))).mulVec) :
    Function.Injective ((configuration support (parameters K)).middleMultiplication 3) := by
  let A := jointMatrix normalExponent traceExponent quarticExponent
    (normalEvaluationMatrix ℤ) (traceEvaluationMatrix ℤ)
  have hmod : Function.Injective (A.map (Int.castRingHom (ZMod 1009))).mulVec := by
    simpa only [A, jointMatrix_map, normalEvaluationMatrix_intCast,
      traceEvaluationMatrix_intCast] using h
  have hcast := integer_matrix_mulVec_injective_of_mod (K := K) A 1009 hmod
  have hnormal := normalSynth_surjective (K := K) (c := 2) (m := 10) (d := 3) normalExponent normalExponent_degree
    normalExponent_positive normalExponent_injective (by decide)
  have htrace := formSynth_surjective (K := K) (n := 10) (d := 3) traceExponent traceExponent_degree
    traceExponent_injective (by decide)
  have hcast' : Function.Injective
      (jointMatrix normalExponent traceExponent quarticExponent
        (normalEvaluationMatrix K) (traceEvaluationMatrix K)).mulVec := by
    simpa only [A, jointMatrix_map, normalEvaluationMatrix_intCast,
      traceEvaluationMatrix_intCast] using hcast
  apply middle_injective_of_jointMatrix _ _ _ quarticExponent normalExponent_degree
    traceExponent_degree normalExponent_positive hnormal htrace
  have hN : evaluationMatrix (configuration support (parameters K)).point normalExponent =
      normalEvaluationMatrix K := by
    ext i j
    simp only [normalEvaluationMatrix, evaluationMatrix, configuration_point]
  have hT : evaluationMatrix (configuration support (parameters K)).trace traceExponent =
      traceEvaluationMatrix K := by
    ext i j
    simp only [traceEvaluationMatrix, evaluationMatrix, configuration_trace]
  rw [hN, hT]
  exact hcast'

/-- The initial actual middle-map witness supplies all twelve-variable cubic
point counts once the ten-variable trace theorem is available. -/
theorem cubic_twelve_variables_of_modular_stack
    (hn : Function.Surjective (normalEvaluationMatrix (ZMod 1009)).mulVec)
    (ht : Function.Surjective (traceEvaluationMatrix (ZMod 1009)).mulVec)
    (hm : Function.Injective
      (jointMatrix normalExponent traceExponent quarticExponent
        (normalEvaluationMatrix (ZMod 1009)) (traceEvaluationMatrix (ZMod 1009))).mulVec)
    (htrace : IdealGenerationAt K 9 3 165) :
    ∀ p, IdealGenerationAt K 11 3 p := by
  have hn' : Function.Surjective (normalEvaluationMatrix K).mulVec := by
    simpa only [normalEvaluationMatrix_intCast] using
      integer_matrix_mulVec_surjective_of_mod (K := K) (normalEvaluationMatrix ℤ) 1009
        (by simpa only [normalEvaluationMatrix_intCast] using hn)
  have ht' : Function.Surjective (traceEvaluationMatrix K).mulVec := by
    simpa only [traceEvaluationMatrix_intCast] using
      integer_matrix_mulVec_surjective_of_mod (K := K) (traceEvaluationMatrix ℤ) 1009
        (by simpa only [traceEvaluationMatrix_intCast] using ht)
  have hcritical : IdealGenerationAt K 11 3 273 :=
    ConeA1Bridge.idealGenerationAt_of_special_middle (c := 2) (n := 9) (by decide) (by decide)
      support (parameters K) 3 point_ne_zero
      (normalEvaluation_surjective_of_matrix hn') (traceEvaluation_surjective_of_matrix ht')
      (Or.inl (middle_injective_of_modular_stack hm))
      (by norm_num [N, Nat.choose]) htrace
  apply idealGenerationAt_all_of_critical (by decide) (by decide)
  · have h : lowerCritical 12 3 = 91 := by norm_num [lowerCritical, E, N, Nat.choose]
    simpa only [h, show N 12 3 - 91 = 273 by decide] using hcritical
  · have h : upperCritical 12 3 = 91 := by norm_num [upperCritical, E, N, Nat.choose]
    simpa only [h, show N 12 3 - 91 = 273 by decide] using hcritical

end IdealGeneration.CubicInitial
