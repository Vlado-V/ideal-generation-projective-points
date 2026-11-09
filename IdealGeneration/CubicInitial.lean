module

public import IdealGeneration.CubicInitialMiddleComparison
public import IdealGeneration.CubicInitialMiddleLink
public import IdealGeneration.CubicInitialNormalEvaluationCertificate
public import IdealGeneration.CubicInitialTraceEvaluationCertificate
public import IdealGeneration.CubicInitialPackedCertificate
public import IdealGeneration.CubicInitialWitness
public import IdealGeneration.CubicInitialStructured
public import IdealGeneration.CubicMarkedBlock
public import IdealGeneration.CubicEvenTransfer
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The initial cubic cone of Appendix C.2 and its scalar and middle ranks. -/

noncomputable section
namespace IdealGeneration.CubicInitial
open ConeMonomialChart ConeParameterSpace ConeMiddleFamily

local instance initialPrime : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

/-- The concrete modular coefficient stack for the Appendix C.2 point data
has full column rank. -/
theorem modular_stack_injective :
    Function.Injective
      (jointMatrix normalExponent traceExponent quarticExponent
        (normalEvaluationMatrix (ZMod 1009)) (traceEvaluationMatrix (ZMod 1009))).mulVec := by
  have hn := normalEvaluation_kernel_of_factorization normalEvaluation_factorization
  have ht := traceEvaluation_kernel_of_factorization traceEvaluation_factorization
  apply jointMatrix_injective_of_kernel_columns (c := 2) (m := 10) _ _ _ _ _
    normalKernel traceKernel hn.2 ht.2
  exact middle_injective_of_rank normalLookupCheckAll traceLookupCheckAll middleRowCheckAll
    CertifiedRank.C2.PackedCertificate.original_rank

variable {K : Type*} [Field K] [CharZero K]

/-- The selected initial middle map is injective over every characteristic-zero field. -/
theorem middle_injective :
    Function.Injective ((configuration support (parameters K)).middleMultiplication 3) :=
  middle_injective_of_modular_stack modular_stack_injective

/-- The checked C.2 cone is the first actual middle witness in the cubic induction. -/
theorem initial_even_middle_witness : CubicEvenMiddleWitness K 10 :=
  ⟨108, 165, configuration support (parameters K), by decide, by decide, middle_injective⟩

/-- The same concrete witness lies in the supported graph family used by the pair extension. -/
theorem initial_graph_middle_injective :
    Function.Injective (((initialGraph K).toConeConfiguration (initialFree K)).middleMultiplication 3) :=
  structured_middle_injective middle_injective

/-- The explicit source and allowed-value coordinates have full initial rank. -/
theorem initial_graph_markedEvaluation_injective :
    Function.Injective ((initialGraph K).markedEvaluation (initialFree K)
      (by norm_num : (2 : K) ≠ 0) (by norm_num : (6 : K) ≠ 0)) :=
  ((initialGraph K).middleMultiplication_injective_iff_markedEvaluation
    (initialFree K) (by norm_num) (by norm_num)).mp initial_graph_middle_injective

/-- The C.2 initial case gives the twelve-variable cubic assertion from its
ten-variable trace case. -/
theorem cubic_twelve_variables (htrace : IdealGenerationAt K 9 3 165) :
    ∀ p, IdealGenerationAt K 11 3 p :=
  cubic_twelve_variables_of_modular_stack
    (normalEvaluation_kernel_of_factorization normalEvaluation_factorization).1
    (traceEvaluation_kernel_of_factorization traceEvaluation_factorization).1
    modular_stack_injective htrace

end IdealGeneration.CubicInitial
