module

public import IdealGeneration.QuadraticCoreRestrictionData
public import IdealGeneration.QuadraticFlagFamily

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The distinguished pair and selected layers of the canonical family reproduce the core. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreRestriction
open QuadraticCoreMiddle QuadraticFlagFamily QuadraticElimination

variable {K P J : Type*} [Field K] [CharZero K] [Fintype P] [DecidableEq J]

/-- Number the two selected layers by their positions in the core. -/
def selectedLayerEmbedding (layers : Bool → J) (hne : layers false ≠ layers true) : Fin 2 ↪ J where
  toFun j := if j = 0 then layers false else layers true
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hij).elim
    · exact (hne hij.symm).elim
    · rfl

omit [DecidableEq J] in
@[simp] theorem selectedLayerEmbedding_zero (layers : Bool → J) (hne : layers false ≠ layers true) :
    selectedLayerEmbedding layers hne 0 = layers false := rfl

omit [DecidableEq J] in
@[simp] theorem selectedLayerEmbedding_one (layers : Bool → J) (hne : layers false ≠ layers true) :
    selectedLayerEmbedding layers hne 1 = layers true := rfl

/-- The fixed six-point core appears in every member of the canonical family. -/
theorem restrict_canonical_parameters (p : P) (layers : Bool → J) (hne : layers false ≠ layers true) :
    restrictParameters (parameters K p layers) (selectedLayerEmbedding layers hne) = coreParameters K := by
  unfold restrictParameters coreParameters
  rw [QuadraticLiftParameters.mk.injEq]
  refine ⟨?_, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · funext i
    rcases i with ⟨u, b⟩
    cases u
    cases b
    · exact parameters_slope_distinguished_false K p layers
    · exact parameters_slope_distinguished_true K p layers
  · funext j
    fin_cases j <;> norm_num [parameters, hne]
  · funext j
    fin_cases j <;> norm_num [parameters, hne]
  · funext j
    fin_cases j <;> norm_num [parameters, hne]

end IdealGeneration.QuadraticCoreRestriction
