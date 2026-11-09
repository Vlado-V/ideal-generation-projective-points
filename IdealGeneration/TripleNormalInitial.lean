module

public import IdealGeneration.TripleNormalInitialCertified
public import IdealGeneration.TripleNormalInitialAllowed
public import IdealGeneration.TripleNormalInitialConsequences
public import IdealGeneration.TripleNormalMiddleKernel
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The checked initial square for the three-normal quadratic step. -/
noncomputable section
namespace IdealGeneration.TripleNormalInitial
open TripleNormal

variable {K : Type*} [Field K] [CharZero K]

/-- The compatible pure-normal lift at the initial flag. -/
def initialPureLift (ω : K) (hω : IsPrimitiveRoot ω 3) :
    Forms K 3 2 →ₗ[K] (configuration ω).residualPiece 2 :=
  SupportedQuadrics.pureLift (configuration ω) ω (baseParameters K)
    (layerNormals K) (layerHeights K) (Layer.baseSupport K 8) (initialPointPattern ω)
    hω baseParameters_ne_zero layerNormalMatrix_det_ne_zero layerHeights_ne_zero

@[simp] theorem initialPureLift_section (ω : K) (hω : IsPrimitiveRoot ω 3) (Q : Forms K 3 2) :
    quadraticRestriction (configuration ω) (initialPureLift ω hω Q) = Q :=
  SupportedQuadrics.pureRestrict_pureLift (configuration ω) ω (baseParameters K)
    (layerNormals K) (layerHeights K) (Layer.baseSupport K 8) (initialPointPattern ω)
    hω baseParameters_ne_zero layerNormalMatrix_det_ne_zero layerHeights_ne_zero Q

theorem initial_quadraticRestriction_surjective (ω : K) (hω : IsPrimitiveRoot ω 3) :
    Function.Surjective (quadraticRestriction (configuration ω)) :=
  fun Q => ⟨initialPureLift ω hω Q, initialPureLift_section ω hω Q⟩

/-- The actual initial cone multiplication is an isomorphism. -/
theorem initial_middle_bijective (ω : K) (hω : IsPrimitiveRoot ω 3) :
    Function.Bijective ((configuration ω).middleMultiplication 2) :=
  initial_middle_bijective_of_certificate ω hω initialCertificate

/-- The checked square (D_8) for the compatible section is bijective. -/
theorem initial_D8_bijective (ω : K) (hω : IsPrimitiveRoot ω 3) :
    Function.Bijective (allowedEvaluationMap (configuration ω) (initialPureLift ω hω)
      (initialPureLift_section ω hω) (fun _ => one_ne_zero)) := by
  let C := configuration ω
  let L := initialPureLift ω hω
  have hL : ∀ Q, quadraticRestriction C (L Q) = Q := initialPureLift_section ω hω
  have hh : ∀ i, C.height i ≠ 0 := fun _ => one_ne_zero
  let e := SupportedQuadrics.mixedEquiv C ω (baseParameters K)
    (layerNormals K) (layerHeights K) (Layer.baseSupport K 8) (initialPointPattern ω)
    hω baseParameters_ne_zero layerNormalMatrix_det_ne_zero layerHeights_ne_zero
  have hk : Module.finrank K (MixedKernel C) = 8 := e.symm.finrank_eq.trans (by simp)
  have hd := allowedEvaluationMap_square C L hL 8 hk
    (initial_valueConstraint_surjective ω hω) (by decide)
  have hi := (middle_injective_iff_allowedEvaluation C L hL hh).mp
    (middle_injective_of_certificate ω hω initialCertificate)
  let : AddCommGroup (EvaluationSource C) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (AllowedValues C) := Module.addCommMonoidToAddCommGroup K
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

/-- Appendix A.4 at fifteen variables, with the independent twelve-variable trace input. -/
theorem initial_idealGenerationAt [IsAlgClosed K] (hinduction : IdealGenerationAt K 11 2 52) :
    IdealGenerationAt K 14 2 80 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 3 K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos 3 K (by decide)))
  exact initial_idealGenerationAt_of_certificate ω
    ((Polynomial.isRoot_cyclotomic_iff_charZero (by decide)).mp hω)
    initialCertificate hinduction

end IdealGeneration.TripleNormalInitial
