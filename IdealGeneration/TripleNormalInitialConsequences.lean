module

public import IdealGeneration.TripleNormalInitialWitness
public import IdealGeneration.TripleNormalQuadraticTransfer

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Transfer the checked initial middle and scalar maps to the quadratic endpoint. -/
namespace IdealGeneration.TripleNormalInitial
open TripleNormal

variable {K : Type*} [Field K] [CharZero K]

theorem initial_middle_bijective_of_certificate (ω : K) (hω : IsPrimitiveRoot ω 3)
    {order : Column ≃ Fin 288} (cert : ModularCertificate order) :
    Function.Bijective ((configuration ω).middleMultiplication 2) :=
  quadratic_tripleNormal_middle_bijective 8 (by decide) (configuration ω)
    (normalEvaluation_surjective_of_certificate ω hω cert)
    (traceEvaluation_surjective_of_certificate ω hω cert)
    (middle_injective_of_certificate ω hω cert)

theorem initial_idealGenerationAt_of_certificate (ω : K) (hω : IsPrimitiveRoot ω 3)
    {order : Column ≃ Fin 288} (cert : ModularCertificate order)
    (hinduction : IdealGenerationAt K 11 2 52) :
    IdealGenerationAt K 14 2 80 :=
  quadratic_tripleNormal_endpoint 8 (by decide) (configuration ω)
    (normalEvaluation_surjective_of_certificate ω hω cert)
    (traceEvaluation_surjective_of_certificate ω hω cert)
    (initial_middle_bijective_of_certificate ω hω cert) hinduction

end IdealGeneration.TripleNormalInitial
