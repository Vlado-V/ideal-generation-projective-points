module

public import IdealGeneration.TripleNormalFlags
public import IdealGeneration.TripleNormalInitialWitness

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The first flag from the checked initial coefficient certificate -/

noncomputable section
namespace IdealGeneration.TripleNormal

open TripleNormalInitial

variable {K : Type*} [Field K] [CharZero K]

/-- The initial numerical certificate supplies the three actual ranks of
the h=8 flag. -/
def flagEight_of_certificate (ω : K) (hω : IsPrimitiveRoot ω 3)
    {order : Column ≃ Fin 288} (cert : ModularCertificate order) :
    FlagWitness K ω 8 :=
  flagEight_of_ranks ω hω (normalEvaluation_surjective_of_certificate ω hω cert)
    (traceEvaluation_surjective_of_certificate ω hω cert) (middle_injective_of_certificate ω hω cert)

end IdealGeneration.TripleNormal
