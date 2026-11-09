module

public import IdealGeneration.CubicInitialNormalPackedData
public import IdealGeneration.CubicInitialResidueEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 2048

namespace IdealGeneration.CubicInitial
open CertifiedRank Matrix

structure NormalPackCertificate (i : Fin 144) : Prop where
  checked : normalPacked i = packCoefficients (2 ^ 40) (normalFactor i)

structure NormalProductCertificate (i : Fin 108) : Prop where
  checked : densePackedProduct (normalResidueEvaluation i) normalPacked =
    packCoefficients (2 ^ 40) (normalIdentityBlock i) + 1009 *
      packCoefficients (2 ^ 40) (fun j : Fin 144 =>
        packedDigit (2 ^ 20) (normalQuotient i) j.val)

end IdealGeneration.CubicInitial
