module

public import IdealGeneration.CubicInitialTracePackedData
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

structure TracePackCertificate (i : Fin 220) : Prop where
  checked : tracePacked i = packCoefficients (2 ^ 40) (traceFactor i)

structure TraceProductCertificate (i : Fin 165) : Prop where
  checked : densePackedProduct (traceResidueEvaluation i) tracePacked =
    packCoefficients (2 ^ 40) (traceIdentityBlock i) + 1009 *
      packCoefficients (2 ^ 40) (fun j : Fin 220 =>
        packedDigit (2 ^ 20) (traceQuotient i) j.val)

end IdealGeneration.CubicInitial
