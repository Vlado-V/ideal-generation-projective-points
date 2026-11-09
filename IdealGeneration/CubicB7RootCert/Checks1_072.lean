module

public import IdealGeneration.CubicB7RootCert.Inverse1

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.B7RootCertificate

open CertifiedRank Matrix

theorem cert1_072 : InverseRowCertificate block1Rows inverse1Rows
    packedInverse1 quotient1Code 72 := by
  constructor <;> decide +kernel

theorem cert1_073 : InverseRowCertificate block1Rows inverse1Rows
    packedInverse1 quotient1Code 73 := by
  constructor <;> decide +kernel


end IdealGeneration.CubicSupported.B7RootCertificate
