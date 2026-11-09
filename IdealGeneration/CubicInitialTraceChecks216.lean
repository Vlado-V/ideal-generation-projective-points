module

public import IdealGeneration.CubicInitialTraceEvaluationFacts

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

theorem tracePack216 : TracePackCertificate 216 := by
  constructor
  decide +kernel

theorem tracePack217 : TracePackCertificate 217 := by
  constructor
  decide +kernel

theorem tracePack218 : TracePackCertificate 218 := by
  constructor
  decide +kernel

theorem tracePack219 : TracePackCertificate 219 := by
  constructor
  decide +kernel


end IdealGeneration.CubicInitial
