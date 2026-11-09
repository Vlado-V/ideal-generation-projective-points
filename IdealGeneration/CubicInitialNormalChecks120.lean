module

public import IdealGeneration.CubicInitialNormalEvaluationFacts

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

theorem normalPack120 : NormalPackCertificate 120 := by
  constructor
  decide +kernel

theorem normalPack121 : NormalPackCertificate 121 := by
  constructor
  decide +kernel

theorem normalPack122 : NormalPackCertificate 122 := by
  constructor
  decide +kernel

theorem normalPack123 : NormalPackCertificate 123 := by
  constructor
  decide +kernel

theorem normalPack124 : NormalPackCertificate 124 := by
  constructor
  decide +kernel

theorem normalPack125 : NormalPackCertificate 125 := by
  constructor
  decide +kernel

theorem normalPack126 : NormalPackCertificate 126 := by
  constructor
  decide +kernel

theorem normalPack127 : NormalPackCertificate 127 := by
  constructor
  decide +kernel

theorem normalPack128 : NormalPackCertificate 128 := by
  constructor
  decide +kernel

theorem normalPack129 : NormalPackCertificate 129 := by
  constructor
  decide +kernel

theorem normalPack130 : NormalPackCertificate 130 := by
  constructor
  decide +kernel

theorem normalPack131 : NormalPackCertificate 131 := by
  constructor
  decide +kernel

theorem normalPack132 : NormalPackCertificate 132 := by
  constructor
  decide +kernel

theorem normalPack133 : NormalPackCertificate 133 := by
  constructor
  decide +kernel

theorem normalPack134 : NormalPackCertificate 134 := by
  constructor
  decide +kernel

theorem normalPack135 : NormalPackCertificate 135 := by
  constructor
  decide +kernel

theorem normalPack136 : NormalPackCertificate 136 := by
  constructor
  decide +kernel

theorem normalPack137 : NormalPackCertificate 137 := by
  constructor
  decide +kernel

theorem normalPack138 : NormalPackCertificate 138 := by
  constructor
  decide +kernel

theorem normalPack139 : NormalPackCertificate 139 := by
  constructor
  decide +kernel

theorem normalPack140 : NormalPackCertificate 140 := by
  constructor
  decide +kernel

theorem normalPack141 : NormalPackCertificate 141 := by
  constructor
  decide +kernel

theorem normalPack142 : NormalPackCertificate 142 := by
  constructor
  decide +kernel

theorem normalPack143 : NormalPackCertificate 143 := by
  constructor
  decide +kernel


end IdealGeneration.CubicInitial
