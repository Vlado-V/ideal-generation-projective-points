module

public import IdealGeneration.CubicB7RootFormula
public import IdealGeneration.CubicB7RootCert.Data

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicSupported.B7Root

open B7RootCertificate CubicRationalFormula
local instance : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

theorem block0Rows080_eq : ∀ (i : Fin 6) (j : Fin 86),
    (formula0 ⟨80 + i.val, by omega⟩ j).eval (fun _ => (0 : ZMod 1009)) =
      (block0Entry ⟨80 + i.val, by omega⟩ j : ZMod 1009) := by
  decide +kernel

end IdealGeneration.CubicSupported.B7Root
