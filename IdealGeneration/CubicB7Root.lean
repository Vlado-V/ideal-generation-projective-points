module

public import IdealGeneration.CubicB7RootComparison
public import IdealGeneration.CubicB7RootDeterminant
public import IdealGeneration.CubicB7RootCertificate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The concrete C.2 witness for the B.7 pool block. -/

namespace IdealGeneration.CubicSupported.B7Root

open B5 B7RootCertificate

/-- The actual C.2 initial pool evaluation is nonsingular in characteristic zero. -/
theorem pool_det_ne_zero (K : Type*) [Field K] [CharZero K] :
    (poolMatrix (actualB7Data (parametersCharZero K)) (pool K)).det ≠ 0 :=
  pool_det_ne_zero_of_mod (formula0_eq_mod.symm ▸ block0_det_ne_zero)
    (formula1_eq_mod.symm ▸ block1_det_ne_zero)

end IdealGeneration.CubicSupported.B7Root
