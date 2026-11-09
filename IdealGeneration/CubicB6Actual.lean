module

public import IdealGeneration.CubicB6Recurrence
public import IdealGeneration.CubicPairC3FixedSamples
public import IdealGeneration.CubicPairC3FutureGuard
public import IdealGeneration.CubicEvenTransfer

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The checked local C.3 determinants instantiate the B.6 recurrence. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B6

open B5 B7Root

/-- The actual local C.3 coefficient condition and its checked transport. -/
def pairCertificates : PairCertificates where
  good _ P j := PairGood P j
  fixedSamples _ P j h := PairGood.fixedSamplesFiber P j h
  retain _ _ _ h j := (pairGood_castSucc_iff h j).mpr
  newestGuard k := exists_newestPairGuard k

/-- The two finite C.2 witnesses produce an actual supported middle injection
over the rationals at every even level. -/
theorem exists_supported_even_middle_rat
    (hinit : Function.Injective (((CubicInitial.initialGraph ℚ).toConeConfiguration
      (CubicInitial.initialFree ℚ)).middleMultiplication 3))
    (hroot : (poolMatrix (actualB7Data (parametersCharZero ℚ)) (pool ℚ)).det ≠ 0)
    (k : ℕ) :
    ∃ (P : Parameters ℚ (10 + 2 * k)) (free : Fin (freeCount k) → Fin (10 + 2 * k) → ℚ),
      P.single = B5.single ∧
      Function.Injective ((P.toConeConfiguration free).middleMultiplication 3) := by
  obtain ⟨good⟩ := goodLevel_all pairCertificates hinit hroot k
  exact ⟨good.cones, good.free, good.graph, good.middle⟩

/-- The rational cone meets the exact B.1 counts. -/
theorem cubicEvenMiddleWitness_rat
    (hinit : Function.Injective (((CubicInitial.initialGraph ℚ).toConeConfiguration
      (CubicInitial.initialFree ℚ)).middleMultiplication 3))
    (hroot : (poolMatrix (actualB7Data (parametersCharZero ℚ)) (pool ℚ)).det ≠ 0)
    (k : ℕ) : CubicEvenMiddleWitness ℚ (10 + 2 * k) := by
  obtain ⟨P, free, hP, hmiddle⟩ := exists_supported_even_middle_rat hinit hroot k
  exact cubicEvenMiddleWitness_of_supported k P hP free hmiddle

end IdealGeneration.CubicSupported.B6
