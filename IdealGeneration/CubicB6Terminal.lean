module

public import IdealGeneration.CubicB6Actual
public import IdealGeneration.CubicSupportedBaseChange
public import IdealGeneration.CubicInitial
public import IdealGeneration.CubicB7Root

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The checked even middle witnesses over every characteristic-zero field. -/

noncomputable section
namespace IdealGeneration

open CubicSupported

/-- Appendix B gives an actual even middle witness in every required dimension. -/
theorem cubicEvenMiddleWitness_all (K : Type*) [Field K] [CharZero K] (k : ℕ) :
    CubicEvenMiddleWitness K (10 + 2 * k) := by
  obtain ⟨P, free, hP, hmiddle⟩ := B6.exists_supported_even_middle_rat
    (CubicInitial.initial_graph_middle_injective (K := ℚ)) (B7Root.pool_det_ne_zero ℚ) k
  exact cubicEvenMiddleWitness_of_supported k (P.castRat K) hP
    (fun i j => (free i j : K)) (BaseChange.supportedMiddle_cast_injective (K := K) P free hmiddle)

end IdealGeneration
