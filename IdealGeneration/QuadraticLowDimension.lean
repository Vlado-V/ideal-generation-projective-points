module

public import IdealGeneration.QuadraticLowDimensionFour
public import IdealGeneration.QuadraticLowDimensionFive
public import IdealGeneration.QuadraticLowDimensionSix
public import IdealGeneration.QuadraticLowDimensionNine
public import IdealGeneration.QuadraticLowDimensionTwelve

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The finite quadratic bases required by the one-step constructions in Appendix A. -/

namespace IdealGeneration

/-- The required low-dimensional quadratic bases follow from exact Euler
minors over small residue fields and their integer lifts. -/
theorem idealGenerationAt_quadratic_low_dimension {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (hN : N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 9 ∨ N = 12) :
    ∀ p, IdealGenerationAt K (N - 1) 2 p := by
  rcases hN with rfl | rfl | rfl | rfl | rfl
  · exact QuadraticLowDimension.quadratic_four_all
  · exact QuadraticLowDimension.quadratic_five_all
  · exact QuadraticLowDimension.quadratic_six_all
  · exact QuadraticLowDimension.quadratic_nine_all
  · exact QuadraticLowDimension.quadratic_twelve_all

end IdealGeneration
