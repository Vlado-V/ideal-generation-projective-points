module

public import IdealGeneration.QuadraticInduction
public import IdealGeneration.QuadraticEndpointA1

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The explicit bases and the two-normal transfers cover two through eleven variables. -/

noncomputable section
namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- The degree-two ideal-generation assertion in up to eleven homogeneous variables. -/
theorem quadratic_through_eleven_variables (n : ℕ) (hn : 2 ≤ n) (hmax : n ≤ 11) :
    ∀ p, IdealGenerationAt K (n - 1) 2 p := by
  have hseven : ∀ p, IdealGenerationAt K 6 2 p :=
    QuadraticEndpointA1.quadratic_mod_one_all 2 (by decide)
      (QuadraticLowDimension.quadratic_five_all 10)
  have height : ∀ p, IdealGenerationAt K 7 2 p :=
    QuadraticEndpointA1.quadratic_mod_two_all 2 (by decide)
      (QuadraticLowDimension.quadratic_six_all 14)
  have hten : ∀ p, IdealGenerationAt K 9 2 p :=
    QuadraticEndpointA1.quadratic_mod_one_all 3 (by decide) (height 24)
  have heleven : ∀ p, IdealGenerationAt K 10 2 p :=
    QuadraticEndpointA1.quadratic_mod_two_all 3 (by decide)
      (QuadraticLowDimension.quadratic_nine_all 30)
  interval_cases n
  · exact idealGenerationAt_projectiveLine_all 2 (by decide)
  · exact idealGenerationAt_projectivePlane 2 (by decide)
  · exact QuadraticLowDimension.quadratic_four_all
  · exact QuadraticLowDimension.quadratic_five_all
  · exact QuadraticLowDimension.quadratic_six_all
  · exact hseven
  · exact height
  · exact QuadraticLowDimension.quadratic_nine_all
  · exact hten
  · exact heleven

end IdealGeneration
