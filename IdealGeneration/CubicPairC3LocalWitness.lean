module

public import IdealGeneration.CubicPairC3Locality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The checked rational witness in the ambient-independent local chart. -/

namespace IdealGeneration.CubicSupported.B5

open CubicPair CubicPair.RationalConstruction CubicMixedLocality

/-- The local chart evaluates to the checked rational C.3 matrix. -/
theorem localC3Matrix_c3Parameters :
    localC3Matrix c3Parameters samplePointsQ = constructionMatrixQ := by
  have hCoeff : localC3Coefficients c3Parameters = restrictedLiftCoefficientsQ := by
    funext c q i r
    exact c3_mixedLinear_basis c q (Fin.castAdd 2 i) r
  have hOne : c3Parameters.edgeSlope c3PairEdgeOne 0 = 810 := by decide +kernel
  have hTwo : c3Parameters.edgeSlope c3PairEdgeTwo 0 = 479 := by decide +kernel
  unfold localC3Matrix constructionMatrixQ
  rw [hCoeff, hOne, hTwo]
  rfl

/-- C.3 supplies a nonsingular sample evaluation for the local chart. -/
theorem localC3Matrix_c3Parameters_det_ne_zero :
    (localC3Matrix c3Parameters samplePointsQ).det ≠ 0 := by
  rw [localC3Matrix_c3Parameters]
  exact constructionMatrixQ_det_ne_zero

end IdealGeneration.CubicSupported.B5
