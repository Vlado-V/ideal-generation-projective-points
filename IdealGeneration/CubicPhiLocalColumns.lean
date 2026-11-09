module

public import IdealGeneration.CubicExplicitSource
public import IdealGeneration.CubicLocalLift

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The single-edge and mixed columns of the explicit trace map in (B.7). -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open MvPolynomial CubicNormalExpansion CubicUpperSolve CubicUpperBlockEquations

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

private theorem kernelCoordinatesEquiv_coefficientLift
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    P.kernelCoordinatesEquiv (P.coefficientLift C₀ B z) = (C₀, B, z) := by
  change (C₀, B, P.freeCoefficients (P.coefficientLift C₀ B z)) = (C₀, B, z)
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext e
  change -P.offDiagonalLift C₀ B z e.val 1 = z e
  simp [offDiagonalLift, e.property]

private theorem coefficientLift_zero : P.coefficientLift 0 0 0 = 0 := by
  apply P.kernelCoordinatesEquiv.injective
  exact (P.kernelCoordinatesEquiv_coefficientLift 0 0 0).trans
    (map_zero P.kernelCoordinatesEquiv).symm

private theorem traceA_zero (k : Fin 2) : traceA (0 : Coefficients K m) k = 0 := by
  simp [traceA, traceQuadratic, upperCoefficient]

private theorem parameterTraceCubic_zeroNormal
    (z : Edge m → Fin 3 → K) (δ : Fin m → P.SingleEdge → K) (j : Fin m) :
    P.parameterTraceCubic (0, z, δ) j = P.coefficientLift 0 (antisymmetric z j) (δ j) := by
  have hC : cubicCorrection (0 : Fin 3 → K) 0 = 0 := by
    change -QuadraticElimination.normalCubicMap (0 : (Fin 3 → K) × (Fin 3 → K)) = 0
    simp
  have hA : quadraticTarget (0 : Coefficients K m) 0 = 0 := by
    simpa only [zero_smul] using quadraticTarget_smul (0 : K) (0 : Coefficients K m) 0
  have hB : symmetricCompletion (0 : Fin m → Fin m → Fin 3 → K) z j = antisymmetric z j := by
    funext i q
    simp [symmetricCompletion]
  change P.coefficientLift (cubicCorrection (0 : Fin 3 → K) 0)
    (symmetricCompletion (quadraticTarget (0 : Coefficients K m) 0) z j) (δ j) = _
  rw [hC, hA, hB]

/-- One unit single-edge parameter in the trace multiplier at coordinate `i`. -/
def singleEdgeParameter (i : Fin m) (e : P.SingleEdge) : P.EliminatedParameters :=
  (0, 0, fun j => if j = i then fun e' => if e' = e then 1 else 0 else 0)

/-- The chosen multiplier has the edge lift, and every other multiplier is zero. -/
theorem parameterTraceCubic_singleEdge (i : Fin m) (e : P.SingleEdge) (j : Fin m) :
    P.parameterTraceCubic (P.singleEdgeParameter i e) j =
      if j = i then P.edgeCubic e else 0 := by
  unfold singleEdgeParameter
  rw [P.parameterTraceCubic_zeroNormal]
  have hz : antisymmetric (0 : Edge m → Fin 3 → K) j = 0 := by
    funext a q
    simp [antisymmetric]
  rw [hz]
  by_cases hj : j = i
  · subst j
    simp [edgeCubic]
  · simp [hj, P.coefficientLift_zero]

/-- A unit single-edge coordinate gives the two local edge column families of `Φ`. -/
theorem parameterPhi_singleEdge {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (i : Fin m) (e : P.SingleEdge) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ (P.singleEdgeParameter i e) k).val =
      X i * C (P.edgeLinear e k) * X e.val.val.1 * X e.val.val.2 := by
  rw [P.parameterPhi_polynomial, productNormal1, Finset.sum_eq_single i]
  · rw [P.parameterTraceCubic_singleEdge, ite_eq_left rfl, P.traceA_edgeCubic]
    ring
  · intro j _ hj
    rw [P.parameterTraceCubic_singleEdge, ite_eq_right hj]
    simp [traceA_zero]
  · simp

/-- A mixed quadratic in one antisymmetric edge coordinate. -/
def mixedEdgeParameter (e : Edge m) (Q : Fin 3 → K) : P.EliminatedParameters :=
  (0, fun e' => if e' = e then Q else 0, 0)

private theorem antisymmetric_unit_apply (e : Edge m) (Q : Fin 3 → K)
    (i j : Fin m) (q : Fin 3) :
    antisymmetric (fun e' => if e' = e then Q else 0) i j q =
      if i = e.val.1 ∧ j = e.val.2 then Q q
      else if i = e.val.2 ∧ j = e.val.1 then -Q q else 0 := by
  by_cases hij : i < j
  · have hforward : (⟨(i, j), hij⟩ : Edge m) = e ↔ i = e.val.1 ∧ j = e.val.2 := by
      rw [Subtype.ext_iff, Prod.mk.injEq]
    have hreverse : ¬ (i = e.val.2 ∧ j = e.val.1) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge e.property.le) hij
    by_cases he : (⟨(i, j), hij⟩ : Edge m) = e
    · simp only [antisymmetric, dite_eq_left hij, ite_eq_left he, ite_eq_left (hforward.mp he)]
    · simp only [antisymmetric, dite_eq_left hij, ite_eq_right he, ite_eq_right (hforward.not.mp he),
        ite_eq_right hreverse, Pi.zero_apply]
  · have hforward : ¬ (i = e.val.1 ∧ j = e.val.2) := by
      rintro ⟨rfl, rfl⟩
      exact hij e.property
    by_cases hji : j < i
    · have hreverse : (⟨(j, i), hji⟩ : Edge m) = e ↔ i = e.val.2 ∧ j = e.val.1 := by
        rw [Subtype.ext_iff, Prod.mk.injEq, and_comm]
      by_cases he : (⟨(j, i), hji⟩ : Edge m) = e
      · simp only [antisymmetric, dite_eq_right hij, dite_eq_left hji, ite_eq_left he, ite_eq_right hforward,
          ite_eq_left (hreverse.mp he)]
      · simp only [antisymmetric, dite_eq_right hij, dite_eq_left hji, ite_eq_right he, ite_eq_right hforward,
          ite_eq_right (hreverse.not.mp he), Pi.zero_apply, neg_zero]
    · have hreverse : ¬ (i = e.val.2 ∧ j = e.val.1) := by
        rintro ⟨rfl, rfl⟩
        exact hji e.property
      simp only [antisymmetric, dite_eq_right hij, dite_eq_right hji, ite_eq_right hforward, ite_eq_right hreverse]

/-- A mixed edge gives the lift at its other endpoint in each endpoint multiplier. -/
theorem parameterTraceCubic_mixedEdge (e : Edge m) (Q : Fin 3 → K) (i : Fin m) :
    P.parameterTraceCubic (P.mixedEdgeParameter e Q) i =
      if i = e.val.1 then P.mixedCubic e.val.2 Q
      else if i = e.val.2 then P.mixedCubic e.val.1 (-Q) else 0 := by
  unfold mixedEdgeParameter
  rw [P.parameterTraceCubic_zeroNormal]
  have hrow : antisymmetric (fun e' => if e' = e then Q else 0) i =
      if i = e.val.1 then mixedArray e.val.2 Q
      else if i = e.val.2 then mixedArray e.val.1 (-Q) else 0 := by
    funext j q
    rw [antisymmetric_unit_apply]
    by_cases h₁ : i = e.val.1
    · subst i
      by_cases hj : j = e.val.2 <;> simp [mixedArray, ne_of_lt e.property, hj]
    · by_cases h₂ : i = e.val.2
      · subst i
        by_cases hj : j = e.val.1 <;> simp [mixedArray, h₁, hj]
      · simp [h₁, h₂]
  rw [hrow]
  by_cases h₁ : i = e.val.1
  · simp [h₁, mixedCubic]
  · by_cases h₂ : i = e.val.2
    · subst i
      simp [h₁, mixedCubic]
    · simp [h₁, h₂, P.coefficientLift_zero]

private theorem mixedCubic_neg (c : Fin m) (Q : Fin 3 → K) :
    P.mixedCubic c (-Q) = -P.mixedCubic c Q := by
  apply P.kernelCoordinatesEquiv.injective
  rw [map_neg]
  unfold mixedCubic
  rw [P.kernelCoordinatesEquiv_coefficientLift, P.kernelCoordinatesEquiv_coefficientLift]
  refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
  funext i q
  by_cases h : i = c <;> simp [mixedArray, h]

private theorem traceA_neg (u : Coefficients K m) (k : Fin 2) : traceA (-u) k = -traceA u k := by
  have h (i j : Fin m) :
      upperCoefficient (-u).2.2.1 (-u).2.2.2 i j k =
        -upperCoefficient u.2.2.1 u.2.2.2 i j k := by
    by_cases hij : i < j
    · simp [upperCoefficient, hij]
    · by_cases he : i = j <;> simp [upperCoefficient, hij, he]
  simp only [traceA, traceQuadratic, h, map_neg, neg_mul, Finset.sum_neg_distrib]

/-- The mixed column is the endpoint product times the difference of the local lifts. -/
theorem parameterPhi_mixedEdge {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (e : Edge m) (Q : Fin 3 → K) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ (P.mixedEdgeParameter e Q) k).val =
      X e.val.1 * X e.val.2 *
        ((∑ j, C (P.mixedLinear e.val.2 Q j k) * X j) -
          (∑ j, C (P.mixedLinear e.val.1 Q j k) * X j)) := by
  rw [P.parameterPhi_polynomial, productNormal1]
  rw [Finset.sum_eq_add_of_mem e.val.1 e.val.2 (Finset.mem_univ _) (Finset.mem_univ _)
    (ne_of_lt e.property) (by
      intro i _ hi
      rw [P.parameterTraceCubic_mixedEdge, ite_eq_right hi.1, ite_eq_right hi.2]
      simp [traceA_zero])]
  simp [P.parameterTraceCubic_mixedEdge, ne_of_gt e.property,
    P.mixedCubic_neg, traceA_neg, P.traceA_mixedCubic]
  ring

end IdealGeneration.CubicSupported.Parameters
