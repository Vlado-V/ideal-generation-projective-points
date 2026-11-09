module

public import IdealGeneration.CubicB11Actual
public import IdealGeneration.CubicMixedLocality
public import IdealGeneration.CubicPairC3Graph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The C.3 determinant on the actual lower-order cubic columns. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open MvPolynomial Parameters CubicPair CubicPair.RationalConstruction CubicMixedLocality
open QuadraticTraceRestriction (sum_over_embedding)

variable {k : ℕ}

/-- The parameters that are used by the four C.3 lift centers. -/
def AgreesWithC3 (Q : Parameters ℚ ((10 + 2 * k) + 2)) (j : Fin k) : Prop :=
  ∀ c : Fin 4, AgreesAt c3Parameters Q (pairC3AmbientEmbedding j)
    (pairC3Ambient_strictMono j) (centerIndex c)

private theorem mem_range_pairC3Trace (j : Fin k) {i : Fin (10 + 2 * k)}
    (hi : i ∈ pairSupport j) : i ∈ Set.range (pairC3Trace j) := by
  rcases (mem_pairSupport_values j i).mp hi with ha | hb | h0 | h5 | h6
  · exact ⟨4, Fin.ext ha.symm⟩
  · exact ⟨3, Fin.ext hb.symm⟩
  · exact ⟨0, Fin.ext h0.symm⟩
  · exact ⟨1, Fin.ext h5.symm⟩
  · exact ⟨2, Fin.ext h6.symm⟩

private theorem sum_mixedLinear_eq_c3 (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (j : Fin k) (h : AgreesWithC3 Q j) (c : Fin 4) (q : Fin 3)
    (y : Fin (10 + 2 * k) → ℚ) (hy : ∀ i, i ∉ pairSupport j → y i = 0)
    (w : Fin 2 → ℚ) (r : Fin 2) :
    (∑ i, Q.mixedLinear (pairC3AmbientEmbedding j (centerIndex c)) (c3Basis q) i r *
      extendTrace y i) = basisLiftValue restrictedLiftCoefficientsQ c q (pairC3Point j y w) r := by
  let e := (pairC3TraceEmbedding j).trans (Fin.castAddEmb 2)
  have hoff (i : Fin ((10 + 2 * k) + 2)) : i ∉ Set.range e → extendTrace y i = 0 := by
    refine Fin.addCases (m := 10 + 2 * k) (n := 2) (fun l hl => ?_) (fun b _ => ?_) i
    · rw [extendTrace_old]
      apply hy
      intro hmem
      obtain ⟨a, ha⟩ := mem_range_pairC3Trace j hmem
      exact hl ⟨a, congrArg (Fin.castAdd 2) ha⟩
    · exact extendTrace_new y b
  rw [sum_over_embedding e _ (fun i hi => by simp [hoff i hi])]
  unfold basisLiftValue
  apply Finset.sum_congr rfl
  intro l _
  have he : e l = pairC3AmbientEmbedding j (Fin.castAdd 2 l) := by
    change (pairC3Trace j l).castAdd 2 = pairC3Ambient j (Fin.castAdd 2 l)
    rw [pairC3Ambient_old]
  rw [he, mixedLinear_eq_c3_coefficients c (h c) q (Fin.castAdd 2 l) r]
  change liftCoefficientsQ c q (Fin.castAdd 2 l) r * extendTrace y
      (pairC3Ambient j (Fin.castAdd 2 l)) =
    liftCoefficientsQ c q (Fin.castAdd 2 l) r * pairC3Point j y w (Fin.castAdd 2 l)
  rw [pairC3Ambient_old, extendTrace_old, pairC3Point, Fin.addCases_left]
  rfl

private theorem center_B (j : Fin k) :
    pairC3AmbientEmbedding j (centerIndex 0) = (pairB j).castAdd 2 := rfl

private theorem center_A (j : Fin k) :
    pairC3AmbientEmbedding j (centerIndex 1) = (pairA j).castAdd 2 := rfl

private theorem center_new (j : Fin k) (b : Fin 2) :
    pairC3AmbientEmbedding j (centerIndex (Fin.natAdd 2 b)) = Fin.natAdd (10 + 2 * k) b := by
  fin_cases b <;> rfl

private theorem shift_slope (u : Fin 2) (τ : ℚ) :
    shiftLinear u ![τ, -1] = τ • c3Basis (Fin.castAdd 1 u) - c3Basis u.succ := by
  funext a
  fin_cases u <;> fin_cases a <;> simp [shiftLinear, c3Basis]

/-- The actual weighted columns use the checked C.3 lift values on the five-coordinate support. -/
theorem actualB7Data_pairC3LiftValues (Q : Parameters ℚ ((10 + 2 * k) + 2)) (j : Fin k)
    (h : AgreesWithC3 Q j) (y : Fin (10 + 2 * k) → ℚ)
    (hy : ∀ i, i ∉ pairSupport j → y i = 0) (w : Fin 2 → ℚ) (r : Fin 2) :
    PairC3LiftValues (actualB7Data Q) j restrictedLiftCoefficientsQ y w r := by
  have hsum (c : Fin 4) (q : Fin 3) := sum_mixedLinear_eq_c3 Q j h c q y hy w r
  constructor
  · intro b q
    change eval (extendTrace y)
      ((∑ i, C (Q.mixedLinear (Fin.natAdd (10 + 2 * k) b) (c3Basis q) i r) * X i) -
        (∑ i, C (Q.mixedLinear (Fin.castAdd 2 (pairA j)) (c3Basis q) i r) * X i)) = _
    simp only [map_sub, map_sum, map_mul, eval_C, eval_X]
    rw [← center_new j b, ← center_A j, hsum, hsum]
  · intro b q
    change eval (extendTrace y)
      ((∑ i, C (Q.mixedLinear (Fin.natAdd (10 + 2 * k) b) (c3Basis q) i r) * X i) -
        (∑ i, C (Q.mixedLinear (Fin.castAdd 2 (pairB j)) (c3Basis q) i r) * X i)) = _
    simp only [map_sub, map_sum, map_mul, eval_C, eval_X]
    rw [← center_new j b, ← center_B j, hsum, hsum]
  · intro b u
    let τ := pairC3Slope (actualB7Data Q) j b
    let c := Fin.natAdd (10 + 2 * k) b
    change eval (extendTrace y) (∑ i, C (Q.mixedLinear c (shiftLinear u ![τ, -1]) i r) * X i) = _
    rw [shift_slope]
    simp only [map_sum, map_mul, eval_C, eval_X]
    have hlinear (i : Fin ((10 + 2 * k) + 2)) :
        Q.mixedLinear c (τ • c3Basis (Fin.castAdd 1 u) - c3Basis u.succ) i r =
          τ * Q.mixedLinear c (c3Basis (Fin.castAdd 1 u)) i r - Q.mixedLinear c (c3Basis u.succ) i r := by
      have he : mixedLinearMap Q c i (τ • c3Basis (Fin.castAdd 1 u) - c3Basis u.succ) =
          τ • mixedLinearMap Q c i (c3Basis (Fin.castAdd 1 u)) - mixedLinearMap Q c i (c3Basis u.succ) := by
        rw [map_sub, map_smul]
      simpa only [mixedLinearMap_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using congrFun he r
    simp only [hlinear, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [c]
    rw [← center_new j b, hsum, hsum]

private theorem slopes_eq_c3 (Q : Parameters ℚ ((10 + 2 * k) + 2)) (j : Fin k)
    (h : AgreesWithC3 Q j) : pairC3Slope (actualB7Data Q) j 0 = 810 ∧
      pairC3Slope (actualB7Data Q) j 1 = 479 := by
  constructor
  · have he := (h 1).edge_eq c3PairEdgeOne (Or.inl rfl)
    have hs := congrFun he.2.2.1 0
    change c3Parameters.edgeSlope c3PairEdgeOne 0 = Q.edgeSlope (pairC3Edge j c3PairEdgeOne) 0 at hs
    rw [pairC3Edge_one] at hs
    exact hs.symm.trans (by decide +kernel)
  · have he := (h 0).edge_eq c3PairEdgeTwo (Or.inl rfl)
    have hs := congrFun he.2.2.1 0
    change c3Parameters.edgeSlope c3PairEdgeTwo 0 = Q.edgeSlope (pairC3Edge j c3PairEdgeTwo) 0 at hs
    rw [pairC3Edge_two] at hs
    exact hs.symm.trans (by decide +kernel)

/-- The literal C.3 determinant for the actual supported lower columns. -/
theorem actual_pairCoreMatrix_det_ne_zero_of_agreesWithC3
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (j : Fin k) (h : AgreesWithC3 Q j)
    (faceParameter : PairFullFace k j → ℚ) (hface : ∀ F, faceParameter F ≠ 0) :
    (pairCoreMatrix (actualB7Data Q) (c3PairBlockData ℚ j faceParameter hface)).det ≠ 0 := by
  obtain ⟨h0, h1⟩ := slopes_eq_c3 Q j h
  apply c3PairBlockData_det_ne_zero _ j faceParameter hface _ h0 h1
  dsimp only
  intro i r
  let D := c3PairBlockData ℚ j faceParameter hface
  exact actualB7Data_pairC3LiftValues Q j h (D.point i) (D.supported i) (D.weight i) r

end IdealGeneration.CubicSupported.B5
