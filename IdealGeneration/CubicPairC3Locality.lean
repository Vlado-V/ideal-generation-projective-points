module

public import IdealGeneration.CubicB11Actual
public import IdealGeneration.CubicMixedLocality
public import IdealGeneration.CubicPairC3Graph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Locality of the actual C.3 pair core over an arbitrary field. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open MvPolynomial Parameters CubicPair CubicMixedLocality
open QuadraticTraceRestriction (sum_over_embedding)

variable {K : Type*} [Field K] {k : ℕ}

/-- The local normal-linear coefficients restricted to the five old trace coordinates. -/
def localC3Coefficients (L : Parameters K 7) : PairLiftCoefficients K :=
  fun c q i r => L.mixedLinear (centerIndex c) (normalBasis q) (Fin.castAdd 2 i) r

/-- The weighted C.3 matrix evaluated from the seven-coordinate chart. -/
def localC3Matrix (L : Parameters K 7) (samples : Fin 13 → Fin 7 → K) :
    Matrix (Fin 26) (Fin 26) K :=
  Matrix.of fun r c => functionColumn (localC3Coefficients L)
    (L.edgeSlope c3PairEdgeOne 0) (L.edgeSlope c3PairEdgeTwo 0) c
    (samples (pairCoreRowEquiv r).1) (pairCoreRowEquiv r).2

private theorem mem_range_pairC3Trace (j : Fin k) {i : Fin (10 + 2 * k)}
    (hi : i ∈ pairSupport j) : i ∈ Set.range (pairC3Trace j) := by
  rcases (mem_pairSupport_values j i).mp hi with ha | hb | h0 | h5 | h6
  · exact ⟨4, Fin.ext ha.symm⟩
  · exact ⟨3, Fin.ext hb.symm⟩
  · exact ⟨0, Fin.ext h0.symm⟩
  · exact ⟨1, Fin.ext h5.symm⟩
  · exact ⟨2, Fin.ext h6.symm⟩

private theorem sum_mixedLinear_eq_c3 (Q : Parameters K ((10 + 2 * k) + 2)) (L : Parameters K 7)
    (j : Fin k) (h : ∀ a : Fin 4, AgreesAt L Q (pairC3AmbientEmbedding j)
      (pairC3Ambient_strictMono j) (centerIndex a)) (c : Fin 4) (q : Fin 3)
    (y : Fin (10 + 2 * k) → K) (hy : ∀ i, i ∉ pairSupport j → y i = 0)
    (w : Fin 2 → K) (r : Fin 2) :
    (∑ i, Q.mixedLinear (pairC3AmbientEmbedding j (centerIndex c)) (normalBasis q) i r *
      extendTrace y i) = basisLiftValue (localC3Coefficients L) c q (pairC3Point j y w) r := by
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
  rw [he, ← mixedLinear_eq_of_agreesAt (h c) (normalBasis q) (Fin.castAdd 2 l)]
  change localC3Coefficients L c q l r * extendTrace y
      (pairC3Ambient j (Fin.castAdd 2 l)) =
    localC3Coefficients L c q l r * pairC3Point j y w (Fin.castAdd 2 l)
  rw [pairC3Ambient_old, extendTrace_old, pairC3Point, Fin.addCases_left]
  rfl

private theorem center_B (j : Fin k) :
    pairC3AmbientEmbedding j (centerIndex 0) = (pairB j).castAdd 2 := rfl

private theorem center_A (j : Fin k) :
    pairC3AmbientEmbedding j (centerIndex 1) = (pairA j).castAdd 2 := rfl

private theorem center_new (j : Fin k) (b : Fin 2) :
    pairC3AmbientEmbedding j (centerIndex (Fin.natAdd 2 b)) = Fin.natAdd (10 + 2 * k) b := by
  fin_cases b <;> rfl

private theorem shift_slope (u : Fin 2) (τ : K) :
    shiftLinear u ![τ, -1] = τ • normalBasis (Fin.castAdd 1 u) - normalBasis u.succ := by
  funext a
  fin_cases u <;> fin_cases a <;> simp [shiftLinear, normalBasis]

private theorem actualB7Data_pairC3LiftValues_of_agreesAt
    (Q : Parameters K ((10 + 2 * k) + 2)) (L : Parameters K 7) (j : Fin k)
    (h : ∀ a : Fin 4, AgreesAt L Q (pairC3AmbientEmbedding j)
      (pairC3Ambient_strictMono j) (centerIndex a)) (y : Fin (10 + 2 * k) → K)
    (hy : ∀ i, i ∉ pairSupport j → y i = 0) (w : Fin 2 → K) (r : Fin 2) :
    PairC3LiftValues (actualB7Data Q) j (localC3Coefficients L) y w r := by
  have hsum (c : Fin 4) (q : Fin 3) := sum_mixedLinear_eq_c3 Q L j h c q y hy w r
  constructor
  · intro b q
    change eval (extendTrace y)
      ((∑ i, C (Q.mixedLinear (Fin.natAdd (10 + 2 * k) b) (normalBasis q) i r) * X i) -
        (∑ i, C (Q.mixedLinear (Fin.castAdd 2 (pairA j)) (normalBasis q) i r) * X i)) = _
    simp only [map_sub, map_sum, map_mul, eval_C, eval_X]
    rw [← center_new j b, ← center_A j, hsum, hsum]
  · intro b q
    change eval (extendTrace y)
      ((∑ i, C (Q.mixedLinear (Fin.natAdd (10 + 2 * k) b) (normalBasis q) i r) * X i) -
        (∑ i, C (Q.mixedLinear (Fin.castAdd 2 (pairB j)) (normalBasis q) i r) * X i)) = _
    simp only [map_sub, map_sum, map_mul, eval_C, eval_X]
    rw [← center_new j b, ← center_B j, hsum, hsum]
  · intro b u
    let τ := pairC3Slope (actualB7Data Q) j b
    let c := Fin.natAdd (10 + 2 * k) b
    change eval (extendTrace y) (∑ i, C (Q.mixedLinear c (shiftLinear u ![τ, -1]) i r) * X i) = _
    rw [shift_slope]
    simp only [map_sum, map_mul, eval_C, eval_X]
    have hlinear (i : Fin ((10 + 2 * k) + 2)) :
        Q.mixedLinear c (τ • normalBasis (Fin.castAdd 1 u) - normalBasis u.succ) i r =
          τ * Q.mixedLinear c (normalBasis (Fin.castAdd 1 u)) i r - Q.mixedLinear c (normalBasis u.succ) i r := by
      have he : mixedLinearMap Q c i (τ • normalBasis (Fin.castAdd 1 u) - normalBasis u.succ) =
          τ • mixedLinearMap Q c i (normalBasis (Fin.castAdd 1 u)) - mixedLinearMap Q c i (normalBasis u.succ) := by
        rw [map_sub, map_smul]
      simpa only [mixedLinearMap_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using congrFun he r
    simp only [hlinear, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [c]
    rw [← center_new j b, hsum, hsum]

/-- Local agreement at the four lift centers determines the entire actual pair core. -/
theorem pairCoreMatrix_eq_localC3Matrix
    (Q : Parameters K ((10 + 2 * k) + 2)) (L : Parameters K 7) (j : Fin k)
    (D : PairBlockData K k j) (hD : D.coreColumn = canonicalPairCoreColumn j)
    (h : ∀ a : Fin 4, AgreesAt L Q (pairC3AmbientEmbedding j)
      (pairC3Ambient_strictMono j) (centerIndex a)) :
    pairCoreMatrix (actualB7Data Q) D =
      localC3Matrix L (fun i => pairC3Point j (D.point i) (D.weight i)) := by
  have hOne := congrFun ((h 1).edge_eq c3PairEdgeOne (Or.inl rfl)).2.2.1 0
  have hTwo := congrFun ((h 0).edge_eq c3PairEdgeTwo (Or.inl rfl)).2.2.1 0
  change L.edgeSlope c3PairEdgeOne 0 = Q.edgeSlope (pairC3Edge j c3PairEdgeOne) 0 at hOne
  change L.edgeSlope c3PairEdgeTwo 0 = Q.edgeSlope (pairC3Edge j c3PairEdgeTwo) 0 at hTwo
  rw [pairC3Edge_one] at hOne
  rw [pairC3Edge_two] at hTwo
  change _ = pairC3Slope (actualB7Data Q) j 0 at hOne
  change _ = pairC3Slope (actualB7Data Q) j 1 at hTwo
  rw [pairCoreMatrix_eq_c3 _ D hD (localC3Coefficients L)
    (fun i r => actualB7Data_pairC3LiftValues_of_agreesAt Q L j h (D.point i)
      (D.supported i) (D.weight i) r), ← hOne, ← hTwo]
  rfl

end IdealGeneration.CubicSupported.B5
