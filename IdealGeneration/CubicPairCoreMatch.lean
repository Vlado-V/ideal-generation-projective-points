module

public import IdealGeneration.CubicPairCoreColumns
public import IdealGeneration.CubicPairRationalConstruction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Comparing the evaluated pair core to the C.3 certificate. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicPair

variable {K : Type*} [Field K] {k : ℕ}

/-- The five C.3 trace coordinates, in increasing order. -/
def pairC3Trace (j : Fin k) : Fin 5 → Fin (10 + 2 * k) :=
  ![⟨0, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩, pairB j, pairA j]

/-- The C.3 sample packs the five trace coordinates and the two direction weights. -/
def pairC3Point (j : Fin k) (y : Fin (10 + 2 * k) → K) (w : Fin 2 → K) : Fin 7 → K :=
  fun i => @Fin.addCases 5 2 (fun _ => K) (y ∘ pairC3Trace j) w i

omit [Field K] in
private theorem pairC3Point_eq_vec (j : Fin k) (y : Fin (10 + 2 * k) → K) (w : Fin 2 → K) :
    pairC3Point j y w = ![y ⟨0, by omega⟩, y ⟨5, by omega⟩, y ⟨6, by omega⟩,
      y (pairB j), y (pairA j), w 0, w 1] := by
  funext i
  fin_cases i <;> rfl

/-- The two cross-edge slopes used by the extra and half-face columns. -/
def pairC3Slope (P : B7Data K (10 + 2 * k)) (j : Fin k) (b : Fin 2) : K :=
  P.cones.edgeSlope (newSlopeEdge b (activePairVertex j b)) 0

/-- The three required identities for the linear lift factors on a C.3 probe. -/
structure PairC3LiftValues (P : B7Data K (10 + 2 * k)) (j : Fin k)
    (coeff : PairLiftCoefficients K) (y : Fin (10 + 2 * k) → K) (w : Fin 2 → K) (r : Fin 2) : Prop where
  motionA : ∀ b q, P.motion b (pairA j) q y r =
    basisLiftValue coeff (Fin.natAdd 2 b) q (pairC3Point j y w) r -
      basisLiftValue coeff 1 q (pairC3Point j y w) r
  motionB : ∀ b q, P.motion b (pairB j) q y r =
    basisLiftValue coeff (Fin.natAdd 2 b) q (pairC3Point j y w) r -
      basisLiftValue coeff 0 q (pairC3Point j y w) r
  extra : ∀ b u, P.extra b (activePairVertex j b) u y r =
    pairC3Slope P j b * basisLiftValue coeff (Fin.natAdd 2 b) (Fin.castAdd 1 u) (pairC3Point j y w) r -
      basisLiftValue coeff (Fin.natAdd 2 b) u.succ (pairC3Point j y w) r

/-- Once the lift factors agree, each actual core column evaluates to the
corresponding entry of C.3. The half-face values follow from the graph labels. -/
theorem canonicalPairCoreColumn_value (P : B7Data K (10 + 2 * k)) (j : Fin k)
    (coeff : PairLiftCoefficients K) (y : Fin (10 + 2 * k) → K) (w : Fin 2 → K) (r : Fin 2)
    (h : PairC3LiftValues P j coeff y w r) (c : Fin 26) :
    b7Value P y w r (canonicalPairCoreColumn j c) =
      functionColumn coeff (pairC3Slope P j 0) (pairC3Slope P j 1) c (pairC3Point j y w) r := by
  have he0 := h.extra 0
  have he1 := h.extra 1
  simp [activePairVertex] at he0 he1
  fin_cases c <;>
    simp [canonicalPairCoreColumn, pairCoreLabelEquiv, pairCoreLabelColumn,
      finSumFinEquiv, Fin.addCases, b7Value, functionColumn, halfFaceValue, localValue,
      pairHalfLocalColumn, pairHalfFactors, activeNeighbor, localEndpoints, localSlopeEdge,
      pairC3Point_eq_vec, pairC3Slope, activePairVertex, otherPairVertex,
      h.motionA, h.motionB, he0, he1] <;> ring

/-- The entire core matrix agrees entrywise with the evaluation in C.3. -/
theorem pairCoreMatrix_eq_c3 (P : B7Data K (10 + 2 * k)) {j : Fin k}
    (D : PairBlockData K k j) (hD : D.coreColumn = canonicalPairCoreColumn j)
    (coeff : PairLiftCoefficients K)
    (h : ∀ i r, PairC3LiftValues P j coeff (D.point i) (D.weight i) r) :
    pairCoreMatrix P D = Matrix.of (fun r c =>
      functionColumn coeff (pairC3Slope P j 0) (pairC3Slope P j 1) c
        (pairC3Point j (D.point (pairCoreRowEquiv r).1) (D.weight (pairCoreRowEquiv r).1))
        (pairCoreRowEquiv r).2) := by
  ext r c
  have he := canonicalPairCoreColumn_value P j coeff (D.point (pairCoreRowEquiv r).1)
    (D.weight (pairCoreRowEquiv r).1) (pairCoreRowEquiv r).2 (h _ _) c
  simpa only [pairCoreMatrix, probeEntry, pairCoreProbe, Matrix.of_apply, hD] using he

/-- The rational C.3 certificate gives the nonzero actual core determinant
when its primitive slopes, samples and lift coefficients are matched. -/
theorem pairCoreMatrix_det_ne_zero_of_c3 [CharZero K]
    (P : B7Data K (10 + 2 * k)) {j : Fin k}
    (D : PairBlockData K k j) (hD : D.coreColumn = canonicalPairCoreColumn j)
    (h : ∀ i r, PairC3LiftValues P j
      (fun a q l t => (RationalConstruction.restrictedLiftCoefficientsQ a q l t : K))
      (D.point i) (D.weight i) r)
    (h0 : pairC3Slope P j 0 = 810) (h1 : pairC3Slope P j 1 = 479)
    (hx : ∀ i l, pairC3Point j (D.point i) (D.weight i) l =
      (RationalConstruction.samplePointsQ i l : K)) : (pairCoreMatrix P D).det ≠ 0 := by
  have hmat : pairCoreMatrix P D =
      RationalConstruction.constructionMatrixQ.map (Rat.castHom K) := by
    rw [pairCoreMatrix_eq_c3 P D hD _ h]
    ext r c
    have hpoint : pairC3Point j (D.point (pairCoreRowEquiv r).1) (D.weight (pairCoreRowEquiv r).1) =
        fun i => (RationalConstruction.rowPointQ r i : K) := by
      funext i
      exact hx _ i
    have hcomponent : (pairCoreRowEquiv r).2 = RationalConstruction.rowComponentQ r := rfl
    have he := map_functionColumn (Rat.castHom K) RationalConstruction.restrictedLiftCoefficientsQ
      810 479 c (RationalConstruction.rowPointQ r) (RationalConstruction.rowComponentQ r)
    simpa [RationalConstruction.constructionMatrixQ, h0, h1, hpoint, hcomponent] using he.symm
  rw [hmat]
  change (RationalConstruction.constructionMatrixQ.map (fun x : ℚ => (x : K))).det ≠ 0
  rw [← Rat.cast_det]
  exact_mod_cast RationalConstruction.constructionMatrixQ_det_ne_zero

end IdealGeneration.CubicSupported.B5
