module

public import IdealGeneration.TripleNormalGroupedInterpolation
public import IdealGeneration.TripleNormalNormalizedEdgeColumns
public import IdealGeneration.TripleNormalOrderedChords

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The normalized plane and root columns have the required ordered leading profile. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open EdgeOrder NormalizedEdgeColumns Matrix
open scoped Matrix

variable {K : Type*} [Field K] {N : ℕ}

def groupedBaseBasis (hN : 5 ≤ N) : GroupedLeadingCol (N + 1) → NormalizedInput K N
  | .inl (g, e, k) => planeColumn (planeEdgesEquiv hN (g, e)) k
  | .inr (r, a) => rootColumn (rootAt r).1 (rootAt r).2 a

def groupedBaseCoordinates (hN : 5 ≤ N) (x : NormalizedInput K N) :
    GroupedLeadingCol (N + 1) → K
  | .inl (g, e, k) => x.1 (planeEdgesEquiv hN (g, e)) k
  | .inr (r, a) => x.2 (rootAt r).1 (rootAt r).2 a

theorem groupedBaseBasis_expansion (hN : 5 ≤ N) (x : NormalizedInput K N) :
    ∑ j, groupedBaseCoordinates hN x j • groupedBaseBasis hN j = x := by
  rw [Fintype.sum_sum_type]
  refine (congrArg₂ (fun a b : NormalizedInput K N => a + b) ?_ ?_).trans (normalizedInput_sum_columns x).symm
  · let e := (Equiv.prodAssoc (Fin (N + 1)) (Fin 3) (Fin 2)).symm.trans
      (Equiv.prodCongr (planeEdgesEquiv hN) (Equiv.refl (Fin 2)))
    exact e.sum_comp (fun c : PlaneEdge N × Fin 2 => x.1 c.1 c.2 • planeColumn c.1 c.2)
  · let e := (Equiv.prodCongr (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm
      (Equiv.refl (Fin 3))).trans (Equiv.prodAssoc (Fin 3) (Fin 3) (Fin 3))
    exact e.sum_comp (fun c : Fin 3 × Fin 3 × Fin 3 =>
      x.2 c.1 c.2.1 c.2.2 • rootColumn c.1 c.2.1 c.2.2)

private theorem planeEdgeInclusion_eq (e : PlaneEdge N) :
    planeEdgeInclusion N e = planeEmbed e := by
  cases e <;> rfl

variable [CharZero K]
  (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
  (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, rootParameters t r ≠ 0)
  (hinj : Function.Injective (rootParameters t))
  (hq : ∀ r b, chordFactor (rootParameters t r) (v b) ≠ 0)

def groupedBaseColumn (hN : 5 ≤ N) (j : GroupedLeadingCol (N + 1)) : Output K N :=
  normalizedCoefficient ω t v hω hroots hinj hq (groupedBaseBasis hN j)

theorem groupedBaseColumn_degree_support (hN : 5 ≤ N)
    (j : GroupedLeadingCol (N + 1)) (e : Edge N)
    (he : degree N (groupedLeadEdge hN j) < degree N e) :
    groupedBaseColumn ω t v hω hroots hinj hq hN j e = 0 := by
  rcases j with ⟨g, b, k⟩ | ⟨r, a⟩
  · change normalizedCoefficient ω t v hω hroots hinj hq (planeColumn
      (planeEdgesEquiv hN (g, b)) k) e = 0
    apply normalizedCoefficient_planeColumn_off
    rw [groupedLeadEdge_plane, planeEdgeInclusion_eq] at he
    intro heq
    rw [heq] at he
    exact (lt_irrefl _) he
  · rw [groupedLeadEdge_root] at he
    rcases e with e | (e | ⟨r', b'⟩)
    · exact False.elim ((not_lt_of_ge (nonrootDegree_lt_rootDegree e (rootAt r)).le) he)
    · exact False.elim ((not_lt_of_ge (triangleDegree_lt_rootDegree N e.val.1 e.val.2
        (rootAt r)).le) he)
    · change normalizedCoefficient ω t v hω hroots hinj hq
        (rootColumn (rootAt r).1 (rootAt r).2 a) (rootEdge r' b') = 0
      apply normalizedCoefficient_rootColumn_off
      intro heq
      rw [heq] at he
      exact (lt_irrefl _) he

theorem groupedBaseColumn_planeTop (hN : 5 ≤ N) (g : Fin (N + 1)) (e : Fin 3) (k : Fin 2) :
    groupedPlaneTop (groupedBaseColumn ω t v hω hroots hinj hq hN) (groupedLeadEdge hN) g e k =
      endpointVector t v (groupedLeadEdge hN (.inl (g, e, 0))) k := by
  unfold groupedPlaneTop groupedBaseColumn
  rw [groupedLeadEdge_plane, groupedLeadEdge_plane, planeEdgeInclusion_eq]
  exact normalizedCoefficient_planeColumn_self ω t v hω hroots hinj hq _ k

theorem groupedBaseColumn_rootTop (hN : 5 ≤ N) (r : Fin 9) (a : Fin 3) :
    groupedRootTop (groupedBaseColumn ω t v hω hroots hinj hq hN) (groupedLeadEdge hN) r a =
      Pi.single a 1 := by
  unfold groupedRootTop groupedBaseColumn
  rw [groupedLeadEdge_root]
  exact normalizedCoefficient_rootColumn_self ω t v hω hroots hinj hq _ _ a

def groupedChordNormals (hN : 5 ≤ N) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (g : Fin (N + 1)) (e : Fin 3) : Fin 3 → K :=
  let edge := groupedLeadEdge hN (.inl (g, e, 0))
  chordNormal (endpointParameter t v edge 0) (endpointParameter t v edge 1)

def nonrootEmbedding (N : ℕ) : Fin N ↪ Fin (N + 3) :=
  ⟨Fin.castAdd 3, fun _ _ h => Fin.ext (congrArg (fun i : Fin (N + 3) => i.val) h)⟩

omit [CharZero K] in
theorem groupedChordNormals_matrix (hN : 5 ≤ N) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (g : Fin (N + 1)) :
    Matrix.of (groupedChordNormals hN t v g) =
      chordMatrix t v (orderedChordTriple hN (nonrootEmbedding N) (Fin.lastCases none some g)) := by
  ext e a
  refine Fin.lastCases ?_ (fun g => ?_) g
  · simp [groupedChordNormals, chordMatrix, orderedChordTriple, endpointParameter]
  · simp [groupedChordNormals, chordMatrix, orderedChordTriple, endpointParameter, nonrootEmbedding]
    rfl

omit [Field K] [CharZero K] in
private theorem endpointParameter_eq_append (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (e : Edge N) :
    endpointParameter t v e 0 = Fin.append t v (edgeEndpoints e).1 ∧
      endpointParameter t v e 1 = Fin.append t v (edgeEndpoints e).2 := by
  rcases e with ⟨i, b⟩ | e | ⟨r, b⟩ <;>
    simp [endpointParameter, edgeEndpoints, nonrootBaseIndex, rootBaseIndex, newEdgeBaseIndex,
      rootParameters]

/-- All normalized base columns have an injective evaluation on a nonempty
open set in the free trace points. -/
theorem groupedBaseColumn_principal_open (hN : 5 ≤ N)
    (hparams : Function.Injective (Fin.append t v))
    (hchords : ∀ g, (chordMatrix t v (orderedChordTriple hN (nonrootEmbedding N) g)).det ≠ 0) :
    ∃ P : MvPolynomial (Fin (2 * (N + 3) + 5) × Fin (N + 3 + 3)) K,
      (∃ a, MvPolynomial.eval a P ≠ 0) ∧
      ∀ a, MvPolynomial.eval a P ≠ 0 → Function.Injective
        (freeTraceMatrix (groupedFreePointIndex N) groupedEvalCoordinate
          (fun j => edgeQuadric edgeEndpoints (groupedBaseColumn ω t v hω hroots hinj hq hN j)) a).mulVec := by
  apply ordered_edge_interpolation_principal_open hN
    (groupedBaseColumn ω t v hω hroots hinj hq hN)
    (groupedBaseColumn_degree_support ω t v hω hroots hinj hq hN) (groupedChordNormals hN t v)
  · intro g e j
    rw [groupedBaseColumn_planeTop]
    exact endpointVector_orthogonal t v _ j
  · intro g
    rw [groupedChordNormals_matrix]
    exact hchords _
  · intro g e
    have htop : groupedPlaneTop (groupedBaseColumn ω t v hω hroots hinj hq hN)
        (groupedLeadEdge hN) g e = endpointVector t v (groupedLeadEdge hN (.inl (g, e, 0))) :=
      funext (groupedBaseColumn_planeTop ω t v hω hroots hinj hq hN g e)
    rw [htop]
    apply endpointVector_independent
    have he := endpointParameter_eq_append t v (groupedLeadEdge hN (.inl (g, e, 0)))
    rw [he.1, he.2]
    exact hparams.ne (edgeEndpoints_ne _)
  · intro r
    have he : groupedRootTop (groupedBaseColumn ω t v hω hroots hinj hq hN)
        (groupedLeadEdge hN) r = Pi.basisFun K (Fin 3) := by
      funext a
      rw [groupedBaseColumn_rootTop, Pi.basisFun_apply]
    rw [he]
    exact (Pi.basisFun K (Fin 3)).linearIndependent

end IdealGeneration.TripleNormal
