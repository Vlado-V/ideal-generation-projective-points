module

public import IdealGeneration.TripleNormalEdgeOrder
public import IdealGeneration.TripleNormalGroupedLeadingBlock

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The ordered edges in the enlarged base coordinates -/

noncomputable section
namespace IdealGeneration.TripleNormal
open EdgeOrder
set_option maxHeartbeats 600000

variable {N : ℕ}

/-- The old nonroot coordinate in the enlarged base. -/
def nonrootBaseIndex (i : Fin N) : Fin (N + 3 + 3) :=
  (i.castAdd 3).castAdd 3

/-- The chosen root coordinate in the enlarged base. -/
def rootBaseIndex (i : Fin 3) : Fin (N + 3 + 3) :=
  (i.natAdd N).castAdd 3

/-- The new base coordinate after the old nonroots and roots. -/
def newEdgeBaseIndex (i : Fin 3) : Fin (N + 3 + 3) :=
  i.natAdd (N + 3)

/-- Actual endpoints of each nonroot, triangle, and root edge. -/
def edgeEndpoints : Edge N → Fin (N + 3 + 3) × Fin (N + 3 + 3)
  | .inl (i, b) => (nonrootBaseIndex i, newEdgeBaseIndex b)
  | .inr (.inl e) => (newEdgeBaseIndex e.val.1, newEdgeBaseIndex e.val.2)
  | .inr (.inr (i, b)) => (rootBaseIndex i, newEdgeBaseIndex b)

/-- All curve weights are doubled so half-integer thresholds become integers. -/
def doubledVertexWeight (N : ℕ) : Fin (N + 3 + 3) → ℕ :=
  Fin.addCases (Fin.addCases (fun i => 2 * oldWeight i) (fun i => 2 * rootWeight N i))
    (fun b => 2 * newWeight N b)

@[simp] theorem doubledVertexWeight_nonroot (i : Fin N) :
    doubledVertexWeight N (nonrootBaseIndex i) = 2 * oldWeight i := by
  simp [doubledVertexWeight, nonrootBaseIndex]

@[simp] theorem doubledVertexWeight_root (i : Fin 3) :
    doubledVertexWeight N (rootBaseIndex i) = 2 * rootWeight N i := by
  simp [doubledVertexWeight, rootBaseIndex]

@[simp] theorem doubledVertexWeight_new (b : Fin 3) :
    doubledVertexWeight N (newEdgeBaseIndex b) = 2 * newWeight N b := by
  simp [doubledVertexWeight, newEdgeBaseIndex]

/-- Each edge has two distinct actual endpoints. -/
theorem edgeEndpoints_ne (e : Edge N) : (edgeEndpoints e).1 ≠ (edgeEndpoints e).2 := by
  rcases e with ⟨i, b⟩ | e | ⟨i, b⟩
  · intro he
    have hv := congrArg Fin.val he
    change i.val = N + 3 + b.val at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    change N + 3 + e.val.1.val = N + 3 + e.val.2.val at hv
    have hl : e.val.1.val < e.val.2.val := e.property
    omega
  · intro he
    have hv := congrArg Fin.val he
    change N + i.val = N + 3 + b.val at hv
    omega

/-- The actual monomial-curve degree is twice the ordered edge degree. -/
theorem edgeEndpointWeight_eq (e : Edge N) :
    doubledVertexWeight N (edgeEndpoints e).1 + doubledVertexWeight N (edgeEndpoints e).2 =
      2 * degree N e := by
  rcases e with ⟨i, b⟩ | e | ⟨i, b⟩ <;>
    simp [edgeEndpoints, degree, nonrootDegree, triangleDegree, rootDegree, Nat.mul_add]

/-- Curve degrees distinguish all three edge groups and every edge within them. -/
theorem edgeEndpointWeight_injective (hN : 5 ≤ N) :
    Function.Injective (fun e : Edge N =>
      doubledVertexWeight N (edgeEndpoints e).1 + doubledVertexWeight N (edgeEndpoints e).2) := by
  intro e f hef
  obtain ⟨i, rfl⟩ := (allEdges hN).surjective e
  obtain ⟨j, rfl⟩ := (allEdges hN).surjective f
  have hdeg : degree N (allEdges hN i) = degree N (allEdges hN j) := by
    simp only [edgeEndpointWeight_eq] at hef
    omega
  exact congrArg (allEdges hN) ((allEdges_degree_strictMono hN).injective hdeg)

/-- The plane groups followed by the root groups, in flattened order. -/
def flattenedEdges (hN : 5 ≤ N) : Fin (3 * (N + 1) + 9) ≃ Edge N :=
  (finCongr (by omega : 3 * (N + 1) + 9 = N * 3 + 12)).trans (allEdges hN)

/-- The undoubled degrees used to choose the successive thresholds. -/
def flattenedEdgeDegree (hN : 5 ≤ N) : Fin (3 * (N + 1) + 9) → ℕ :=
  fun i => degree N (flattenedEdges hN i)

theorem flattenedEdgeDegree_strictMono (hN : 5 ≤ N) :
    StrictMono (flattenedEdgeDegree hN) := by
  intro i j hij
  exact allEdges_degree_strictMono hN hij

/-- The flattened index of one of the three edges in a plane group. -/
def planeEdgeIndex (g : Fin (N + 1)) (e : Fin 3) : Fin (3 * (N + 1) + 9) :=
  ⟨3 * g.val + e.val, by omega⟩

/-- The flattened index of a root edge after all plane groups. -/
def rootEdgeIndex (N : ℕ) (r : Fin 9) : Fin (3 * (N + 1) + 9) :=
  ⟨3 * (N + 1) + r.val, by omega⟩

/-- The leading edge attached to each column of the grouped block. -/
def groupedLeadEdge (hN : 5 ≤ N) : GroupedLeadingCol (N + 1) → Edge N
  | .inl (g, e, _) => flattenedEdges hN (planeEdgeIndex g e)
  | .inr (r, _) => flattenedEdges hN (rootEdgeIndex N r)

@[simp] theorem groupedLeadEdge_plane_nonroot (hN : 5 ≤ N) (g : Fin N) (e : Fin 3) (i : Fin 2) :
    groupedLeadEdge hN (.inl (g.castSucc, e, i)) = .inl (edgeAt hN g e) := by
  change allEdges hN (Fin.cast (by omega) (planeEdgeIndex g.castSucc e)) = _
  have hi : Fin.cast (by omega : 3 * (N + 1) + 9 = N * 3 + 12)
      (planeEdgeIndex g.castSucc e) = (finProdFinEquiv (g, e)).castAdd 12 := by
    apply Fin.ext
    change 3 * g.val + e.val = e.val + 3 * g.val
    omega
  rw [hi, allEdges_nonroot, orderedEdge_apply_prod]

@[simp] theorem groupedLeadEdge_plane_triangle (hN : 5 ≤ N) (e : Fin 3) (i : Fin 2) :
    groupedLeadEdge hN (.inl (Fin.last N, e, i)) = .inr (.inl (triangleAt e)) := by
  change allEdges hN (Fin.cast (by omega) (planeEdgeIndex (Fin.last N) e)) = _
  have hi : Fin.cast (by omega : 3 * (N + 1) + 9 = N * 3 + 12)
      (planeEdgeIndex (Fin.last N) e) = (e.castAdd 9).natAdd (N * 3) := by
    apply Fin.ext
    change 3 * N + e.val = N * 3 + e.val
    omega
  rw [hi, allEdges_triangle]

@[simp] theorem groupedLeadEdge_root (hN : 5 ≤ N) (r : Fin 9) (i : Fin 3) :
    groupedLeadEdge hN (.inr (r, i)) = .inr (.inr (rootAt r)) := by
  change allEdges hN (Fin.cast (by omega) (rootEdgeIndex N r)) = _
  have hi : Fin.cast (by omega : 3 * (N + 1) + 9 = N * 3 + 12)
      (rootEdgeIndex N r) = (r.natAdd 3).natAdd (N * 3) := by
    apply Fin.ext
    change 3 * (N + 1) + r.val = N * 3 + (3 + r.val)
    omega
  rw [hi, allEdges_root]

private def singlePlaneRow : Fin 1 × Fin 3 ≃ Fin 3 where
  toFun := Prod.snd
  invFun i := (0, i)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

/-- All plane slots enumerate the nonroot edges followed by the triangle. -/
def planeEdgesEquiv (hN : 5 ≤ N) :
    Fin (N + 1) × Fin 3 ≃ NonrootEdge N ⊕ TriangleEdge :=
  (Equiv.prodCongr (finSumFinEquiv : Fin N ⊕ Fin 1 ≃ Fin (N + 1)).symm (Equiv.refl _)).trans
    ((Equiv.sumProdDistrib _ _ _).trans
      (Equiv.sumCongr (Equiv.ofBijective _ (edgeAt_bijective hN))
        (singlePlaneRow.trans (Equiv.ofBijective triangleAt triangleAt_bijective))))

@[simp] theorem planeEdgesEquiv_nonroot (hN : 5 ≤ N) (g : Fin N) (e : Fin 3) :
    planeEdgesEquiv hN (g.castSucc, e) = .inl (edgeAt hN g e) := by
  simp [planeEdgesEquiv, Equiv.sumCongr]

@[simp] theorem planeEdgesEquiv_triangle (hN : 5 ≤ N) (e : Fin 3) :
    planeEdgesEquiv hN (Fin.last N, e) = .inr (triangleAt e) := by
  simp [planeEdgesEquiv, Equiv.sumCongr, singlePlaneRow]

/-- Regard the two plane edge groups as part of the full ordered edge type. -/
def planeEdgeInclusion (N : ℕ) : (NonrootEdge N ⊕ TriangleEdge) ↪ Edge N :=
  Function.Embedding.sumMap (Function.Embedding.refl _) Function.Embedding.inl

/-- A plane column leads on its enumerated edge, independently of its coefficient slot. -/
theorem groupedLeadEdge_plane (hN : 5 ≤ N) (g : Fin (N + 1)) (e : Fin 3) (i : Fin 2) :
    groupedLeadEdge hN (.inl (g, e, i)) = planeEdgeInclusion N (planeEdgesEquiv hN (g, e)) := by
  refine Fin.lastCases ?_ (fun g => ?_) g
  · simp [planeEdgeInclusion]
  · simp [planeEdgeInclusion]

end IdealGeneration.TripleNormal
