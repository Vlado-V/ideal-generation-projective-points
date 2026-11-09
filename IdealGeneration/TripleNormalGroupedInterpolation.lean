module

public import IdealGeneration.TripleNormalCurveEvaluation
public import IdealGeneration.TripleNormalGroupedThresholds
public import IdealGeneration.TripleNormalEdgeCoordinates
public import IdealGeneration.TripleNormalBaseRankOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Realize the ordered plane and root blocks by actual monomial-curve evaluations. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix
open scoped Matrix

variable {K V E : Type*} [Field K] [Infinite K] [Fintype E] {G : ℕ}

def groupedEvalCoordinate : GroupedLeadingRow G → Fin 3
  | .inl (_, _, a) => a
  | .inr (_, a) => a

private instance (i : GroupedLeadingRow G) (j : GroupedLeadingCol G) :
    Decidable (groupedLeadingIncidence i j) := by
  rcases i with ⟨g, p, a⟩ | ⟨r, a⟩ <;> rcases j with ⟨g', e, b⟩ | ⟨r', b⟩ <;>
    unfold groupedLeadingIncidence <;> infer_instance

def groupedLeadingRowColEquiv (G : ℕ) : GroupedLeadingRow G ≃ GroupedLeadingCol G :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin G)) (Equiv.prodComm (Fin 2) (Fin 3)))
    (Equiv.refl _)

variable (coeff : GroupedLeadingCol G → E → Fin 3 → K) (lead : GroupedLeadingCol G → E)

def groupedPlaneTop (g : Fin G) (e : Fin 3) (j : Fin 2) : Fin 3 → K :=
  coeff (.inl (g, e, j)) (lead (.inl (g, e, j)))

def groupedRootTop (r : Fin 9) (j : Fin 3) : Fin 3 → K :=
  coeff (.inr (r, j)) (lead (.inr (r, j)))

omit [Infinite K] [Fintype E] in
private theorem groupedLeading_entry (i : GroupedLeadingRow G) (j : GroupedLeadingCol G) :
    (if groupedLeadingIncidence i j then coeff j (lead j) (groupedEvalCoordinate i) else 0) =
      groupedLeadingMatrix (groupedPlaneTop coeff lead) (groupedRootTop coeff lead) i j := by
  rcases i with ⟨g, p, a⟩ | ⟨r, a⟩ <;> rcases j with ⟨g', e, b⟩ | ⟨r', b⟩
  · by_cases he : g' = g
    · subst g'
      simp [groupedLeadingIncidence, groupedEvalCoordinate, groupedLeadingMatrix, groupedPlaneTop]
    · simp [groupedLeadingIncidence, groupedLeadingMatrix, he]
  · simp [groupedLeadingIncidence, groupedLeadingMatrix]
  · simp [groupedLeadingIncidence, groupedLeadingMatrix]
  · by_cases he : r' = r
    · subst r'
      simp [groupedLeadingIncidence, groupedEvalCoordinate, groupedLeadingMatrix, groupedRootTop]
    · simp [groupedLeadingIncidence, groupedLeadingMatrix, he]

/-- Weight bounds with the ordered incidence pattern give a genuine injective
matrix of evaluations on (2G+9) common base points. -/
theorem exists_grouped_edge_interpolation
    (ends : E → V × V) (weight : V → ℕ)
    (rowWeight : GroupedLeadingRow G → ℕ) (colWeight : GroupedLeadingCol G → ℕ)
    (hdeg : Function.Injective (edgeDegree ends weight))
    (hsupport : ∀ j e, edgeDegree ends weight (lead j) < edgeDegree ends weight e → coeff j e = 0)
    (hweight : ∀ i j, (groupedEvalBlock i + 1) * edgeDegree ends weight (lead j) ≤
      rowWeight i + colWeight j)
    (hinc : ∀ i j, rowWeight i + colWeight j =
      (groupedEvalBlock i + 1) * edgeDegree ends weight (lead j) ↔ groupedLeadingIncidence i j)
    (n : Fin G → Fin 3 → Fin 3 → K)
    (horth : ∀ g e j, n g e ⬝ᵥ groupedPlaneTop coeff lead g e j = 0)
    (hn : ∀ g, (Matrix.of (n g)).det ≠ 0)
    (hP : ∀ g e, LinearIndependent K (groupedPlaneTop coeff lead g e))
    (hR : ∀ r, LinearIndependent K (groupedRootTop coeff lead r)) :
    ∃ x : K, x ≠ 0 ∧ Function.Injective
      (Matrix.of fun (i : GroupedLeadingRow G) (j : GroupedLeadingCol G) =>
        MvPolynomial.eval (fun v => (x ^ (groupedEvalBlock i + 1)) ^ weight v)
          (edgeQuadric ends (coeff j) (groupedEvalCoordinate i))).mulVec := by
  let ec := groupedLeadingRowColEquiv G
  have hd := groupedLeadingMatrix_reindex_det_ne_zero
    (groupedPlaneTop coeff lead) (groupedRootTop coeff lead) n horth hn hP hR
    (Equiv.refl (GroupedLeadingRow G)) ec
  have heq : (Matrix.of fun (i j : GroupedLeadingRow G) =>
      if rowWeight i + colWeight (ec j) =
        (groupedEvalBlock i + 1) * edgeDegree ends weight (lead (ec j))
      then coeff (ec j) (lead (ec j)) (groupedEvalCoordinate i) else 0) =
      (groupedLeadingMatrix (groupedPlaneTop coeff lead) (groupedRootTop coeff lead)).submatrix
        (Equiv.refl (GroupedLeadingRow G)) ec := by
    ext i j
    change (if _ then _ else _) =
      groupedLeadingMatrix (groupedPlaneTop coeff lead) (groupedRootTop coeff lead) i (ec j)
    have he := groupedLeading_entry coeff lead i (ec j)
    by_cases h : groupedLeadingIncidence i (ec j)
    · rw [ite_eq_left ((hinc i (ec j)).mpr h)]
      rw [ite_eq_left h] at he
      exact he
    · rw [ite_eq_right (fun hh => h ((hinc i (ec j)).mp hh))]
      rw [ite_eq_right h] at he
      exact he
  obtain ⟨x, hx, hmx⟩ := exists_edge_interpolation ends weight (coeff ∘ ec) (lead ∘ ec)
    groupedEvalBlock groupedEvalCoordinate rowWeight (colWeight ∘ ec) hdeg
    (fun j e => hsupport (ec j) e) (fun i j => hweight i (ec j)) (heq.symm ▸ hd)
  let M : Matrix (GroupedLeadingRow G) (GroupedLeadingCol G) K :=
    Matrix.of fun i j => MvPolynomial.eval (fun v => (x ^ (groupedEvalBlock i + 1)) ^ weight v)
      (edgeQuadric ends (coeff j) (groupedEvalCoordinate i))
  have hi : Function.Injective (M.submatrix (Equiv.refl (GroupedLeadingRow G)) ec).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero hmx
  refine ⟨x, hx, ?_⟩
  change Function.Injective M.mulVec
  intro u v huv
  have he : (M.submatrix (Equiv.refl (GroupedLeadingRow G)) ec).mulVec (u ∘ ec) =
      (M.submatrix (Equiv.refl (GroupedLeadingRow G)) ec).mulVec (v ∘ ec) := by
    simpa [Matrix.submatrix_mulVec_equiv, Function.comp_def] using huv
  have he' := hi he
  funext j
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun he' (ec.symm j)

/-- Threshold potentials for all of the ordered columns simultaneously. -/
theorem exists_grouped_leading_weights (d : Fin (3 * G + 9) → ℕ) (hd : StrictMono d) :
    ∃ (rowWeight : GroupedLeadingRow G → ℕ) (colWeight : GroupedLeadingCol G → ℕ),
      (∀ i j, (groupedEvalBlock i + 1) * groupedColumnDegree d j ≤
        rowWeight i + colWeight j) ∧
      (∀ i j, rowWeight i + colWeight j =
        (groupedEvalBlock i + 1) * groupedColumnDegree d j ↔ groupedLeadingIncidence i j) := by
  classical
  have hcol (j : GroupedLeadingCol G) := exists_columnWeight_for_thresholds
    (groupedThreshold d) (groupedAssignedBlock j) (groupedColumnDegree d j)
    (groupedThreshold_le_before d hd j) (groupedThreshold_ge_after d hd j)
  choose c hc using hcol
  refine ⟨fun i => blockThresholdWeight (groupedThreshold d) (groupedEvalBlock i), c, ?_, ?_⟩
  · exact fun i j => (hc j (groupedEvalBlock i)).1
  · exact fun i j => (hc j (groupedEvalBlock i)).2.trans (groupedThreshold_interval_iff d hd i j)

variable {N : ℕ}

def groupedFreePointIndex (N : ℕ) (i : GroupedLeadingRow (N + 1)) : Fin (2 * (N + 3) + 5) :=
  ⟨groupedEvalBlock i, by
    rcases i with ⟨g, p, a⟩ | ⟨r, a⟩
    · have hg := g.isLt
      have hp := p.isLt
      simp only [groupedEvalBlock]
      omega
    · have hr := r.isLt
      simp only [groupedEvalBlock]
      omega⟩

/-- The ordered edge profile produces a nonempty principal rank open in the
actual free base points. -/
theorem ordered_edge_interpolation_principal_open (hN : 5 ≤ N)
    (f : GroupedLeadingCol (N + 1) → EdgeOrder.Edge N → Fin 3 → K)
    (hsupport : ∀ j e, EdgeOrder.degree N (groupedLeadEdge hN j) < EdgeOrder.degree N e →
      f j e = 0)
    (n : Fin (N + 1) → Fin 3 → Fin 3 → K)
    (horth : ∀ g e j, n g e ⬝ᵥ groupedPlaneTop f (groupedLeadEdge hN) g e j = 0)
    (hn : ∀ g, (Matrix.of (n g)).det ≠ 0)
    (hP : ∀ g e, LinearIndependent K (groupedPlaneTop f (groupedLeadEdge hN) g e))
    (hR : ∀ r, LinearIndependent K (groupedRootTop f (groupedLeadEdge hN) r)) :
    ∃ P : MvPolynomial (Fin (2 * (N + 3) + 5) × Fin (N + 3 + 3)) K,
      (∃ a, MvPolynomial.eval a P ≠ 0) ∧
      ∀ a, MvPolynomial.eval a P ≠ 0 → Function.Injective
        (freeTraceMatrix (groupedFreePointIndex N) groupedEvalCoordinate
          (fun j => edgeQuadric edgeEndpoints (f j)) a).mulVec := by
  have hdeg (e : EdgeOrder.Edge N) :
      edgeDegree edgeEndpoints (doubledVertexWeight N) e = 2 * EdgeOrder.degree N e :=
    edgeEndpointWeight_eq e
  have hcolumn (j : GroupedLeadingCol (N + 1)) :
      edgeDegree edgeEndpoints (doubledVertexWeight N) (groupedLeadEdge hN j) =
        groupedColumnDegree (flattenedEdgeDegree hN) j := by
    rw [hdeg]
    cases j <;> rfl
  obtain ⟨rwgt, cwgt, hwt, hi⟩ :=
    exists_grouped_leading_weights (flattenedEdgeDegree hN) (flattenedEdgeDegree_strictMono hN)
  obtain ⟨x, _, hx⟩ := exists_grouped_edge_interpolation f (groupedLeadEdge hN)
    edgeEndpoints (doubledVertexWeight N) rwgt cwgt (edgeEndpointWeight_injective hN)
    (fun j e he => hsupport j e (by rw [hdeg, hdeg] at he; omega))
    (fun i j => (hcolumn j).symm ▸ hwt i j) (fun i j => (hcolumn j).symm ▸ hi i j)
    n horth hn hP hR
  let a₀ : Fin (2 * (N + 3) + 5) × Fin (N + 3 + 3) → K :=
    fun i => (x ^ (i.1.val + 1)) ^ doubledVertexWeight N i.2
  obtain ⟨P, hP₀, hPg⟩ := freeTraceMatrix_injective_principal_open (groupedLeadingRowColEquiv (N + 1))
    (groupedFreePointIndex N) groupedEvalCoordinate (fun j => edgeQuadric edgeEndpoints (f j)) a₀ hx
  exact ⟨P, ⟨a₀, hP₀⟩, hPg⟩

end IdealGeneration.TripleNormal
