module

public import IdealGeneration.CubicSupportedRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Edge labels and trace supports when adding a pair of variables in B.4. -/

namespace IdealGeneration.CubicSupported

/-- The increasing edge from an old vertex to one of the two new vertices. -/
def crossEdge {m : ℕ} (i : Fin m) (b : Fin 2) : Edge (m + 2) :=
  ⟨(Fin.castAdd 2 i, Fin.natAdd m b), by
    change i.val < m + b.val
    omega⟩

@[simp] theorem crossEdge_val {m : ℕ} (i : Fin m) (b : Fin 2) :
    (crossEdge i b).val = (Fin.castAdd 2 i, Fin.natAdd m b) := rfl

/-- The edge joining the two new vertices. -/
def newPairEdge (m : ℕ) : Edge (m + 2) :=
  ⟨(Fin.natAdd m 0, Fin.natAdd m 1), by
    change m + 0 < m + 1
    omega⟩

@[simp] theorem newPairEdge_val (m : ℕ) :
    (newPairEdge m).val = (Fin.natAdd m 0, Fin.natAdd m 1) := rfl

/-- Old, cross, and new-pair edge labels in the enlarged graph. -/
abbrev PairExtensionEdgeLabel (m : ℕ) := Edge m ⊕ ((Fin m × Fin 2) ⊕ Unit)

private def edgeOfExtensionLabel (m : ℕ) : PairExtensionEdgeLabel m → Edge (m + 2)
  | .inl e => oldEdge m e
  | .inr (.inl (i, b)) => crossEdge i b
  | .inr (.inr _) => newPairEdge m

private def extensionLabelOfEdge (m : ℕ) (e : Edge (m + 2)) : PairExtensionEdgeLabel m :=
  if h₂ : e.val.2.val < m then
    .inl ⟨(⟨e.val.1.val, lt_trans e.property h₂⟩, ⟨e.val.2.val, h₂⟩), e.property⟩
  else if h₁ : e.val.1.val < m then
    .inr (.inl (⟨e.val.1.val, h₁⟩, ⟨e.val.2.val - m, by omega⟩))
  else .inr (.inr ())

/-- Every enlarged edge is uniquely old, cross, or the edge between the two new vertices. -/
def edgeExtensionEquiv (m : ℕ) : Edge (m + 2) ≃ PairExtensionEdgeLabel m where
  toFun := extensionLabelOfEdge m
  invFun := edgeOfExtensionLabel m
  left_inv e := by
    unfold extensionLabelOfEdge
    split_ifs with h₂ h₁
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change m + (e.val.2.val - m) = e.val.2.val
        omega
    · have he : e.val.1.val < e.val.2.val := e.property
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        change m + 0 = e.val.1.val
        omega
      · apply Fin.ext
        change m + 1 = e.val.2.val
        omega
  right_inv := by
    rintro (e | (⟨i, b⟩ | ⟨⟩))
    · simp [edgeOfExtensionLabel, extensionLabelOfEdge, e.val.2.isLt]
    · have hb : ¬ m + b.val < m := by omega
      simp [edgeOfExtensionLabel, extensionLabelOfEdge, i.isLt, hb]
    · simp [edgeOfExtensionLabel, extensionLabelOfEdge]

@[simp] theorem edgeExtensionEquiv_symm_old {m : ℕ} (e : Edge m) :
    (edgeExtensionEquiv m).symm (.inl e) = oldEdge m e := rfl

@[simp] theorem edgeExtensionEquiv_symm_cross {m : ℕ} (i : Fin m) (b : Fin 2) :
    (edgeExtensionEquiv m).symm (.inr (.inl (i, b))) = crossEdge i b := rfl

@[simp] theorem edgeExtensionEquiv_symm_pair (m : ℕ) :
    (edgeExtensionEquiv m).symm (.inr (.inr ())) = newPairEdge m := rfl

@[simp] theorem edgeExtensionEquiv_old {m : ℕ} (e : Edge m) :
    edgeExtensionEquiv m (oldEdge m e) = .inl e := by
  simpa only [edgeExtensionEquiv_symm_old] using (edgeExtensionEquiv m).apply_symm_apply (.inl e)

@[simp] theorem edgeExtensionEquiv_cross {m : ℕ} (i : Fin m) (b : Fin 2) :
    edgeExtensionEquiv m (crossEdge i b) = .inr (.inl (i, b)) := by
  simpa only [edgeExtensionEquiv_symm_cross] using
    (edgeExtensionEquiv m).apply_symm_apply (.inr (.inl (i, b)))

@[simp] theorem edgeExtensionEquiv_pair (m : ℕ) :
    edgeExtensionEquiv m (newPairEdge m) = .inr (.inr ()) := by
  simpa only [edgeExtensionEquiv_symm_pair] using
    (edgeExtensionEquiv m).apply_symm_apply (.inr (.inr ()))

/-- A pair addition introduces `2*m` cross edges and one edge between the new vertices. -/
theorem card_edge_extension (m : ℕ) : Fintype.card (Edge (m + 2)) =
    Fintype.card (Edge m) + 2 * m + 1 := by
  rw [Fintype.card_congr (edgeExtensionEquiv m)]
  simp [PairExtensionEdgeLabel, Nat.mul_comm, Nat.add_assoc]

/-- Cross edges retain both their old vertex and new direction labels. -/
theorem crossEdge_injective (m : ℕ) :
    Function.Injective (fun p : Fin m × Fin 2 => crossEdge p.1 p.2) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  simpa using congrArg (edgeExtensionEquiv m) h

/-- An edge is old precisely when its larger endpoint is old. -/
theorem mem_range_oldEdge_iff {m : ℕ} (e : Edge (m + 2)) :
    e ∈ Set.range (oldEdge m) ↔ e.val.2.val < m := by
  constructor
  · rintro ⟨e, rfl⟩
    exact e.val.2.isLt
  · intro he
    refine ⟨⟨(⟨e.val.1.val, lt_trans e.property he⟩, ⟨e.val.2.val, he⟩), e.property⟩, rfl⟩

@[simp] theorem crossEdge_not_old {m : ℕ} (i : Fin m) (b : Fin 2) :
    crossEdge i b ∉ Set.range (oldEdge m) := by
  rw [mem_range_oldEdge_iff]
  change ¬ m + b.val < m
  omega

@[simp] theorem newPairEdge_not_old (m : ℕ) : newPairEdge m ∉ Set.range (oldEdge m) := by
  rw [mem_range_oldEdge_iff]
  change ¬ m + 1 < m
  omega

section Supports

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem old_ne_new (i : Fin m) (b : Fin 2) : Fin.castAdd 2 i ≠ Fin.natAdd m b := by
  intro h
  have he := congrArg Fin.val h
  change i.val = m + b.val at he
  omega

/-- A cross support restricts to its old endpoint. -/
@[simp] theorem edgeSupport_cross_old (i : Fin m) (b : Fin 2) (μ lam : R) (j : Fin m) :
    edgeSupport (crossEdge i b) μ lam (Fin.castAdd 2 j) = vertexSupport i μ j := by
  simp [edgeSupport, vertexSupport, old_ne_new]

/-- A cross support has one new coordinate with the edge scaling. -/
@[simp] theorem edgeSupport_cross_new (i : Fin m) (b : Fin 2) (μ lam : R) (c : Fin 2) :
    edgeSupport (crossEdge i b) μ lam (Fin.natAdd m c) = vertexSupport b (μ * lam) c := by
  simp [edgeSupport, vertexSupport, (old_ne_new i c).symm]

@[simp] theorem edgeSupport_newPair_old (μ lam : R) (j : Fin m) :
    edgeSupport (newPairEdge m) μ lam (Fin.castAdd 2 j) = 0 := by
  simp [edgeSupport, vertexSupport, old_ne_new]

@[simp] theorem edgeSupport_newPair_new (μ lam : R) (b : Fin 2) :
    edgeSupport (newPairEdge m) μ lam (Fin.natAdd m b) = ![μ, μ * lam] b := by
  fin_cases b <;> simp [edgeSupport, vertexSupport]

end Supports

section SingleEdges

variable {K : Type*} [Field K] {m : ℕ}

/-- A new incidence is an old-by-new edge that is single in the enlarged graph. -/
abbrev NewIncidence (Q : Parameters K (m + 2)) :=
  {p : Fin m × Fin 2 // Q.single (crossEdge p.1 p.2) = true}

/-- The single cross edge of a new incidence. -/
def crossSingleEdge (Q : Parameters K (m + 2)) : NewIncidence Q ↪ Q.SingleEdge where
  toFun p := ⟨crossEdge p.val.1 p.val.2, p.property⟩
  inj' _ _ h := Subtype.ext (crossEdge_injective m (congrArg Subtype.val h))

@[simp] theorem crossSingleEdge_val (Q : Parameters K (m + 2)) (p : NewIncidence Q) :
    (crossSingleEdge Q p).val = crossEdge p.val.1 p.val.2 := rfl

namespace Compatible

variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)

/-- A single cross edge lies outside the old single edges. -/
@[simp] theorem crossSingleEdge_not_old (p : NewIncidence Q) :
    crossSingleEdge Q p ∉ Set.range h.singleEdge := by
  rintro ⟨e, he⟩
  exact crossEdge_not_old p.val.1 p.val.2 ⟨e.val, congrArg Subtype.val he⟩

private def singleEdgeOfExtensionLabel : P.SingleEdge ⊕ NewIncidence Q → Q.SingleEdge :=
  Sum.elim h.singleEdge (crossSingleEdge Q)

private theorem singleEdgeOfExtensionLabel_bijective (hpair : Q.single (newPairEdge m) = false) :
    Function.Bijective h.singleEdgeOfExtensionLabel := by
  constructor
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (h.singleEdge.injective hab)
    · exact False.elim (h.crossSingleEdge_not_old b ⟨a, hab⟩)
    · exact False.elim (h.crossSingleEdge_not_old a ⟨b, hab.symm⟩)
    · exact congrArg Sum.inr ((crossSingleEdge Q).injective hab)
  · intro e
    obtain ⟨a, ha⟩ := (edgeExtensionEquiv m).symm.surjective e.val
    rcases a with a | (⟨i, b⟩ | ⟨⟩)
    · change oldEdge m a = e.val at ha
      have hs : P.single a = true := by rw [← h.single_eq a, ha]; exact e.property
      exact ⟨.inl ⟨a, hs⟩, Subtype.ext ha⟩
    · change crossEdge i b = e.val at ha
      have hs : Q.single (crossEdge i b) = true := by rw [ha]; exact e.property
      exact ⟨.inr ⟨(i, b), hs⟩, Subtype.ext ha⟩
    · change newPairEdge m = e.val at ha
      have he := e.property
      rw [← ha, hpair] at he
      contradiction

/-- If the edge between the two new vertices is double, every single edge is
an old single edge or a new incidence. -/
noncomputable def singleEdgeExtensionEquiv (hpair : Q.single (newPairEdge m) = false) :
    Q.SingleEdge ≃ P.SingleEdge ⊕ NewIncidence Q :=
  (Equiv.ofBijective h.singleEdgeOfExtensionLabel (h.singleEdgeOfExtensionLabel_bijective hpair)).symm

@[simp] theorem singleEdgeExtensionEquiv_symm_old (hpair : Q.single (newPairEdge m) = false)
    (e : P.SingleEdge) : (h.singleEdgeExtensionEquiv hpair).symm (.inl e) = h.singleEdge e := rfl

@[simp] theorem singleEdgeExtensionEquiv_symm_cross (hpair : Q.single (newPairEdge m) = false)
    (p : NewIncidence Q) : (h.singleEdgeExtensionEquiv hpair).symm (.inr p) = crossSingleEdge Q p := rfl

@[simp] theorem singleEdgeExtensionEquiv_old (hpair : Q.single (newPairEdge m) = false)
    (e : P.SingleEdge) : h.singleEdgeExtensionEquiv hpair (h.singleEdge e) = .inl e := by
  simpa only [singleEdgeExtensionEquiv_symm_old] using
    (h.singleEdgeExtensionEquiv hpair).apply_symm_apply (.inl e)

@[simp] theorem singleEdgeExtensionEquiv_cross (hpair : Q.single (newPairEdge m) = false)
    (p : NewIncidence Q) : h.singleEdgeExtensionEquiv hpair (crossSingleEdge Q p) = .inr p := by
  simpa only [singleEdgeExtensionEquiv_symm_cross] using
    (h.singleEdgeExtensionEquiv hpair).apply_symm_apply (.inr p)

/-- With a double new-pair edge, single cross edges are exactly the complement of the old ones. -/
theorem mem_range_crossSingleEdge_iff (hpair : Q.single (newPairEdge m) = false)
    (e : Q.SingleEdge) : e ∈ Set.range (crossSingleEdge Q) ↔ e ∉ Set.range h.singleEdge := by
  constructor
  · rintro ⟨p, rfl⟩
    exact h.crossSingleEdge_not_old p
  · intro he
    obtain ⟨a, ha⟩ := (h.singleEdgeExtensionEquiv hpair).symm.surjective e
    rcases a with a | p
    · exact False.elim (he ⟨a, ha⟩)
    · exact ⟨p, ha⟩

include h in
/-- The number of new incidences is the increase in the single-edge count. -/
theorem card_newIncidence (hpair : Q.single (newPairEdge m) = false) :
    Fintype.card (NewIncidence Q) = Fintype.card Q.SingleEdge - Fintype.card P.SingleEdge := by
  rw [Fintype.card_congr (h.singleEdgeExtensionEquiv hpair), Fintype.card_sum]
  omega

end Compatible
end SingleEdges
end IdealGeneration.CubicSupported
