module

public import IdealGeneration.CubicFaceAssignment

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The five half faces in each direction at a pair in Appendix B.5. -/

namespace IdealGeneration.CubicSupported.B5

variable {k : ℕ}

/-- The old neighborhood of the next even vertex. -/
theorem neighbor_zero_iff (i : Fin (10 + 2 * k)) : neighbor 0 i ↔
    (1 ≤ i.val ∧ i.val ≤ 4) ∨ (11 ≤ i.val ∧ i.val % 2 = 1) := by
  have hi := i.isLt
  simp only [neighbor, singleLabels, Fin.val_zero, Nat.add_zero]
  omega

/-- The old neighborhood of the next odd vertex. -/
theorem neighbor_one_iff (i : Fin (10 + 2 * k)) : neighbor 1 i ↔
    (7 ≤ i.val ∧ i.val ≤ 9) ∨ (10 ≤ i.val ∧ i.val % 2 = 0) := by
  have hi := i.isLt
  simp only [neighbor, singleLabels, Fin.val_one]
  omega

/-- The three possible contributions to the exact column count on an edge. -/
theorem card_faceLocalColumns_edge_eq {m : ℕ} (b : Fin 2) (e : Edge m) :
    (faceLocalColumns b (Sum.inr e)).card =
      (if singleLabels e.val.1.val e.val.2.val then 1 else 0) +
      (if neighbor b e.val.1 then 1 else 0) + (if neighbor b e.val.2 then 1 else 0) := by
  rw [card_faceLocalColumns]
  simp only [oldFaceCount, single_eq_true, faceVertices, Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : neighbor b e.val.1 <;> by_cases h2 : neighbor b e.val.2 <;>
    simp [h1, h2, ne_of_lt e.property]

set_option maxHeartbeats 1400000 in
/-- A half edge assigned to a pair lies on its five-coordinate support. -/
theorem half_edge_on_pairSupport_of_owned (j : Fin k) (b : Fin 2)
    (e : Edge (10 + 2 * k)) (ho : faceOwner (Sum.inr e) = some j.val)
    (hh : (faceLocalColumns b (Sum.inr e)).card = 1) :
    faceVertices (Sum.inr e) ⊆ pairSupport j := by
  have hi := e.val.1.isLt
  have hj := e.val.2.isLt
  have hlt := e.property
  have hjk := j.isLt
  have hown : (e.val.1.val = 10 + 2 * j.val ∨ e.val.1.val = 11 + 2 * j.val) ∨
      (e.val.1.val < 10 ∧ (e.val.2.val = 10 + 2 * j.val ∨ e.val.2.val = 11 + 2 * j.val)) := by
    by_cases h : 10 ≤ e.val.1.val
    · exact Or.inl ((vertexOwner_eq_some _ _).mp (by simpa only [faceOwner, h, ite_true] using ho))
    · exact Or.inr ⟨lt_of_not_ge h, (vertexOwner_eq_some _ _).mp
        (by simpa only [faceOwner, h, ite_false] using ho)⟩
  have hcount := card_faceLocalColumns_edge_eq b e
  rw [hh] at hcount
  have hs :
      (e.val.1.val = 11 + 2 * j.val ∨ e.val.1.val = 10 + 2 * j.val ∨
        e.val.1.val = 0 ∨ e.val.1.val = 5 ∨ e.val.1.val = 6) ∧
      (e.val.2.val = 11 + 2 * j.val ∨ e.val.2.val = 10 + 2 * j.val ∨
        e.val.2.val = 0 ∨ e.val.2.val = 5 ∨ e.val.2.val = 6) := by
    have hval : b.val = 0 ∨ b.val = 1 := by have := b.isLt; omega
    rcases hval with hb | hb
    · have hb' : b = 0 := Fin.ext hb
      subst b
      simp only [neighbor_zero_iff, singleLabels] at hcount
      repeat' split at hcount
      all_goals omega
    · have hb' : b = 1 := Fin.ext hb
      subst b
      simp only [neighbor_one_iff, singleLabels] at hcount
      repeat' split at hcount
      all_goals omega
  intro i him
  have him' : i = e.val.1 ∨ i = e.val.2 := by simpa [faceVertices] using him
  rcases him' with rfl | rfl
  · exact (mem_pairSupport_values _ _).mpr hs.1
  · exact (mem_pairSupport_values _ _).mpr hs.2

/-- On `S_j`, the single local column exists exactly when the active vertex occurs. -/
theorem card_faceLocalColumns_on_pairSupport (j : Fin k) (b : Fin 2)
    (F : Face (10 + 2 * k)) (hF : faceVertices F ⊆ pairSupport j) :
    (faceLocalColumns b F).card = if activePairVertex j b ∈ faceVertices F then 1 else 0 := by
  have hold : oldFaceCount F = 0 := by
    rcases F with i | e
    · rfl
    · have hi : e.val.1 ∈ pairSupport j := hF (by simp [faceVertices])
      have hj : e.val.2 ∈ pairSupport j := hF (by simp [faceVertices])
      simp [oldFaceCount, not_single_of_edge_on_pairSupport j e hi hj]
  have hfilter : (faceVertices F).filter (neighbor b) =
      (faceVertices F).filter (fun i => i = activePairVertex j b) :=
    Finset.filter_congr (fun _ hi => neighbor_iff_on_pairSupport j b (hF hi))
  rw [card_faceLocalColumns, hold, zero_add, hfilter, Finset.filter_eq']
  by_cases h : activePairVertex j b ∈ faceVertices F <;> simp [h]

/-- The half faces of one assigned pair are precisely its faces in `S_j`
containing the active vertex of the chosen direction. -/
theorem half_face_of_owned_iff (j : Fin k) (b : Fin 2) (F : Face (10 + 2 * k))
    (ho : faceOwner F = some j.val) :
    (faceLocalColumns b F).card = 1 ↔
      faceVertices F ⊆ pairSupport j ∧ activePairVertex j b ∈ faceVertices F := by
  constructor
  · intro hh
    have hS : faceVertices F ⊆ pairSupport j := by
      rcases F with i | e
      · have hi := (vertexOwner_eq_some i j.val).mp ho
        rw [faceVertices, Finset.singleton_subset_iff]
        exact (mem_pairSupport_values j i).mpr (by omega)
      · exact half_edge_on_pairSupport_of_owned j b e ho hh
    rw [card_faceLocalColumns_on_pairSupport j b F hS] at hh
    refine ⟨hS, ?_⟩
    by_contra h
    simp [h] at hh
  · rintro ⟨hS, ha⟩
    simp [card_faceLocalColumns_on_pairSupport j b F hS, ha]


/-- The active vertex is owned by the indicated pair. -/
theorem vertexOwner_activePairVertex (j : Fin k) (b : Fin 2) :
    vertexOwner (activePairVertex j b) = some j.val := by
  by_cases hb : b = 0
  · rw [activePairVertex, ite_eq_left hb, vertexOwner_eq_some]
    exact Or.inr rfl
  · rw [activePairVertex, ite_eq_right hb, vertexOwner_eq_some]
    exact Or.inl rfl

/-- The active vertex belongs to the five-coordinate support. -/
theorem activePairVertex_mem_pairSupport (j : Fin k) (b : Fin 2) :
    activePairVertex j b ∈ pairSupport j := by
  have hv := (vertexOwner_eq_some _ _).mp (vertexOwner_activePairVertex j b)
  exact (mem_pairSupport_values _ _).mpr (by tauto)

/-- A face on the five-coordinate support containing the active vertex is
owned by this pair. -/
theorem faceOwner_of_pairSupport_and_active (j : Fin k) (b : Fin 2)
    (F : Face (10 + 2 * k)) (hS : faceVertices F ⊆ pairSupport j)
    (hA : activePairVertex j b ∈ faceVertices F) : faceOwner F = some j.val := by
  have hOwn := vertexOwner_activePairVertex j b
  rcases F with i | e
  · have hi : activePairVertex j b = i := by simpa [faceVertices] using hA
    change vertexOwner i = some j.val
    rw [← hi]
    exact hOwn
  · by_cases he : 10 ≤ e.val.1.val
    · have hi : e.val.1 ∈ pairSupport j := hS (by simp [faceVertices])
      rcases vertexOwner_of_mem_pairSupport j hi with hnone | hj
      · have hlt := (vertexOwner_eq_none _).mp hnone
        omega
      · simpa only [faceOwner, he, ite_true] using hj
    · have ha : activePairVertex j b = e.val.1 ∨ activePairVertex j b = e.val.2 := by
        simpa [faceVertices] using hA
      have hval := (vertexOwner_eq_some _ _).mp hOwn
      have hne : activePairVertex j b ≠ e.val.1 := by
        intro h
        rw [h] at hval
        omega
      have ha' := ha.resolve_left hne
      rw [faceOwner, ite_eq_right he, ← ha']
      exact hOwn

/-- The five exact half faces, enumerated by the second monomial factor in `S_j`. -/
def pairHalfFaces (j : Fin k) (b : Fin 2) : Finset (Face (10 + 2 * k)) :=
  (pairSupport j).image (monomialFace (activePairVertex j b))

/-- This list exhausts the half faces assigned to the pair. -/
theorem mem_pairHalfFaces_iff (j : Fin k) (b : Fin 2) (F : Face (10 + 2 * k)) :
    F ∈ pairHalfFaces j b ↔ faceOwner F = some j.val ∧ (faceLocalColumns b F).card = 1 := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    have hA := activePairVertex_mem_pairSupport j b
    have hS : faceVertices (monomialFace (activePairVertex j b) i) ⊆ pairSupport j := by
      rw [faceVertices_monomialFace]
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    have hmem : activePairVertex j b ∈ faceVertices (monomialFace (activePairVertex j b) i) := by
      simp [faceVertices_monomialFace]
    exact ⟨faceOwner_of_pairSupport_and_active j b _ hS hmem,
      (card_faceLocalColumns_on_pairSupport j b _ hS).trans (ite_eq_left hmem)⟩
  · rintro ⟨ho, hh⟩
    obtain ⟨hS, ha⟩ := (half_face_of_owned_iff j b F ho).mp hh
    apply Finset.mem_image.mpr
    rcases F with i | e
    · have hi : activePairVertex j b = i := by simpa [faceVertices] using ha
      exact ⟨i, hS (by simp [faceVertices]), monomialFace_eq_vertex.mpr ⟨hi, rfl⟩⟩
    · have hm : activePairVertex j b = e.val.1 ∨ activePairVertex j b = e.val.2 := by
        simpa [faceVertices] using ha
      rcases hm with h | h
      · exact ⟨e.val.2, hS (by simp [faceVertices]), (monomialFace_eq_edge e).mpr (Or.inl ⟨h, rfl⟩)⟩
      · exact ⟨e.val.1, hS (by simp [faceVertices]), (monomialFace_eq_edge e).mpr (Or.inr ⟨h, rfl⟩)⟩

/-- The support consists of two pair vertices and three distinct roots. -/
theorem card_pairSupport (j : Fin k) : (pairSupport j).card = 5 := by
  unfold pairSupport
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, pairA, pairB]
  all_goals omega

/-- There are exactly five half faces in each normal direction at every pair. -/
theorem card_pairHalfFaces (j : Fin k) (b : Fin 2) : (pairHalfFaces j b).card = 5 := by
  rw [pairHalfFaces, Finset.card_image_of_injective _ (monomialFace_right_injective _), card_pairSupport]

end IdealGeneration.CubicSupported.B5
