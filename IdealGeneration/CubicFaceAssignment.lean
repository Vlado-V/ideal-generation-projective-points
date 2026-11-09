module

public import IdealGeneration.CubicLocalFaces

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Face ownership and the five-coordinate pair supports of Appendix B.5

The first ten coordinates form the pool. Every other vertex belongs to one
of the consecutive pairs. An edge belongs to the earlier pair that it meets.
-/

namespace IdealGeneration.CubicSupported.B5

/-- The pair index of a vertex, with `none` reserved for the initial pool. -/
def vertexOwner {m : ℕ} (i : Fin m) : Option ℕ :=
  if 10 ≤ i.val then some ((i.val - 10) / 2) else none

@[simp] theorem vertexOwner_eq_none {m : ℕ} (i : Fin m) :
    vertexOwner i = none ↔ i.val < 10 := by
  by_cases h : 10 ≤ i.val
  · simp [vertexOwner, h, not_lt.mpr h]
  · simp [vertexOwner, h, lt_of_not_ge h]

@[simp] theorem vertexOwner_eq_some {m : ℕ} (i : Fin m) (j : ℕ) :
    vertexOwner i = some j ↔ i.val = 10 + 2 * j ∨ i.val = 11 + 2 * j := by
  by_cases h : 10 ≤ i.val <;> simp [vertexOwner, h] <;> omega

/-- A face is assigned to its first nonpool vertex. -/
def faceOwner {m : ℕ} : Face m → Option ℕ
  | .inl i => vertexOwner i
  | .inr e => if 10 ≤ e.val.1.val then vertexOwner e.val.1 else vertexOwner e.val.2

/-- A pool face has every vertex in the initial ten coordinates. -/
theorem faceOwner_eq_none {m : ℕ} (F : Face m) :
    faceOwner F = none ↔ ∀ i ∈ faceVertices F, i.val < 10 := by
  rcases F with i | e
  · simp [faceOwner, faceVertices]
  · by_cases h : 10 ≤ e.val.1.val
    · simp [faceOwner, faceVertices, vertexOwner, h, not_lt.mpr h]
    · have h' : e.val.1.val < 10 := by omega
      simp [faceOwner, faceVertices, h, h']

/-- Every owned face contains a vertex of its owning pair. -/
theorem exists_vertex_of_faceOwner {m : ℕ} (F : Face m) (j : ℕ)
    (h : faceOwner F = some j) :
    ∃ i ∈ faceVertices F, vertexOwner i = some j := by
  rcases F with i | e
  · exact ⟨i, by simp [faceVertices], h⟩
  · by_cases he : 10 ≤ e.val.1.val
    · exact ⟨e.val.1, by simp [faceVertices], by simpa [faceOwner, he] using h⟩
    · exact ⟨e.val.2, by simp [faceVertices], by simpa [faceOwner, he] using h⟩

/-- No vertex of a later-owned face belongs to an earlier pair. -/
theorem faceOwner_le_vertexOwner {m : ℕ} (F : Face m) {i : Fin m} {j l : ℕ}
    (hF : faceOwner F = some j) (hi : i ∈ faceVertices F)
    (hiOwner : vertexOwner i = some l) : j ≤ l := by
  rcases F with u | e
  · have hi' : i = u := by simpa [faceVertices] using hi
    subst i
    change vertexOwner u = some j at hF
    exact Nat.le_of_eq (Option.some.inj (hF.symm.trans hiOwner))
  · have him : i = e.val.1 ∨ i = e.val.2 := by simpa [faceVertices] using hi
    have he := e.property
    by_cases hfirst : 10 ≤ e.val.1.val
    · have hOwner : vertexOwner e.val.1 = some j := by simpa [faceOwner, hfirst] using hF
      have h1 := (vertexOwner_eq_some _ _).mp hOwner
      rcases him with rfl | rfl
      · exact Nat.le_of_eq (Option.some.inj (hOwner.symm.trans hiOwner))
      · have h2 := (vertexOwner_eq_some _ _).mp hiOwner
        omega
    · have hOwner : vertexOwner e.val.2 = some j := by simpa [faceOwner, hfirst] using hF
      rcases him with rfl | rfl
      · have h1 := (vertexOwner_eq_some _ _).mp hiOwner
        omega
      · exact Nat.le_of_eq (Option.some.inj (hOwner.symm.trans hiOwner))

/-- The vertices of an exact monomial face are precisely its coordinate factors. -/
theorem faceVertices_monomialFace {m : ℕ} (i j : Fin m) :
    faceVertices (monomialFace i j) = {i, j} := by
  by_cases h : i < j
  · simp [monomialFace, faceVertices, h]
  · by_cases h' : j < i
    · ext u
      simp [monomialFace, faceVertices, h, h', or_comm]
    · have hij : i = j := by omega
      subst j
      simp [monomialFace, faceVertices]

/-- The older even and odd vertices of pair `j`. -/
def pairB {k : ℕ} (j : Fin k) : Fin (10 + 2 * k) := ⟨10 + 2 * j.val, by omega⟩

def pairA {k : ℕ} (j : Fin k) : Fin (10 + 2 * k) := ⟨11 + 2 * j.val, by omega⟩

/-- The five coordinates `S_j` on which the pair-core points are chosen. -/
def pairSupport {k : ℕ} (j : Fin k) : Finset (Fin (10 + 2 * k)) :=
  {pairA j, pairB j, ⟨0, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩}

@[simp] theorem mem_pairSupport_values {k : ℕ} (j : Fin k) (i : Fin (10 + 2 * k)) :
    i ∈ pairSupport j ↔ i.val = 11 + 2 * j.val ∨ i.val = 10 + 2 * j.val ∨
      i.val = 0 ∨ i.val = 5 ∨ i.val = 6 := by
  simp only [pairSupport, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, pairA, pairB]

/-- On the support of one pair, every nonpool vertex belongs to that pair. -/
theorem vertexOwner_of_mem_pairSupport {k : ℕ} (j : Fin k) {i : Fin (10 + 2 * k)}
    (hi : i ∈ pairSupport j) : vertexOwner i = none ∨ vertexOwner i = some j.val := by
  have hi' := (mem_pairSupport_values j i).mp hi
  rw [vertexOwner_eq_none, vertexOwner_eq_some]
  omega

/-- Earlier pairs do not meet the support of a later pair's core samples. -/
theorem not_mem_pairSupport_of_earlier {k : ℕ} (j : Fin k) {i : Fin (10 + 2 * k)}
    {l : ℕ} (hi : vertexOwner i = some l) (h : l < j.val) : i ∉ pairSupport j := by
  intro hs
  rcases vertexOwner_of_mem_pairSupport j hs with hnone | hj
  · simp [hi] at hnone
  · have he := Option.some.inj (hi.symm.trans hj)
    omega

/-- The one vertex in `S_j` attached to the new vertex of direction `b`. -/
def activePairVertex {k : ℕ} (j : Fin k) (b : Fin 2) : Fin (10 + 2 * k) :=
  if b = 0 then pairA j else pairB j

/-- The roots and the other vertex of the pair do not contribute a new-edge
column on the five-coordinate support. -/
theorem neighbor_iff_on_pairSupport {k : ℕ} (j : Fin k) (b : Fin 2)
    {i : Fin (10 + 2 * k)} (hi : i ∈ pairSupport j) :
    neighbor b i ↔ i = activePairVertex j b := by
  have hs := (mem_pairSupport_values j i).mp hi
  have hj := j.isLt
  fin_cases b <;> simp [neighbor, singleLabels, activePairVertex, pairA, pairB, Fin.ext_iff] <;>
    omega

/-- No old single edge is supported on the five pair coordinates. -/
theorem not_single_of_edge_on_pairSupport {k : ℕ} (j : Fin k)
    (e : Edge (10 + 2 * k)) (hi : e.val.1 ∈ pairSupport j) (hj : e.val.2 ∈ pairSupport j) :
    ¬ single e = true := by
  intro hs
  have h := (single_eq_true e).mp hs
  have hroots := singleLabels_excludes_roots h
  have hi' := (mem_pairSupport_values j e.val.1).mp hi
  have hj' := (mem_pairSupport_values j e.val.2).mp hj
  have he := e.property
  have h1 : e.val.1.val = 10 + 2 * j.val := by omega
  have h2 : e.val.2.val = 11 + 2 * j.val := by omega
  exact same_pair_double j.val (by simpa only [h1, h2] using h)

/-- A face contained in `S_j` has at most one local column in each direction. -/
theorem card_faceLocalColumns_le_one_on_pairSupport {k : ℕ} (j : Fin k) (b : Fin 2)
    (F : Face (10 + 2 * k)) (hF : faceVertices F ⊆ pairSupport j) :
    (faceLocalColumns b F).card ≤ 1 := by
  have hfilter : (faceVertices F).filter (neighbor b) ⊆ {activePairVertex j b} := by
    intro i hi
    obtain ⟨hiF, hin⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_singleton.mpr ((neighbor_iff_on_pairSupport j b (hF hiF)).mp hin)
  have hcount := Finset.card_le_card hfilter
  rw [Finset.card_singleton] at hcount
  have hold : oldFaceCount F = 0 := by
    rcases F with i | e
    · rfl
    · have hi : e.val.1 ∈ pairSupport j := hF (by simp [faceVertices])
      have hj : e.val.2 ∈ pairSupport j := hF (by simp [faceVertices])
      simp [oldFaceCount, not_single_of_edge_on_pairSupport j e hi hj]
  rw [card_faceLocalColumns, hold, zero_add]
  exact hcount

section Evaluation

variable {K : Type*} [Field K] {m : ℕ} {b : Fin 2}

/-- Outside its face a probe has zero coordinate even when its edge parameter is zero. -/
theorem faceProbe_eq_zero_of_not_mem (F : Face m) (lam : K) {i : Fin m}
    (hi : i ∉ faceVertices F) : faceProbe F lam i = 0 := by
  rcases F with u | e
  · have h : i ≠ u := by simpa [faceVertices] using hi
    simp [faceProbe, vertexSupport, h]
  · have h : i ≠ e.val.1 ∧ i ≠ e.val.2 := by simpa [faceVertices] using hi
    simp [faceProbe, edgeSupport, vertexSupport, h.1, h.2]

/-- A local column of pair `j` contains a coordinate of that pair as a factor. -/
theorem localValue_zero_of_owner (P : Parameters K (m + 2)) (c : LocalColumn m b)
    {j : ℕ} (hc : faceOwner (localFace c) = some j)
    (y : Fin m → K) (hy : ∀ i, vertexOwner i = some j → y i = 0)
    (w : Fin 2 → K) (r : Fin 2) : localValue P c y w r = 0 := by
  obtain ⟨i, hi, hio⟩ := exists_vertex_of_faceOwner (localFace c) j hc
  have hi' : i = (localEndpoints c).1 ∨ i = (localEndpoints c).2 := by
    simpa [localFace, faceVertices_monomialFace] using hi
  rcases hi' with rfl | rfl <;> simp [localValue, hy _ hio]

/-- Every full-face local column vanishes on the pair-core support. -/
theorem localValue_full_face_zero_on_pairSupport {k : ℕ}
    (P : Parameters K ((10 + 2 * k) + 2)) (c : LocalColumn (10 + 2 * k) b)
    (hfull : (faceLocalColumns b (localFace c)).card = 2) (j : Fin k)
    (y : Fin (10 + 2 * k) → K) (hy : ∀ i ∉ pairSupport j, y i = 0)
    (w : Fin 2 → K) (r : Fin 2) : localValue P c y w r = 0 := by
  by_cases h1 : (localEndpoints c).1 ∈ pairSupport j
  · by_cases h2 : (localEndpoints c).2 ∈ pairSupport j
    · have hs : faceVertices (localFace c) ⊆ pairSupport j := by
        intro i hi
        have hi' : i = (localEndpoints c).1 ∨ i = (localEndpoints c).2 := by
          simpa [localFace, faceVertices_monomialFace] using hi
        rcases hi' with rfl | rfl <;> assumption
      have hle := card_faceLocalColumns_le_one_on_pairSupport j b (localFace c) hs
      omega
    · simp [localValue, hy _ h2]
  · simp [localValue, hy _ h1]

end Evaluation
end IdealGeneration.CubicSupported.B5
