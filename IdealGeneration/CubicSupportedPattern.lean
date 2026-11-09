module

public import IdealGeneration.CubicSupportedGraph
public import IdealGeneration.CubicPairLifts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The single-edge graph of Appendix B.5 and its C.3 restriction. -/

namespace IdealGeneration.CubicSupported.B5

/-- The first part of the single-edge graph. -/
def partA (i : ℕ) : Prop := i < 5 ∨ 11 ≤ i ∧ i % 2 = 1

/-- The second part of the single-edge graph. -/
def partB (i : ℕ) : Prop := (5 ≤ i ∧ i < 10) ∨ 10 ≤ i ∧ i % 2 = 0

theorem parts_cover (i : ℕ) : partA i ∨ partB i := by
  unfold partA partB
  omega

theorem parts_disjoint (i : ℕ) : ¬ (partA i ∧ partB i) := by
  unfold partA partB
  omega

/-- The increasing single edges have the two initial edges and the two kinds
of later endpoint prescribed by B.5. -/
def singleLabels (i j : ℕ) : Prop :=
  i < j ∧
    ((j < 10 ∧ ((i = 1 ∧ j = 7) ∨ (i = 2 ∧ j = 8))) ∨
     (10 ≤ j ∧ j % 2 = 0 ∧ ((1 ≤ i ∧ i ≤ 4) ∨ (11 ≤ i ∧ i % 2 = 1))) ∨
     (11 ≤ j ∧ j % 2 = 1 ∧ ((7 ≤ i ∧ i ≤ 9) ∨ (10 ≤ i ∧ i % 2 = 0 ∧ i + 1 < j))))

instance (i j : ℕ) : Decidable (singleLabels i j) := by
  unfold singleLabels
  infer_instance

/-- The B.5 pattern in the edge representation of the cone parameters. -/
def single {m : ℕ} (e : Edge m) : Bool := decide (singleLabels e.val.1.val e.val.2.val)

@[simp] theorem single_eq_true {m : ℕ} (e : Edge m) :
    single e = true ↔ singleLabels e.val.1.val e.val.2.val := by
  simp [single]

/-- Below coordinate ten there are exactly the two initial single edges. -/
theorem singleLabels_initial_iff {i j : ℕ} (hj : j < 10) :
    singleLabels i j ↔ (i = 1 ∧ j = 7) ∨ (i = 2 ∧ j = 8) := by
  unfold singleLabels
  omega

/-- The new even vertex attaches to the earlier first part, excluding the root. -/
theorem singleLabels_even_iff {i j : ℕ} (hj : 10 ≤ j) (heven : j % 2 = 0) :
    singleLabels i j ↔ i < j ∧ partA i ∧ i ≠ 0 := by
  unfold singleLabels partA
  omega

/-- The new odd vertex attaches to the earlier second part, omitting its roots
and the even vertex introduced in the same step. -/
theorem singleLabels_odd_iff {i j : ℕ} (hj : 11 ≤ j) (hodd : j % 2 = 1) :
    singleLabels i j ↔ i + 1 < j ∧ partB i ∧ i ≠ 5 ∧ i ≠ 6 := by
  unfold singleLabels partB
  omega

theorem same_pair_double (k : ℕ) : ¬ singleLabels (10 + 2 * k) (11 + 2 * k) := by
  unfold singleLabels
  omega

/-- An increasing single edge joins opposite parts of the graph. -/
theorem singleLabels_bipartite {i j : ℕ} (h : singleLabels i j) :
    (partA i ∧ partB j) ∨ (partB i ∧ partA j) := by
  unfold singleLabels partA partB at *
  omega

/-- No single edge has one of the three distinguished roots as an endpoint. -/
theorem singleLabels_excludes_roots {i j : ℕ} (h : singleLabels i j) :
    (i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 6) ∧ (j ≠ 0 ∧ j ≠ 5 ∧ j ≠ 6) := by
  unfold singleLabels at h
  omega

/-- Symmetric adjacency in the graph of single edges. -/
def adjacent {m : ℕ} (i j : Fin m) : Prop :=
  singleLabels i.val j.val ∨ singleLabels j.val i.val

theorem adjacent_bipartite {m : ℕ} {i j : Fin m} (h : adjacent i j) :
    (partA i.val ∧ partB j.val) ∨ (partB i.val ∧ partA j.val) := by
  rcases h with h | h
  · exact singleLabels_bipartite h
  · rcases singleLabels_bipartite h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

theorem adjacent_excludes_roots {m : ℕ} {i j : Fin m}
    (hi : i.val = 0 ∨ i.val = 5 ∨ i.val = 6) : ¬ adjacent i j := by
  rintro (h | h)
  · have hi' := (singleLabels_excludes_roots h).1
    tauto
  · have hi' := (singleLabels_excludes_roots h).2
    tauto

/-- The single-edge graph is triangle-free. -/
theorem triangle_free {m : ℕ} {i j k : Fin m}
    (hij : adjacent i j) (hjk : adjacent j k) : ¬ adjacent i k := by
  intro hik
  have hij' := adjacent_bipartite hij
  have hjk' := adjacent_bipartite hjk
  have hik' := adjacent_bipartite hik
  have hi := parts_disjoint i.val
  have hj := parts_disjoint j.val
  have hk := parts_disjoint k.val
  tauto

private theorem c3_labels_lt : ∀ i, CubicPair.coordinateLabel i < 14 := by decide +kernel

private theorem c3_labels_increasing :
    ∀ i j : Fin 7, i < j → CubicPair.coordinateLabel i < CubicPair.coordinateLabel j := by
  decide +kernel

/-- Embed the seven coordinates of the C.3 sample in any ambient pattern containing them. -/
def c3Vertex {m : ℕ} (hm : 14 ≤ m) (i : Fin 7) : Fin m :=
  ⟨CubicPair.coordinateLabel i, (c3_labels_lt i).trans_le hm⟩

theorem c3Vertex_strictMono {m : ℕ} (hm : 14 ≤ m) : StrictMono (c3Vertex hm) :=
  fun _ _ h => c3_labels_increasing _ _ h

/-- The increasing edge induced by the seven C.3 coordinate labels. -/
def c3Edge {m : ℕ} (hm : 14 ≤ m) (e : Edge 7) : Edge m :=
  ⟨(c3Vertex hm e.val.1, c3Vertex hm e.val.2), c3Vertex_strictMono hm e.property⟩

private theorem c3_single_check : ∀ i j : Fin 7, i < j →
    decide (singleLabels (CubicPair.coordinateLabel i) (CubicPair.coordinateLabel j)) =
      CubicPair.singleEdge i j := by
  decide +kernel

/-- The restriction to the C.3 labels has exactly the single edges `{11,12}` and `{10,13}`. -/
theorem single_c3Edge {m : ℕ} (hm : 14 ≤ m) (e : Edge 7) :
    single (c3Edge hm e) = CubicPair.singleEdge e.val.1 e.val.2 :=
  c3_single_check e.val.1 e.val.2 e.property

/-- The three roots followed by the coordinates of two selected pairs. -/
def pairLabels (r s : ℕ) : Fin 7 → ℕ :=
  ![0, 5, 6, 10 + 2 * r, 11 + 2 * r, 10 + 2 * s, 11 + 2 * s]

theorem pairLabels_strictMono {r s : ℕ} (hrs : r < s) : StrictMono (pairLabels r s) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [pairLabels] at * <;> omega

theorem pairLabels_lt {m r s : ℕ} (hrs : r < s) (hs : 11 + 2 * s < m) (i : Fin 7) :
    pairLabels r s i < m := by
  fin_cases i <;> norm_num [pairLabels] <;> omega

/-- Embed the three roots and any two successive-in-order pairs in the ambient coordinates. -/
def pairVertex {m r s : ℕ} (hrs : r < s) (hs : 11 + 2 * s < m) (i : Fin 7) : Fin m :=
  ⟨pairLabels r s i, pairLabels_lt hrs hs i⟩

theorem pairVertex_strictMono {m r s : ℕ} (hrs : r < s) (hs : 11 + 2 * s < m) :
    StrictMono (pairVertex hrs hs) :=
  fun _ _ h => pairLabels_strictMono hrs h

/-- Restrict the ambient graph to the three roots and the two chosen pairs. -/
def pairEdge {m r s : ℕ} (hrs : r < s) (hs : 11 + 2 * s < m) (e : Edge 7) : Edge m :=
  ⟨(pairVertex hrs hs e.val.1, pairVertex hrs hs e.val.2), pairVertex_strictMono hrs hs e.property⟩

theorem singleLabels_pair_iff {r s : ℕ} (hrs : r < s) {i j : Fin 7} (hij : i < j) :
    singleLabels (pairLabels r s i) (pairLabels r s j) ↔ CubicPair.singleEdge i j = true := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pairLabels, CubicPair.singleEdge, singleLabels] at * <;> omega

/-- Every two chosen pairs have the C.3 single-edge pattern on their seven coordinates. -/
theorem single_pairEdge {m r s : ℕ} (hrs : r < s) (hs : 11 + 2 * s < m) (e : Edge 7) :
    single (pairEdge hrs hs e) = CubicPair.singleEdge e.val.1 e.val.2 := by
  apply Bool.eq_iff_iff.mpr
  rw [single_eq_true]
  exact singleLabels_pair_iff hrs e.property

section Count

private abbrev CrossPair (k : ℕ) := {p : Fin k × Fin k // p.1 ≠ p.2}
private abbrev EdgeFamily (k : ℕ) :=
  Fin 2 ⊕ (Fin 4 × Fin k) ⊕ (Fin 3 × Fin k) ⊕ CrossPair k

/-- Enumerate initial, old-to-even, old-to-odd and cross-pair single edges. -/
private def familyLabels {k : ℕ} : EdgeFamily k → ℕ × ℕ
  | .inl d => (1 + d.val, 7 + d.val)
  | .inr (.inl (i, b)) => (1 + i.val, 10 + 2 * b.val)
  | .inr (.inr (.inl (i, a))) => (7 + i.val, 11 + 2 * a.val)
  | .inr (.inr (.inr e)) =>
    if e.val.1 < e.val.2 then (11 + 2 * e.val.1.val, 10 + 2 * e.val.2.val)
    else (10 + 2 * e.val.2.val, 11 + 2 * e.val.1.val)

private theorem familyLabels_valid {k : ℕ} (x : EdgeFamily k) :
    (familyLabels x).1 < 10 + 2 * k ∧ (familyLabels x).2 < 10 + 2 * k ∧
      singleLabels (familyLabels x).1 (familyLabels x).2 := by
  rcases x with d | (⟨i, b⟩ | (⟨i, a⟩ | e))
  · simp only [familyLabels, singleLabels]; omega
  · simp only [familyLabels, singleLabels]; omega
  · simp only [familyLabels, singleLabels]; omega
  · have he := e.property
    simp only [familyLabels]
    split <;> unfold singleLabels <;> omega

private theorem familyLabels_injective {k : ℕ} :
    Function.Injective (familyLabels (k := k)) := by
  intro x y h
  rcases x with x | (⟨i, b⟩ | (⟨i, a⟩ | x)) <;>
    rcases y with y | (⟨j, d⟩ | (⟨j, c⟩ | y)) <;>
    simp only [familyLabels] at h
  all_goals repeat' (split at h)
  all_goals simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at *
  all_goals first
    | omega
    | apply Subtype.ext
      apply Prod.ext <;> (apply Fin.ext; omega)

private theorem familyLabels_complete {k i j : ℕ} (hj : j < 10 + 2 * k)
    (h : singleLabels i j) : ∃ x : EdgeFamily k, familyLabels x = (i, j) := by
  have hi : i < 10 + 2 * k := h.1.trans hj
  by_cases hOld : j < 10
  · rcases (singleLabels_initial_iff hOld).mp h with h | h
    · exact ⟨.inl 0, by simp [familyLabels, h.1, h.2]⟩
    · exact ⟨.inl 1, by simp [familyLabels, h.1, h.2]⟩
  · by_cases he : j % 2 = 0
    · have hE := (singleLabels_even_iff (by omega) he).mp h
      let b : Fin k := ⟨(j - 10) / 2, by omega⟩
      have hA := hE.2.1
      change i < 5 ∨ 11 ≤ i ∧ i % 2 = 1 at hA
      rcases hA with hA | ⟨hA, hOdd⟩
      · let u : Fin 4 := ⟨i - 1, by have := hE.2.2; omega⟩
        refine ⟨.inr (.inl (u, b)), ?_⟩
        simp only [familyLabels, u, b, Prod.mk.injEq]
        omega
      · let a : Fin k := ⟨(i - 11) / 2, by omega⟩
        have hab : a < b := by
          change (i - 11) / 2 < (j - 10) / 2
          have := hE.1
          omega
        refine ⟨.inr (.inr (.inr ⟨(a, b), ne_of_lt hab⟩)), ?_⟩
        simp only [familyLabels, hab, ite_true, a, b, Prod.mk.injEq]
        omega
    · have hOdd : j % 2 = 1 := by omega
      have hO := (singleLabels_odd_iff (by omega) hOdd).mp h
      let a : Fin k := ⟨(j - 11) / 2, by omega⟩
      have hB := hO.2.1
      change (5 ≤ i ∧ i < 10) ∨ 10 ≤ i ∧ i % 2 = 0 at hB
      rcases hB with ⟨h5, h10⟩ | ⟨h10, hiEven⟩
      · let u : Fin 3 := ⟨i - 7, by have := hO.2.2; omega⟩
        refine ⟨.inr (.inr (.inl (u, a))), ?_⟩
        simp only [familyLabels, u, a, Prod.mk.injEq]
        have := hO.2.2
        omega
      · let b : Fin k := ⟨(i - 10) / 2, by omega⟩
        have hba : b < a := by
          change (i - 10) / 2 < (j - 11) / 2
          have := hO.1
          omega
        have hab : ¬ a < b := not_lt_of_ge hba.le
        refine ⟨.inr (.inr (.inr ⟨(a, b), ne_of_gt hba⟩)), ?_⟩
        simp only [familyLabels, hab, ite_false, a, b, Prod.mk.injEq]
        omega

private def familyEdge {k : ℕ} (x : EdgeFamily k) :
    {e : Edge (10 + 2 * k) // single e = true} :=
  let h := familyLabels_valid x
  ⟨⟨(⟨(familyLabels x).1, h.1⟩, ⟨(familyLabels x).2, h.2.1⟩), h.2.2.1⟩,
    (single_eq_true _).mpr h.2.2⟩

private theorem familyEdge_bijective {k : ℕ} : Function.Bijective (familyEdge (k := k)) := by
  constructor
  · intro x y h
    apply familyLabels_injective
    exact congrArg (fun e : {e : Edge (10 + 2 * k) // single e = true} =>
      (e.val.val.1.val, e.val.val.2.val)) h
  · intro e
    obtain ⟨x, hx⟩ := familyLabels_complete e.val.val.2.isLt ((single_eq_true _).mp e.property)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hx)
    · exact Fin.ext (congrArg Prod.snd hx)

private def diagonalEquiv (k : ℕ) : Fin k ≃ {p : Fin k × Fin k // p.1 = p.2} where
  toFun i := ⟨(i, i), rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property)

/-- After `k` pair additions the B.5 graph has `k² + 6k + 2` single edges. -/
theorem card_single (k : ℕ) :
    Fintype.card {e : Edge (10 + 2 * k) // single e = true} = k * k + 6 * k + 2 := by
  let e := Equiv.ofBijective (familyEdge (k := k)) familyEdge_bijective
  have hdiag : Fintype.card {p : Fin k × Fin k // p.1 = p.2} = k := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (diagonalEquiv k)).symm
  have hcross : Fintype.card (CrossPair k) = k * k - k := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_prod, Fintype.card_fin, hdiag]
  rw [← Fintype.card_congr e]
  simp only [EdgeFamily, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hcross]
  have hk : k ≤ k * k := Nat.le_mul_self k
  omega

end Count

end IdealGeneration.CubicSupported.B5
