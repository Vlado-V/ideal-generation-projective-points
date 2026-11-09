module

public import IdealGeneration.CubicB11Assembly
public import IdealGeneration.CubicHalfFaces

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The twenty-six pair-core columns in the order of Appendix C.3. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

variable {k : ℕ}

/-- The other vertex of the pair, following the active vertex in the C.3 order. -/
def otherPairVertex (j : Fin k) (b : Fin 2) : Fin (10 + 2 * k) :=
  if b = 0 then pairB j else pairA j

/-- The factors of the half-face columns, in their prescribed order. -/
def pairHalfFactors (j : Fin k) (b : Fin 2) : Fin 5 → Fin (10 + 2 * k) :=
  ![activePairVertex j b, otherPairVertex j b, ⟨0, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩]

theorem pairA_mem_pairSupport (j : Fin k) : pairA j ∈ pairSupport j :=
  (mem_pairSupport_values j _).mpr (Or.inl rfl)

theorem pairB_mem_pairSupport (j : Fin k) : pairB j ∈ pairSupport j :=
  (mem_pairSupport_values j _).mpr (Or.inr (Or.inl rfl))

theorem pairHalfFactors_mem (j : Fin k) (b : Fin 2) (i : Fin 5) :
    pairHalfFactors j b i ∈ pairSupport j := by
  fin_cases i
  · exact activePairVertex_mem_pairSupport j b
  · change otherPairVertex j b ∈ pairSupport j
    by_cases hb : b = 0
    · simpa only [otherPairVertex, hb, ite_true] using pairB_mem_pairSupport j
    · simpa only [otherPairVertex, hb, ite_false] using pairA_mem_pairSupport j
  · exact (mem_pairSupport_values j _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  · exact (mem_pairSupport_values j _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact (mem_pairSupport_values j _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- Every coordinate in the pair support occurs in the prescribed order. -/
theorem exists_pairHalfFactors_eq (j : Fin k) (b : Fin 2)
    {i : Fin (10 + 2 * k)} (hi : i ∈ pairSupport j) : ∃ c, pairHalfFactors j b c = i := by
  have hv := (mem_pairSupport_values j i).mp hi
  rcases hv with ha | hb | h0 | h5 | h6
  · by_cases hd : b = 0
    · exact ⟨0, Fin.ext (by simpa [pairHalfFactors, activePairVertex, hd, pairA] using ha.symm)⟩
    · exact ⟨1, Fin.ext (by simpa [pairHalfFactors, otherPairVertex, hd, pairA] using ha.symm)⟩
  · by_cases hd : b = 0
    · exact ⟨1, Fin.ext (by simpa [pairHalfFactors, otherPairVertex, hd, pairB] using hb.symm)⟩
    · exact ⟨0, Fin.ext (by simpa [pairHalfFactors, activePairVertex, hd, pairB] using hb.symm)⟩
  · exact ⟨2, Fin.ext h0.symm⟩
  · exact ⟨3, Fin.ext h5.symm⟩
  · exact ⟨4, Fin.ext h6.symm⟩

/-- The active single-edge endpoint in each direction. -/
def activeNeighbor (j : Fin k) (b : Fin 2) : {i : Fin (10 + 2 * k) // neighbor b i} :=
  ⟨activePairVertex j b, (neighbor_iff_on_pairSupport j b (activePairVertex_mem_pairSupport j b)).mpr rfl⟩

/-- The half-face local columns are the actual new-edge columns at the active endpoint. -/
def pairHalfLocalColumn (j : Fin k) (b : Fin 2) (i : Fin 5) : LocalColumn (10 + 2 * k) b :=
  .inr (activeNeighbor j b, pairHalfFactors j b i)

theorem pairHalfLocalColumn_face (j : Fin k) (b : Fin 2) (i : Fin 5) :
    faceOwner (localFace (pairHalfLocalColumn j b i)) = some j.val ∧
      (faceLocalColumns b (localFace (pairHalfLocalColumn j b i))).card = 1 := by
  apply (mem_pairHalfFaces_iff j b _).mp
  exact Finset.mem_image.mpr ⟨_, pairHalfFactors_mem j b i, rfl⟩

/-- The disjoint ordered column families in the two directions. -/
abbrev PairCoreLabel :=
  (Fin 3 ⊕ (Fin 2 ⊕ (Fin 3 ⊕ Fin 5))) ⊕ (Fin 3 ⊕ (Fin 3 ⊕ (Fin 2 ⊕ Fin 5)))

/-- In C.3 the first direction lists motion at `a`, extra at `a`, motion at `b`,
then half faces at `a`. The second direction lists both motion families first. -/
def pairCoreLabelEquiv : Fin 26 ≃ PairCoreLabel :=
  (finSumFinEquiv (m := 13) (n := 13)).symm.trans
    (Equiv.sumCongr
      ((finSumFinEquiv (m := 3) (n := 10)).symm.trans
        (Equiv.sumCongr (Equiv.refl _) ((finSumFinEquiv (m := 2) (n := 8)).symm.trans
          (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 5)).symm))))
      ((finSumFinEquiv (m := 3) (n := 10)).symm.trans
        (Equiv.sumCongr (Equiv.refl _) ((finSumFinEquiv (m := 3) (n := 7)).symm.trans
          (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 2) (n := 5)).symm)))))

/-- The actual pair-core column attached to an ordered label. -/
def pairCoreLabelColumn (j : Fin k) : PairCoreLabel → B7Column (10 + 2 * k)
  | .inl (.inl q) => .motion 0 (pairA j) q
  | .inl (.inr (.inl u)) => .extra 0 (activeNeighbor j 0) u
  | .inl (.inr (.inr (.inl q))) => .motion 0 (pairB j) q
  | .inl (.inr (.inr (.inr i))) => .localColumn 0 (pairHalfLocalColumn j 0 i)
  | .inr (.inl q) => .motion 1 (pairA j) q
  | .inr (.inr (.inl q)) => .motion 1 (pairB j) q
  | .inr (.inr (.inr (.inl u))) => .extra 1 (activeNeighbor j 1) u
  | .inr (.inr (.inr (.inr i))) => .localColumn 1 (pairHalfLocalColumn j 1 i)

/-- The twenty-six columns of `E_j` in the literal C.3 order. -/
def canonicalPairCoreColumn (j : Fin k) (i : Fin 26) : B7Column (10 + 2 * k) :=
  pairCoreLabelColumn j (pairCoreLabelEquiv i)

/-- The pair core consists of the half faces and the owned star columns. -/
def IsPairCoreColumn (j : Fin k) : B7Column (10 + 2 * k) → Prop
  | .localColumn b c => faceOwner (localFace c) = some j.val ∧ (faceLocalColumns b (localFace c)).card = 1
  | .motion _ i _ => vertexOwner i = some j.val
  | .extra _ i _ => vertexOwner i.val = some j.val
  | .remaining _ _ _ => False

theorem pairCoreLabelColumn_isPairCoreColumn (j : Fin k) (i : PairCoreLabel) :
    IsPairCoreColumn j (pairCoreLabelColumn j i) := by
  rcases i with (q | u | q | i) | (q | q | u | i)
  · exact (vertexOwner_eq_some _ _).mpr (Or.inr rfl)
  · exact vertexOwner_activePairVertex j 0
  · exact (vertexOwner_eq_some _ _).mpr (Or.inl rfl)
  · exact pairHalfLocalColumn_face j 0 i
  · exact (vertexOwner_eq_some _ _).mpr (Or.inr rfl)
  · exact (vertexOwner_eq_some _ _).mpr (Or.inl rfl)
  · exact vertexOwner_activePairVertex j 1
  · exact pairHalfLocalColumn_face j 1 i

/-- The canonical columns are owned by the pair, as required by the assembly. -/
theorem canonicalPairCoreColumn_owner (j : Fin k) (i : Fin 26) :
    b7Owner (canonicalPairCoreColumn j i) = some j.val := by
  have h := pairCoreLabelColumn_isPairCoreColumn j (pairCoreLabelEquiv i)
  unfold canonicalPairCoreColumn
  generalize pairCoreLabelColumn j (pairCoreLabelEquiv i) = c at h ⊢
  cases c with
  | localColumn _ _ => exact h.1
  | motion _ _ _ => exact h
  | extra _ _ _ => exact h
  | remaining _ _ _ => exact h.elim

/-- Each owned half face contributes its unique local column to the core. -/
theorem exists_pairHalfLocalColumn_eq (j : Fin k) (b : Fin 2) (c : LocalColumn (10 + 2 * k) b)
    (ho : faceOwner (localFace c) = some j.val)
    (hh : (faceLocalColumns b (localFace c)).card = 1) : ∃ i, pairHalfLocalColumn j b i = c := by
  have hF := (mem_pairHalfFaces_iff j b (localFace c)).mpr ⟨ho, hh⟩
  obtain ⟨i, hi, hface⟩ := Finset.mem_image.mp hF
  obtain ⟨l, hl⟩ := exists_pairHalfFactors_eq j b hi
  have hlocal : localFace (pairHalfLocalColumn j b l) = localFace c := by
    change monomialFace (activePairVertex j b) (pairHalfFactors j b l) = localFace c
    rw [hl, hface]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hh
  have hc : c = u := by
    have hmem := (mem_faceLocalColumns (localFace c) c).mpr rfl
    simpa only [hu, Finset.mem_singleton] using hmem
  have hl' : pairHalfLocalColumn j b l = u := by
    have hmem := (mem_faceLocalColumns (localFace c) _).mpr hlocal
    simpa only [hu, Finset.mem_singleton] using hmem
  exact ⟨l, hl'.trans hc.symm⟩

private theorem direction_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  have hb := b.isLt
  have hb' : b.val = 0 ∨ b.val = 1 := by omega
  exact hb'.imp Fin.ext Fin.ext

/-- Every half-face or star column belonging to the pair is present in its core. -/
theorem exists_pairCoreLabelColumn_eq (j : Fin k) (c : B7Column (10 + 2 * k))
    (hc : IsPairCoreColumn j c) : ∃ i, pairCoreLabelColumn j i = c := by
  cases c with
  | localColumn b c =>
    obtain ⟨i, rfl⟩ := exists_pairHalfLocalColumn_eq j b c hc.1 hc.2
    rcases direction_cases b with rfl | rfl
    · exact ⟨.inl (.inr (.inr (.inr i))), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inr i))), rfl⟩
  | motion b i q =>
    rcases (vertexOwner_eq_some i j.val).mp hc with hB | hA
    · have hi : i = pairB j := Fin.ext hB
      subst i
      rcases direction_cases b with rfl | rfl
      · exact ⟨.inl (.inr (.inr (.inl q))), rfl⟩
      · exact ⟨.inr (.inr (.inl q)), rfl⟩
    · have hi : i = pairA j := Fin.ext hA
      subst i
      rcases direction_cases b with rfl | rfl
      · exact ⟨.inl (.inl q), rfl⟩
      · exact ⟨.inr (.inl q), rfl⟩
  | extra b i u =>
    have hv := (vertexOwner_eq_some i.val j.val).mp hc
    have hs := (mem_pairSupport_values j i.val).mpr (by tauto)
    have hi : i = activeNeighbor j b := Subtype.ext ((neighbor_iff_on_pairSupport j b hs).mp i.property)
    subst i
    rcases direction_cases b with rfl | rfl
    · exact ⟨.inl (.inr (.inl u)), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inl u))), rfl⟩
  | remaining b u q => exact hc.elim

/-- The ordered list exhausts the assigned half-face and star columns. -/
theorem mem_range_canonicalPairCoreColumn (j : Fin k) (c : B7Column (10 + 2 * k)) :
    c ∈ Set.range (canonicalPairCoreColumn j) ↔ IsPairCoreColumn j c := by
  constructor
  · rintro ⟨i, rfl⟩
    exact pairCoreLabelColumn_isPairCoreColumn j _
  · intro hc
    obtain ⟨i, rfl⟩ := exists_pairCoreLabelColumn_eq j c hc
    exact ⟨pairCoreLabelEquiv.symm i, by simp [canonicalPairCoreColumn]⟩

/-- A pair block with the canonical core list includes every column it owns. -/
theorem mem_range_pairColumn_iff {K : Type*} [Field K] {j : Fin k}
    (D : PairBlockData K k j) (hD : D.coreColumn = canonicalPairCoreColumn j)
    (c : B7Column (10 + 2 * k)) : c ∈ Set.range (pairColumn D) ↔ b7Owner c = some j.val := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    exact pairColumn_owner D i
  · intro ho
    by_cases hc : IsPairCoreColumn j c
    · obtain ⟨i, hi⟩ := (mem_range_canonicalPairCoreColumn j c).mpr hc
      refine ⟨.inl i, ?_⟩
      change D.coreColumn i = c
      rw [hD, hi]
    · cases c with
      | localColumn b c =>
        change faceOwner (localFace c) = some j.val at ho
        have hmem := (mem_faceLocalColumns (localFace c) c).mpr rfl
        have hpos := Finset.card_pos.mpr ⟨c, hmem⟩
        have hle := card_faceLocalColumns_le_two b (localFace c)
        have hne : (faceLocalColumns b (localFace c)).card ≠ 1 := fun h => hc ⟨ho, h⟩
        have htwo : (faceLocalColumns b (localFace c)).card = 2 := by omega
        let F : PairFullFace k j := ⟨(b, localFace c), ho, htwo⟩
        let u : {v : LocalColumn (10 + 2 * k) b // v ∈ faceLocalColumns b (localFace c)} := ⟨c, hmem⟩
        refine ⟨.inr ((fullFaceEnumeration F).symm u, F), ?_⟩
        change B7Column.localColumn b (fullFaceColumn F ((fullFaceEnumeration F).symm u)) =
          B7Column.localColumn b c
        rw [fullFaceColumn, Equiv.apply_symm_apply]
      | motion _ _ _ => exact (hc ho).elim
      | extra _ _ _ => exact (hc ho).elim
      | remaining _ _ _ => simp [b7Owner] at ho

end IdealGeneration.CubicSupported.B5
