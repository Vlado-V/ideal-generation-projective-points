module

public import IdealGeneration.CubicSupportedPattern
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Local columns and face probes in Appendix B.5

A face counts the local columns with that *exact* monomial support. An edge
probe can also see the columns of its endpoint vertices. The exact-face
columns supply the diagonal full-face minors after ordering the proper-face
columns separately.
-/

namespace IdealGeneration.CubicSupported.B5

/-- A face of the coordinate simplex is a vertex or an increasing edge. -/
abbrev Face (m : ℕ) := Fin m ⊕ Edge m

/-- The old trace vertices belonging to a face. -/
def faceVertices {m : ℕ} : Face m → Finset (Fin m)
  | .inl i => {i}
  | .inr e => {e.val.1, e.val.2}

/-- Old vertices attached by a single edge to the new vertex in direction `b`. -/
def neighbor {m : ℕ} (b : Fin 2) (i : Fin m) : Prop :=
  singleLabels i.val (m + b.val)

instance {m : ℕ} (b : Fin 2) (i : Fin m) : Decidable (neighbor b i) :=
  inferInstanceAs (Decidable (singleLabels i.val (m + b.val)))

/-- The old edge and new edge used in the local slope labels. -/
def oldSlopeEdge {m : ℕ} (e : Edge m) : Edge (m + 2) :=
  ⟨(e.val.1.castAdd 2, e.val.2.castAdd 2), e.property⟩

def newSlopeEdge {m : ℕ} (b : Fin 2) (i : Fin m) : Edge (m + 2) :=
  ⟨(i.castAdd 2, b.natAdd m), by
    change i.val < m + b.val
    omega⟩

/-- The two local families of (B.7), in one fixed normal direction. -/
abbrev LocalColumn (m : ℕ) (b : Fin 2) :=
  {e : Edge m // single e = true} ⊕ ({i : Fin m // neighbor b i} × Fin m)

/-- The two trace coordinate factors of a local column. -/
def localEndpoints {m : ℕ} {b : Fin 2} : LocalColumn m b → Fin m × Fin m
  | .inl e => e.val.val
  | .inr i => (i.1.val, i.2)

/-- The single edge whose normal form labels a local column. -/
def localSlopeEdge {m : ℕ} {b : Fin 2} : LocalColumn m b → Edge (m + 2)
  | .inl e => oldSlopeEdge e.val
  | .inr i => newSlopeEdge b i.1.val

@[simp] theorem single_localSlopeEdge {m : ℕ} {b : Fin 2} (c : LocalColumn m b) :
    single (localSlopeEdge c) = true := by
  rcases c with e | i
  · exact (single_eq_true _).mpr ((single_eq_true _).mp e.property)
  · exact (single_eq_true _).mpr i.1.property

/-- The exact face supporting a quadratic monomial. -/
def monomialFace {m : ℕ} (i j : Fin m) : Face m :=
  if h : i < j then .inr ⟨(i, j), h⟩
  else if h' : j < i then .inr ⟨(j, i), h'⟩
  else .inl i

@[simp] theorem monomialFace_eq_vertex {m : ℕ} {i j v : Fin m} :
    monomialFace i j = Sum.inl v ↔ i = v ∧ j = v := by
  by_cases h : i < j
  · simp [monomialFace, h, show ¬ (i = v ∧ j = v) by rintro ⟨rfl, rfl⟩; omega]
  · by_cases h' : j < i
    · simp [monomialFace, h, h', show ¬ (i = v ∧ j = v) by rintro ⟨rfl, rfl⟩; omega]
    · have hij : i = j := by omega
      subst j
      simp [monomialFace]

@[simp] theorem monomialFace_eq_edge {m : ℕ} {i j : Fin m} (e : Edge m) :
    monomialFace i j = Sum.inr e ↔
      (i = e.val.1 ∧ j = e.val.2) ∨ (i = e.val.2 ∧ j = e.val.1) := by
  obtain ⟨⟨u, v⟩, huv⟩ := e
  change u < v at huv
  change _ ↔ (i = u ∧ j = v) ∨ (i = v ∧ j = u)
  by_cases h : i < j
  · have hrev : ¬ (i = v ∧ j = u) := by rintro ⟨rfl, rfl⟩; omega
    simp [monomialFace, h, hrev]
  · by_cases h' : j < i
    · have hfwd : ¬ (i = u ∧ j = v) := by rintro ⟨rfl, rfl⟩; omega
      simp [monomialFace, h, h', hfwd, and_comm]
    · have hij : i = j := by omega
      subst j
      have hfwd : ¬ (i = u ∧ i = v) := by rintro ⟨rfl, rfl⟩; omega
      have hrev : ¬ (i = v ∧ i = u) := by rintro ⟨rfl, rfl⟩; omega
      simp [monomialFace, hfwd, hrev]

/-- The exact support of a local column, ignoring its normal form. -/
def localFace {m : ℕ} {b : Fin 2} (c : LocalColumn m b) : Face m :=
  monomialFace (localEndpoints c).1 (localEndpoints c).2

@[simp] theorem localFace_old {m : ℕ} {b : Fin 2} (e : {e : Edge m // single e = true}) :
    localFace (b := b) (.inl e) = .inr e.val := by
  simp [localFace, localEndpoints, monomialFace, e.val.property]

/-- The local columns with exact support `F`. -/
def faceLocalColumns {m : ℕ} (b : Fin 2) : Face m → Finset (LocalColumn m b)
  | .inl i => if h : neighbor b i then {.inr (⟨i, h⟩, i)} else ∅
  | .inr e =>
      (if h : single e = true then {.inl ⟨e, h⟩} else ∅) ∪
      (if h : neighbor b e.val.1 then {.inr (⟨e.val.1, h⟩, e.val.2)} else ∅) ∪
      (if h : neighbor b e.val.2 then {.inr (⟨e.val.2, h⟩, e.val.1)} else ∅)

/-- The explicit enumeration contains exactly the local columns of the face. -/
@[simp] theorem mem_faceLocalColumns {m : ℕ} {b : Fin 2} (F : Face m)
    (c : LocalColumn m b) : c ∈ faceLocalColumns b F ↔ localFace c = F := by
  rcases F with i | e <;> rcases c with f | ⟨j, k⟩
  · by_cases hi : neighbor b i <;> simp [faceLocalColumns, hi]
  · change _ ↔ monomialFace j.val k = Sum.inl i
    by_cases hi : neighbor b i
    · simp [faceLocalColumns, hi, Subtype.ext_iff]
    · have hji : j.val ≠ i := fun h => hi (h ▸ j.property)
      simp [faceLocalColumns, hi, hji]
  · by_cases he : single e = true
    · by_cases hi : neighbor b e.val.1 <;> by_cases hj : neighbor b e.val.2 <;>
        simp [faceLocalColumns, he, hi, hj, Subtype.ext_iff]
    · have hfe : f.val ≠ e := fun h => he (h ▸ f.property)
      by_cases hi : neighbor b e.val.1 <;> by_cases hj : neighbor b e.val.2 <;>
        simp [faceLocalColumns, he, hi, hj, hfe]
  · change _ ↔ monomialFace j.val k = Sum.inr e
    by_cases hs : single e = true <;> by_cases hi : neighbor b e.val.1 <;>
      by_cases hj : neighbor b e.val.2
    all_goals simp only [faceLocalColumns, hs, hi, hj, dite_true, dite_false,
      Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, Sum.inr.injEq,
      Sum.inr_ne_inl, Prod.mk.injEq, false_or, or_false,
      monomialFace_eq_edge]
    all_goals first | rfl | (have h := j.property; grind)

/-- A face contributes one old-edge column exactly when it is a single edge. -/
def oldFaceCount {m : ℕ} : Face m → ℕ
  | .inl _ => 0
  | .inr e => if single e = true then 1 else 0

/-- The exact-face multiplicity is the number stated in (B.5). -/
theorem card_faceLocalColumns {m : ℕ} (b : Fin 2) (F : Face m) :
    (faceLocalColumns b F).card =
      oldFaceCount F + ((faceVertices F).filter (neighbor b)).card := by
  rcases F with i | e
  · by_cases hi : neighbor b i <;> simp [faceLocalColumns, oldFaceCount, faceVertices, Finset.filter_singleton, hi]
  · have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    have hji := hij.symm
    by_cases hs : single e = true <;> by_cases hi : neighbor b e.val.1 <;>
      by_cases hj : neighbor b e.val.2 <;>
      simp [faceLocalColumns, oldFaceCount, faceVertices, hs, hi, hj, hij, hji,
        Finset.singleton_union, Finset.insert_union, Finset.filter_insert, Finset.filter_singleton]

/-- A single old edge cannot have both endpoints in the new neighborhood. -/
theorem not_three_face_columns {m : ℕ} (b : Fin 2) (e : Edge m)
    (hs : single e = true) (hi : neighbor b e.val.1) (hj : neighbor b e.val.2) : False := by
  let i := e.val.1.castAdd 2
  let j := e.val.2.castAdd 2
  let w := b.natAdd m
  have hij : adjacent i j := Or.inl ((single_eq_true e).mp hs)
  have hjw : adjacent j w := Or.inl hj
  have hiw : adjacent i w := Or.inl hi
  exact triangle_free hij hjw hiw

/-- At a vertex only the square of its coordinate can have that exact support. -/
theorem card_faceLocalColumns_vertex_le_one {m : ℕ} (b : Fin 2) (i : Fin m) :
    (faceLocalColumns b (Sum.inl i)).card ≤ 1 := by
  by_cases hi : neighbor b i <;> simp [faceLocalColumns, hi]

/-- There are at most two local columns with the exact support of a face. -/
theorem card_faceLocalColumns_le_two {m : ℕ} (b : Fin 2) (F : Face m) :
    (faceLocalColumns b F).card ≤ 2 := by
  rw [card_faceLocalColumns]
  rcases F with i | e
  · by_cases hi : neighbor b i <;> simp [oldFaceCount, faceVertices, Finset.filter_singleton, hi]
  · have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    have hji := hij.symm
    by_cases hs : single e = true <;> by_cases hi : neighbor b e.val.1 <;>
      by_cases hj : neighbor b e.val.2
    · exact (not_three_face_columns b e hs hi hj).elim
    all_goals simp [oldFaceCount, faceVertices, Finset.filter_insert, Finset.filter_singleton,
      hs, hi, hj, hij]


/-- Fixing one factor, the exact monomial face determines the other factor. -/
theorem monomialFace_right_injective {m : ℕ} (i : Fin m) :
    Function.Injective (monomialFace i) := by
  intro j k h
  cases hF : monomialFace i j with
  | inl v =>
    have hj := (monomialFace_eq_vertex.mp hF).2
    have hk := (monomialFace_eq_vertex.mp (h.symm.trans hF)).2
    exact hj.trans hk.symm
  | inr e =>
    have hj := (monomialFace_eq_edge e).mp hF
    have hk := (monomialFace_eq_edge e).mp (h.symm.trans hF)
    have he := e.property
    rcases hj with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
      rcases hk with ⟨hi', hk⟩ | ⟨hi', hk⟩ <;> omega

/-- Two exact-face columns with the same slope edge are the same column. -/
theorem eq_of_localFace_eq_of_localSlopeEdge_eq {m : ℕ} {b : Fin 2}
    {c c' : LocalColumn m b} (hf : localFace c = localFace c')
    (he : localSlopeEdge c = localSlopeEdge c') : c = c' := by
  have h1 := congrArg (fun e : Edge (m + 2) => e.val.1.val) he
  have h2 := congrArg (fun e : Edge (m + 2) => e.val.2.val) he
  rcases c with e | ⟨i, j⟩ <;> rcases c' with e' | ⟨i', j'⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · change e.val.val.2.val = m + b.val at h2
    have hlt := e.val.val.2.isLt
    omega
  · change m + b.val = e'.val.val.2.val at h2
    have hlt := e'.val.val.2.isLt
    omega
  · have hii' : i = i' := Subtype.ext (Fin.ext h1)
    subst i'
    have hjj' : j = j' := monomialFace_right_injective i.val hf
    subst j'
    rfl

section Evaluation

open MvPolynomial
variable {K : Type*} [Field K] {m : ℕ} {b : Fin 2}

/-- The normalized probe on a vertex or on an edge, with nonzero edge parameter. -/
def faceProbe : Face m → K → Fin m → K
  | .inl i, _ => vertexSupport i 1
  | .inr e, lam => edgeSupport e 1 lam

/-- A coordinate of a probe is nonzero exactly on the indicated face. -/
theorem faceProbe_ne_zero_iff (F : Face m) {lam : K} (hlam : lam ≠ 0) (i : Fin m) :
    faceProbe F lam i ≠ 0 ↔ i ∈ faceVertices F := by
  rcases F with j | e
  · by_cases h : i = j <;> simp [faceProbe, faceVertices, vertexSupport, h]
  · have h12 : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    by_cases h1 : i = e.val.1
    · subst i
      simp [faceProbe, faceVertices, edgeSupport, vertexSupport, h12]
    · by_cases h2 : i = e.val.2
      · subst i
        simp [faceProbe, faceVertices, edgeSupport, vertexSupport, h12.symm, hlam]
      · simp [faceProbe, faceVertices, edgeSupport, vertexSupport, h1, h2]

/-- A unit weight in a single normal direction. -/
def pureDirection (b : Fin 2) (j : Fin 2) : K := if j = b then 1 else 0

/-- The actual local vector column value with the direction weight included. -/
def localValue (P : Parameters K (m + 2)) (c : LocalColumn m b)
    (y : Fin m → K) (w : Fin 2 → K) (j : Fin 2) : K :=
  w b * (y (localEndpoints c).1 * y (localEndpoints c).2) *
    ![P.edgeSlope (localSlopeEdge c) 0, -1] j

/-- The genuine polynomial local column in the old trace and weight variables. -/
noncomputable def localPolynomial (P : Parameters K (m + 2)) (c : LocalColumn m b)
    (j : Fin 2) : MvPolynomial (Fin m ⊕ Fin 2) K :=
  X (.inr b) * (X (.inl (localEndpoints c).1) * X (.inl (localEndpoints c).2)) *
    C (![P.edgeSlope (localSlopeEdge c) 0, -1] j)

/-- The explicit local values evaluate the genuine polynomial columns. -/
theorem eval_localPolynomial (P : Parameters K (m + 2)) (c : LocalColumn m b)
    (y : Fin m → K) (w : Fin 2 → K) (j : Fin 2) :
    eval (Sum.elim y w) (localPolynomial P c j) = localValue P c y w j := by
  simp [localPolynomial, localValue]

/-- A probe of another direction annihilates every local column of direction `b`. -/
theorem localValue_wrong_direction (P : Parameters K (m + 2)) (c : LocalColumn m b)
    (y : Fin m → K) {b' : Fin 2} (h : b ≠ b') (j : Fin 2) :
    localValue P c y (pureDirection b') j = 0 := by
  simp [localValue, pureDirection, h]

/-- A probe kills any local column whose monomial support leaves its face. -/
theorem localValue_eq_zero_of_not_supported (P : Parameters K (m + 2))
    (c : LocalColumn m b) (F : Face m) {lam : K} (hlam : lam ≠ 0)
    (h : ¬ ((localEndpoints c).1 ∈ faceVertices F ∧
      (localEndpoints c).2 ∈ faceVertices F)) (w : Fin 2 → K) (j : Fin 2) :
    localValue P c (faceProbe F lam) w j = 0 := by
  by_cases h1 : (localEndpoints c).1 ∈ faceVertices F
  · have h2 : (localEndpoints c).2 ∉ faceVertices F := fun h2 => h ⟨h1, h2⟩
    have hz : faceProbe F lam (localEndpoints c).2 = 0 := by
      by_contra hn
      exact h2 ((faceProbe_ne_zero_iff F hlam _).mp hn)
    simp [localValue, hz]
  · have hz : faceProbe F lam (localEndpoints c).1 = 0 := by
      by_contra hn
      exact h1 ((faceProbe_ne_zero_iff F hlam _).mp hn)
    simp [localValue, hz]

/-- Distinct exact edge supports cannot see one another at face probes. -/
theorem localValue_eq_zero_of_other_face (P : Parameters K (m + 2))
    (c : LocalColumn m b) (F : Face m) {lam : K} (hlam : lam ≠ 0)
    (hends : (localEndpoints c).1 ≠ (localEndpoints c).2)
    (hface : localFace c ≠ F) (w : Fin 2 → K) (j : Fin 2) :
    localValue P c (faceProbe F lam) w j = 0 := by
  apply localValue_eq_zero_of_not_supported P c F hlam _ w j
  rintro ⟨hi, hj⟩
  apply hface
  rcases F with i | e
  · simp only [faceVertices, Finset.mem_singleton] at hi hj
    exact (hends (hi.trans hj.symm)).elim
  · simp only [faceVertices, Finset.mem_insert, Finset.mem_singleton] at hi hj
    apply (monomialFace_eq_edge e).mpr
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hends (hi.trans hj.symm)).elim
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨hi, hj⟩
    · exact (hends (hi.trans hj.symm)).elim

/-- The exact support of any full-face column has two distinct endpoints. -/
theorem localEndpoints_ne_of_full_face (c : LocalColumn m b)
    (hfull : (faceLocalColumns b (localFace c)).card = 2) :
    (localEndpoints c).1 ≠ (localEndpoints c).2 := by
  intro h
  have hf : localFace c = Sum.inl (localEndpoints c).1 :=
    monomialFace_eq_vertex.mpr ⟨rfl, h.symm⟩
  rw [hf] at hfull
  have hle := card_faceLocalColumns_vertex_le_one b (localEndpoints c).1
  omega

/-- A full-face column evaluates to zero on every other face. This gives the
zero off-diagonal entries among full-face pivots of one direction. -/
theorem localValue_full_face_off_diagonal (P : Parameters K (m + 2))
    (c : LocalColumn m b) (F : Face m) {lam : K} (hlam : lam ≠ 0)
    (hfull : (faceLocalColumns b (localFace c)).card = 2)
    (hface : localFace c ≠ F) (w : Fin 2 → K) (j : Fin 2) :
    localValue P c (faceProbe F lam) w j = 0 :=
  localValue_eq_zero_of_other_face P c F hlam (localEndpoints_ne_of_full_face c hfull)
    hface w j

/-- The scalar monomial factor at a column's own normalized face probe. -/
def faceScale (F : Face m) (lam : K) : K :=
  match F with
  | .inl _ => 1
  | .inr _ => lam

/-- A local column on its exact face has its monomial factor times its normal form. -/
theorem localValue_own_face (P : Parameters K (m + 2)) (c : LocalColumn m b)
    (F : Face m) (lam : K) (h : localFace c = F) (j : Fin 2) :
    localValue P c (faceProbe F lam) (pureDirection b) j =
      faceScale F lam * ![P.edgeSlope (localSlopeEdge c) 0, -1] j := by
  rcases F with i | e
  · obtain ⟨h1, h2⟩ := monomialFace_eq_vertex.mp h
    simp [localValue, pureDirection, faceProbe, faceScale, h1, h2, vertexSupport]
  · have h12 : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    have h21 := h12.symm
    rcases (monomialFace_eq_edge e).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [localValue, pureDirection, faceProbe, faceScale, h1, h2, edgeSupport,
        vertexSupport, h12, h21]

/-- The two columns in a full-face pivot, evaluated in their pure direction. -/
def fullFaceMinor (P : Parameters K (m + 2)) (c₀ c₁ : LocalColumn m b)
    (F : Face m) (lam : K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => localValue P (![c₀, c₁] j) (faceProbe F lam) (pureDirection b) i

/-- The exact determinant of the two columns belonging to a full face. -/
theorem det_fullFaceMinor (P : Parameters K (m + 2)) (c₀ c₁ : LocalColumn m b)
    (F : Face m) (lam : K) (h₀ : c₀ ∈ faceLocalColumns b F)
    (h₁ : c₁ ∈ faceLocalColumns b F) :
    (fullFaceMinor P c₀ c₁ F lam).det =
      faceScale F lam ^ 2 *
        (P.edgeSlope (localSlopeEdge c₁) 0 - P.edgeSlope (localSlopeEdge c₀) 0) := by
  rw [Matrix.det_fin_two]
  simp only [fullFaceMinor, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    localValue_own_face P c₀ F lam ((mem_faceLocalColumns F c₀).mp h₀),
    localValue_own_face P c₁ F lam ((mem_faceLocalColumns F c₁).mp h₁)]
  ring

/-- Nonzero probe coordinates and distinct single slopes make the full-face pivot invertible. -/
theorem det_fullFaceMinor_ne_zero (P : Parameters K (m + 2)) (c₀ c₁ : LocalColumn m b)
    (F : Face m) {lam : K} (hlam : lam ≠ 0) (h₀ : c₀ ∈ faceLocalColumns b F)
    (h₁ : c₁ ∈ faceLocalColumns b F)
    (hτ : P.edgeSlope (localSlopeEdge c₁) 0 ≠ P.edgeSlope (localSlopeEdge c₀) 0) :
    (fullFaceMinor P c₀ c₁ F lam).det ≠ 0 := by
  rw [det_fullFaceMinor P c₀ c₁ F lam h₀ h₁]
  have hs : faceScale F lam ≠ 0 := by rcases F <;> simp [faceScale, hlam]
  exact mul_ne_zero (pow_ne_zero _ hs) (sub_ne_zero.mpr hτ)


/-- Each full face has a nonsingular local pivot when the single-edge slopes are distinct. -/
theorem exists_fullFaceMinor_ne_zero (P : Parameters K (m + 2))
    (F : Face m) {lam : K} (hlam : lam ≠ 0)
    (hfull : (faceLocalColumns b F).card = 2)
    (hτ : Set.InjOn (fun e : Edge (m + 2) => P.edgeSlope e 0) {e | single e = true}) :
    ∃ c₀ c₁ : LocalColumn m b, faceLocalColumns b F = {c₀, c₁} ∧
      (fullFaceMinor P c₀ c₁ F lam).det ≠ 0 := by
  obtain ⟨c₀, c₁, hne, hcols⟩ := Finset.card_eq_two.mp hfull
  have h₀ : c₀ ∈ faceLocalColumns b F := by simp [hcols]
  have h₁ : c₁ ∈ faceLocalColumns b F := by simp [hcols]
  refine ⟨c₀, c₁, hcols, det_fullFaceMinor_ne_zero P c₀ c₁ F hlam h₀ h₁ ?_⟩
  intro he
  apply hne
  apply eq_of_localFace_eq_of_localSlopeEdge_eq
  · exact ((mem_faceLocalColumns F c₀).mp h₀).trans ((mem_faceLocalColumns F c₁).mp h₁).symm
  · exact hτ (single_localSlopeEdge c₀) (single_localSlopeEdge c₁) he.symm

end Evaluation
end IdealGeneration.CubicSupported.B5
