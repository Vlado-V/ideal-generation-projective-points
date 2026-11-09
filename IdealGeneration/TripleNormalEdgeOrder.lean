module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Integer weights and the ordered edge triples in the three-normal enlargement. -/

namespace IdealGeneration.TripleNormal.EdgeOrder

variable {N : ℕ}

def gap (N : ℕ) : ℕ := 2 * N + 10

def oldWeight (i : Fin N) : ℕ := 10 * i.val + 1

def newWeight (N : ℕ) (b : Fin 3) : ℕ := 10 * (gap N + b.val) + b.val + 1

def rootWeight (N : ℕ) (r : Fin 3) : ℕ := 100 * gap N + 100 * r.val + 1

abbrev NonrootEdge (N : ℕ) := Fin N × Fin 3

def edgeCode (e : NonrootEdge N) : ℕ := 10 * (e.1.val + e.2.val) + e.2.val

def nonrootDegree (e : NonrootEdge N) : ℕ := oldWeight e.1 + newWeight N e.2

def triangleDegree (N : ℕ) (b b' : Fin 3) : ℕ := newWeight N b + newWeight N b'

def rootDegree (N : ℕ) (e : Fin 3 × Fin 3) : ℕ := rootWeight N e.1 + newWeight N e.2

theorem nonrootDegree_eq (e : NonrootEdge N) :
    nonrootDegree e = 10 * gap N + edgeCode e + 2 := by
  unfold nonrootDegree oldWeight newWeight edgeCode
  omega

theorem edgeCode_lt_iff (e f : NonrootEdge N) :
    edgeCode e < edgeCode f ↔
      e.1.val + e.2.val < f.1.val + f.2.val ∨
        e.1.val + e.2.val = f.1.val + f.2.val ∧ e.2.val < f.2.val := by
  have he := e.2.isLt
  have hf := f.2.isLt
  unfold edgeCode
  omega

/-- The initial triple consists of the one edge at sum zero and the two at sum one. -/
def firstEdges (hN : 5 ≤ N) : Fin 3 → NonrootEdge N :=
  ![(⟨0, by omega⟩, 0), (⟨1, by omega⟩, 0), (⟨0, by omega⟩, 1)]

/-- The final triple consists of the two edges at sum `N` and the one at sum `N+1`. -/
def lastEdges (hN : 5 ≤ N) : Fin 3 → NonrootEdge N :=
  ![(⟨N - 1, by omega⟩, 1), (⟨N - 2, by omega⟩, 2), (⟨N - 1, by omega⟩, 2)]

/-- The `g`-th triple in increasing degree order. Interior triples have sum `g+1`. -/
def edgeAt (hN : 5 ≤ N) (g : Fin N) (k : Fin 3) : NonrootEdge N :=
  if hg : g.val = 0 then firstEdges hN k
  else if hl : g.val + 1 = N then lastEdges hN k
  else (⟨g.val + 1 - k.val, by omega⟩, k)

theorem edgeAt_first (hN : 5 ≤ N) (g : Fin N) (hg : g.val = 0) (k : Fin 3) :
    edgeAt hN g k = firstEdges hN k := by
  simp [edgeAt, hg]

theorem edgeAt_last (hN : 5 ≤ N) (g : Fin N) (hg : g.val + 1 = N) (k : Fin 3) :
    edgeAt hN g k = lastEdges hN k := by
  have hz : g.val ≠ 0 := by omega
  simp [edgeAt, hz, hg]

theorem edgeAt_middle (hN : 5 ≤ N) (g : Fin N) (hg : 0 < g.val)
    (hl : g.val + 1 < N) (k : Fin 3) :
    edgeAt hN g k = (⟨g.val + 1 - k.val, by omega⟩, k) := by
  have hz : g.val ≠ 0 := by omega
  have hn : g.val + 1 ≠ N := by omega
  simp [edgeAt, hz, hn]

theorem edgeCode_first (hN : 5 ≤ N) (g : Fin N) (hg : g.val = 0) (k : Fin 3) :
    edgeCode (edgeAt hN g k) = (![0, 10, 11] : Fin 3 → ℕ) k := by
  rw [edgeAt_first hN g hg]
  fin_cases k <;> rfl

theorem edgeCode_last (hN : 5 ≤ N) (g : Fin N) (hg : g.val + 1 = N) (k : Fin 3) :
    edgeCode (edgeAt hN g k) = (![10 * N + 1, 10 * N + 2, 10 * (N + 1) + 2] : Fin 3 → ℕ) k := by
  rw [edgeAt_last hN g hg]
  fin_cases k
  · change 10 * ((N - 1) + 1) + 1 = 10 * N + 1
    omega
  · change 10 * ((N - 2) + 2) + 2 = 10 * N + 2
    omega
  · change 10 * ((N - 1) + 2) + 2 = 10 * (N + 1) + 2
    omega

theorem edgeCode_middle (hN : 5 ≤ N) (g : Fin N) (hg : 0 < g.val)
    (hl : g.val + 1 < N) (k : Fin 3) :
    edgeCode (edgeAt hN g k) = 10 * (g.val + 1) + k.val := by
  rw [edgeAt_middle hN g hg hl]
  change 10 * ((g.val + 1 - k.val) + k.val) + k.val = _
  have hk := k.isLt
  omega

theorem edgeCode_strictMono_slot (hN : 5 ≤ N) (g : Fin N) :
    StrictMono (fun k => edgeCode (edgeAt hN g k)) := by
  intro k l hkl
  change edgeCode (edgeAt hN g k) < edgeCode (edgeAt hN g l)
  by_cases hg : g.val = 0
  · rw [edgeCode_first hN g hg, edgeCode_first hN g hg]
    fin_cases k <;> fin_cases l <;> simp_all
  · by_cases hl : g.val + 1 = N
    · rw [edgeCode_last hN g hl, edgeCode_last hN g hl]
      fin_cases k <;> fin_cases l <;> simp_all
      omega
    · rw [edgeCode_middle hN g (by omega) (by omega),
          edgeCode_middle hN g (by omega) (by omega)]
      exact Nat.add_lt_add_left hkl _

private theorem edgeCode_le_of_not_last (hN : 5 ≤ N) (g : Fin N)
    (hg : g.val + 1 < N) (k : Fin 3) :
    edgeCode (edgeAt hN g k) ≤ 10 * (g.val + 1) + 2 := by
  by_cases hz : g.val = 0
  · rw [edgeCode_first hN g hz]
    fin_cases k <;> simp_all
  · rw [edgeCode_middle hN g (by omega) hg]
    have hk := k.isLt
    omega

private theorem le_edgeCode_of_not_first (hN : 5 ≤ N) (g : Fin N)
    (hg : 0 < g.val) (k : Fin 3) :
    10 * (g.val + 1) ≤ edgeCode (edgeAt hN g k) := by
  by_cases hl : g.val + 1 = N
  · rw [edgeCode_last hN g hl]
    fin_cases k <;> simp_all
    omega
  · rw [edgeCode_middle hN g hg (by omega)]
    omega

theorem edgeCode_lt_of_group_lt (hN : 5 ≤ N) {g g' : Fin N} (hg : g < g')
    (k k' : Fin 3) : edgeCode (edgeAt hN g k) < edgeCode (edgeAt hN g' k') := by
  have huv := edgeCode_le_of_not_last hN g (by omega) k
  have hlv := le_edgeCode_of_not_first hN g' (by omega) k'
  omega

/-- Consecutive positions are grouped by threes, using group-major order. -/
def orderedEdge (hN : 5 ≤ N) (i : Fin (N * 3)) : NonrootEdge N :=
  let p := (finProdFinEquiv : Fin N × Fin 3 ≃ Fin (N * 3)).symm i
  edgeAt hN p.1 p.2

theorem orderedEdge_code_strictMono (hN : 5 ≤ N) :
    StrictMono (fun i => edgeCode (orderedEdge hN i)) := by
  intro i j hij
  let e := (finProdFinEquiv : Fin N × Fin 3 ≃ Fin (N * 3))
  let p := e.symm i
  let q := e.symm j
  have hp := congrArg Fin.val (e.apply_symm_apply i)
  have hq := congrArg Fin.val (e.apply_symm_apply j)
  change p.2.val + 3 * p.1.val = i.val at hp
  change q.2.val + 3 * q.1.val = j.val at hq
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  change edgeCode (edgeAt hN p.1 p.2) < edgeCode (edgeAt hN q.1 q.2)
  by_cases hpq : p.1 < q.1
  · exact edgeCode_lt_of_group_lt hN hpq p.2 q.2
  · have hg : p.1 = q.1 := Fin.ext (by omega)
    have hk : p.2 < q.2 := by omega
    rw [hg]
    exact edgeCode_strictMono_slot hN q.1 hk

theorem orderedEdge_degree_strictMono (hN : 5 ≤ N) :
    StrictMono (fun i => nonrootDegree (orderedEdge hN i)) := by
  intro i j hij
  have hc : edgeCode (orderedEdge hN i) < edgeCode (orderedEdge hN j) :=
    orderedEdge_code_strictMono hN hij
  change nonrootDegree (orderedEdge hN i) < nonrootDegree (orderedEdge hN j)
  rw [nonrootDegree_eq, nonrootDegree_eq]
  omega

@[simp] theorem orderedEdge_apply_prod (hN : 5 ≤ N) (g : Fin N) (k : Fin 3) :
    orderedEdge hN (finProdFinEquiv (g, k)) = edgeAt hN g k := by
  simp [orderedEdge]

theorem edgeAt_bijective (hN : 5 ≤ N) :
    Function.Bijective (fun p : Fin N × Fin 3 => edgeAt hN p.1 p.2) := by
  have hi : Function.Injective (fun p : Fin N × Fin 3 => edgeAt hN p.1 p.2) := by
    intro p q hpq
    let e := (finProdFinEquiv : Fin N × Fin 3 ≃ Fin (N * 3))
    apply e.injective
    apply (orderedEdge_code_strictMono hN).injective
    simpa only [orderedEdge, e, Equiv.symm_apply_apply] using congrArg edgeCode hpq
  exact ⟨hi, Finite.surjective_of_injective hi⟩

theorem orderedEdge_bijective (hN : 5 ≤ N) : Function.Bijective (orderedEdge hN) :=
  (edgeAt_bijective hN).comp (finProdFinEquiv : Fin N × Fin 3 ≃ Fin (N * 3)).symm.bijective

/-- An interior triple is a matching: distinct slots have distinct old and new endpoints. -/
theorem middle_disjoint (hN : 5 ≤ N) (g : Fin N) (hg : 0 < g.val)
    (hl : g.val + 1 < N) {k l : Fin 3} (hkl : k ≠ l) :
    (edgeAt hN g k).1 ≠ (edgeAt hN g l).1 ∧
      (edgeAt hN g k).2 ≠ (edgeAt hN g l).2 := by
  rw [edgeAt_middle hN g hg hl, edgeAt_middle hN g hg hl]
  refine ⟨?_, hkl⟩
  intro h
  have hv := congrArg Fin.val h
  change g.val + 1 - k.val = g.val + 1 - l.val at hv
  exact hkl (Fin.ext (by omega))

/-- In the initial triple the first two edges meet at a new endpoint avoided by the third. -/
theorem first_incidence (hN : 5 ≤ N) :
    (firstEdges hN 0).2 = (firstEdges hN 1).2 ∧
      (firstEdges hN 0).1 ≠ (firstEdges hN 1).1 ∧
      (firstEdges hN 2).2 ≠ (firstEdges hN 0).2 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  · change (1 : Fin 3) ≠ 0
    decide

/-- In the final triple the last two edges meet at a new endpoint avoided by the first. -/
theorem last_incidence (hN : 5 ≤ N) :
    (lastEdges hN 1).2 = (lastEdges hN 2).2 ∧
      (lastEdges hN 1).1 ≠ (lastEdges hN 2).1 ∧
      (lastEdges hN 0).2 ≠ (lastEdges hN 1).2 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    change N - 2 = N - 1 at hv
    omega
  · change (1 : Fin 3) ≠ 2
    decide

abbrev TriangleEdge := {e : Fin 3 × Fin 3 // e.1 < e.2}

def triangleAt : Fin 3 → TriangleEdge :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]

theorem triangleAt_bijective : Function.Bijective triangleAt := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [triangleAt]
  · rintro ⟨⟨b, b'⟩, hlt⟩
    fin_cases b <;> fin_cases b' <;>
      first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | simp [Fin.lt_def] at hlt

theorem triangleAt_degree_strictMono (N : ℕ) :
    StrictMono (fun i => triangleDegree N (triangleAt i).val.1 (triangleAt i).val.2) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [triangleAt, triangleDegree, newWeight] <;> omega

/-- Every triangle degree is strictly larger than every old-nonroot–new degree. -/
theorem nonrootDegree_lt_triangleDegree (e : NonrootEdge N) (b b' : Fin 3) :
    nonrootDegree e < triangleDegree N b b' := by
  have hi := e.1.isLt
  have hb := e.2.isLt
  unfold nonrootDegree triangleDegree oldWeight newWeight gap
  omega

/-- The nine root–new edges have distinct degrees, ordered by root and then new index. -/
theorem rootDegree_lt_iff (N : ℕ) (e f : Fin 3 × Fin 3) :
    rootDegree N e < rootDegree N f ↔
      e.1 < f.1 ∨ e.1 = f.1 ∧ e.2 < f.2 := by
  have he := e.2.isLt
  have hf := f.2.isLt
  simp only [rootDegree, rootWeight, newWeight, Fin.lt_def, Fin.ext_iff]
  omega

theorem rootDegree_injective (N : ℕ) : Function.Injective (rootDegree N) := by
  intro e f h
  have he := e.2.isLt
  have hf := f.2.isLt
  unfold rootDegree rootWeight newWeight at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

def rootAt : Fin 9 → Fin 3 × Fin 3 :=
  (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm

theorem rootAt_bijective : Function.Bijective rootAt :=
  (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm.bijective

theorem rootAt_degree_strictMono (N : ℕ) : StrictMono (fun i => rootDegree N (rootAt i)) := by
  intro i j hij
  let e := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)
  let p := rootAt i
  let q := rootAt j
  have hp := congrArg Fin.val (e.apply_symm_apply i)
  have hq := congrArg Fin.val (e.apply_symm_apply j)
  change p.2.val + 3 * p.1.val = i.val at hp
  change q.2.val + 3 * q.1.val = j.val at hq
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  apply (rootDegree_lt_iff N p q).mpr
  by_cases h : p.1 < q.1
  · exact Or.inl h
  · exact Or.inr ⟨Fin.ext (by omega), by omega⟩

theorem triangleDegree_lt_rootDegree (N : ℕ) (b b' : Fin 3) (e : Fin 3 × Fin 3) :
    triangleDegree N b b' < rootDegree N e := by
  have hb := b.isLt
  have hb' := b'.isLt
  unfold triangleDegree rootDegree newWeight rootWeight gap
  omega

theorem nonrootDegree_lt_rootDegree (e : NonrootEdge N) (f : Fin 3 × Fin 3) :
    nonrootDegree e < rootDegree N f :=
  (nonrootDegree_lt_triangleDegree e 0 1).trans (triangleDegree_lt_rootDegree N 0 1 f)

abbrev Edge (N : ℕ) := NonrootEdge N ⊕ (TriangleEdge ⊕ (Fin 3 × Fin 3))

def degree (N : ℕ) : Edge N → ℕ :=
  Sum.elim nonrootDegree (Sum.elim (fun e => triangleDegree N e.val.1 e.val.2) (rootDegree N))

/-- The full ordered edge list, with the nonroot, triangle, and root blocks in sequence. -/
noncomputable def allEdges (hN : 5 ≤ N) : Fin (N * 3 + 12) ≃ Edge N :=
  (finSumFinEquiv : Fin (N * 3) ⊕ Fin 12 ≃ Fin (N * 3 + 12)).symm.trans
    (Equiv.sumCongr (Equiv.ofBijective (orderedEdge hN) (orderedEdge_bijective hN))
      ((finSumFinEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12).symm.trans
        (Equiv.sumCongr (Equiv.ofBijective triangleAt triangleAt_bijective)
          (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm)))

@[simp] theorem allEdges_nonroot (hN : 5 ≤ N) (i : Fin (N * 3)) :
    allEdges hN (i.castAdd 12) = Sum.inl (orderedEdge hN i) := by
  simp [allEdges, Equiv.sumCongr]

@[simp] theorem allEdges_triangle (hN : 5 ≤ N) (i : Fin 3) :
    allEdges hN ((i.castAdd 9).natAdd (N * 3)) = Sum.inr (Sum.inl (triangleAt i)) := by
  have hs : (finSumFinEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12).symm (i.castAdd 9) = Sum.inl i :=
    finSumFinEquiv_symm_apply_castAdd i
  simp [allEdges, Equiv.sumCongr, hs]

@[simp] theorem allEdges_root (hN : 5 ≤ N) (i : Fin 9) :
    allEdges hN ((i.natAdd 3).natAdd (N * 3)) = Sum.inr (Sum.inr (rootAt i)) := by
  have hs : (finSumFinEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12).symm (i.natAdd 3) = Sum.inr i :=
    finSumFinEquiv_symm_apply_natAdd i
  simp [allEdges, Equiv.sumCongr, rootAt, hs]

private theorem strictMono_append {m n : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ)
    (hf : StrictMono f) (hg : StrictMono g) (hfg : ∀ i j, f i < g j) :
    StrictMono (fun i : Fin (m + n) => Fin.addCases (motive := fun _ => ℕ) f g i) := by
  intro i j hij
  let e := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · have h : i < j := hij
    simpa only [e, finSumFinEquiv_apply_left, Fin.addCases_left] using hf h
  · simpa only [e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.addCases_left, Fin.addCases_right] using hfg i j
  · have h : m + i.val < j.val := hij
    omega
  · have h : m + i.val < m + j.val := hij
    have h' : i < j := by omega
    simpa only [e, finSumFinEquiv_apply_right, Fin.addCases_right] using hg h'

theorem allEdges_degree_strictMono (hN : 5 ≤ N) :
    StrictMono (fun i => degree N (allEdges hN i)) := by
  let f : Fin (N * 3) → ℕ := fun i => nonrootDegree (orderedEdge hN i)
  let g : Fin 3 → ℕ := fun i => triangleDegree N (triangleAt i).val.1 (triangleAt i).val.2
  let k : Fin 9 → ℕ := fun i => rootDegree N (rootAt i)
  let tail : Fin 12 → ℕ := fun i => Fin.addCases g k i
  have htail : StrictMono tail := strictMono_append g k (triangleAt_degree_strictMono N)
    (rootAt_degree_strictMono N) (fun i j => triangleDegree_lt_rootDegree N _ _ _)
  have hcross : ∀ i j, f i < tail j := by
    intro i j
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12).surjective j
    rcases j with j | j
    · simpa only [tail, f, g, finSumFinEquiv_apply_left, Fin.addCases_left] using
        nonrootDegree_lt_triangleDegree (orderedEdge hN i) (triangleAt j).val.1 (triangleAt j).val.2
    · simpa only [tail, f, k, finSumFinEquiv_apply_right, Fin.addCases_right] using
        nonrootDegree_lt_rootDegree (orderedEdge hN i) (rootAt j)
  have hEq : (fun i => degree N (allEdges hN i)) =
      (fun i : Fin (N * 3 + 12) => Fin.addCases f tail i) := by
    funext i
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin (N * 3) ⊕ Fin 12 ≃ Fin (N * 3 + 12)).surjective i
    rcases i with i | i
    · simp [degree, f]
    · obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12).surjective i
      rcases i with i | i
      · change degree N (allEdges hN ((i.castAdd 9).natAdd (N * 3))) =
          Fin.addCases f tail ((i.castAdd 9).natAdd (N * 3))
        simp [degree, tail, g]
      · change degree N (allEdges hN ((i.natAdd 3).natAdd (N * 3))) =
          Fin.addCases f tail ((i.natAdd 3).natAdd (N * 3))
        simp [degree, tail, k]
  rw [hEq]
  exact strictMono_append f tail (orderedEdge_degree_strictMono hN) htail hcross

end IdealGeneration.TripleNormal.EdgeOrder
