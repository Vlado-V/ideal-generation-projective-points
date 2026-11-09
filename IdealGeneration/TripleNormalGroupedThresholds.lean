module

public import IdealGeneration.TripleNormalGroupedLeadingBlock
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Degree thresholds for the plane triples and the nine root blocks. -/

namespace IdealGeneration.TripleNormal

variable {G : ℕ}

/-- The sorted degree list has three edges per plane group, followed by nine root edges. -/
def groupedDegreeIndex : GroupedLeadingCol G → Fin (3 * G + 9)
  | .inl (g, e, _) => ⟨3 * g.val + e.val, by omega⟩
  | .inr (r, _) => ⟨3 * G + r.val, by omega⟩

/-- Doubling the edge degrees leaves an integer threshold strictly between consecutive degrees. -/
def groupedColumnDegree (d : Fin (3 * G + 9) → ℕ) (j : GroupedLeadingCol G) : ℕ :=
  2 * d (groupedDegreeIndex j)

/-- Start the first two plane edges at the first block and the last edge at the second. -/
def groupedAssignedBlock : GroupedLeadingCol G → ℕ
  | .inl (g, e, _) => 2 * g.val + if e.val = 2 then 1 else 0
  | .inr (r, _) => 2 * G + r.val

/-- The index of the edge used as the threshold after block `k`. -/
private def thresholdIndex (G k : ℕ) : Fin (3 * G + 9) :=
  if hk : k < 2 * G then ⟨3 * (k / 2) + (k % 2 + 1), by omega⟩
  else if hr : k < 2 * G + 9 then ⟨3 * G + (k - 2 * G), by omega⟩
  else ⟨3 * G + 8, by omega⟩

private def thresholdOffset (G k : ℕ) : ℕ :=
  if k < 2 * G ∧ k % 2 = 0 then 0 else 1

/-- The threshold at the middle plane edge equals its degree. Every other
threshold is odd and therefore strictly between, or beyond, doubled degrees. -/
def groupedThreshold (d : Fin (3 * G + 9) → ℕ) (k : ℕ) : ℕ :=
  2 * d (thresholdIndex G k) + thresholdOffset G k

private theorem thresholdIndex_lt_before (j : GroupedLeadingCol G) {k : ℕ}
    (hk : k < groupedAssignedBlock j) : thresholdIndex G k < groupedDegreeIndex j := by
  rcases j with ⟨g, e, a⟩ | ⟨r, a⟩
  · simp only [groupedAssignedBlock] at hk
    unfold thresholdIndex groupedDegreeIndex
    split_ifs <;> simp only [Fin.lt_def] <;> split_ifs at hk <;> omega
  · simp only [groupedAssignedBlock] at hk
    unfold thresholdIndex groupedDegreeIndex
    split_ifs <;> simp only [Fin.lt_def] <;> omega

private theorem thresholdIndex_le_after (j : GroupedLeadingCol G) {k : ℕ}
    (hk : groupedAssignedBlock j ≤ k) : groupedDegreeIndex j ≤ thresholdIndex G k := by
  rcases j with ⟨g, e, a⟩ | ⟨r, a⟩
  · simp only [groupedAssignedBlock] at hk
    unfold thresholdIndex groupedDegreeIndex
    split_ifs <;> simp only [Fin.le_def] <;> split_ifs at hk <;> omega
  · simp only [groupedAssignedBlock] at hk
    unfold thresholdIndex groupedDegreeIndex
    split_ifs <;> simp only [Fin.le_def] <;> omega

private theorem thresholdOffset_le_one (k : ℕ) : thresholdOffset G k ≤ 1 := by
  unfold thresholdOffset
  split_ifs <;> omega

/-- Each earlier threshold is below the column degree. -/
theorem groupedThreshold_le_before (d : Fin (3 * G + 9) → ℕ) (hd : StrictMono d)
    (j : GroupedLeadingCol G) (k : ℕ) (hk : k < groupedAssignedBlock j) :
    groupedThreshold d k ≤ groupedColumnDegree d j := by
  have hlt := hd (thresholdIndex_lt_before j hk)
  have hgap := thresholdOffset_le_one (G := G) k
  unfold groupedThreshold groupedColumnDegree
  omega

/-- The threshold at or after the assigned block is at least the column degree. -/
theorem groupedThreshold_ge_after (d : Fin (3 * G + 9) → ℕ) (hd : StrictMono d)
    (j : GroupedLeadingCol G) (k : ℕ) (hk : groupedAssignedBlock j ≤ k) :
    groupedColumnDegree d j ≤ groupedThreshold d k := by
  have hle := hd.monotone (thresholdIndex_le_after j hk)
  unfold groupedThreshold groupedColumnDegree
  omega

private def isSharedColumn : GroupedLeadingCol G → Prop
  | .inl (_, e, _) => e.val = 1
  | .inr _ => False

private theorem groupedThreshold_eq_columnDegree_iff (d : Fin (3 * G + 9) → ℕ)
    (hd : StrictMono d) (j : GroupedLeadingCol G) (k : ℕ) :
    groupedThreshold d k = groupedColumnDegree d j ↔
      k = groupedAssignedBlock j ∧ isSharedColumn j := by
  have heq : groupedThreshold d k = groupedColumnDegree d j ↔
      thresholdIndex G k = groupedDegreeIndex j ∧ thresholdOffset G k = 0 := by
    unfold groupedThreshold groupedColumnDegree
    have ho := thresholdOffset_le_one (G := G) k
    constructor
    · intro he
      exact ⟨hd.injective (by omega), by omega⟩
    · rintro ⟨he, hz⟩
      rw [he, hz, add_zero]
  rw [heq]
  clear heq hd d
  by_cases hmid : k < 2 * G ∧ k % 2 = 0
  · have ho : thresholdOffset G k = 0 := by simp [thresholdOffset, hmid]
    have hi : (thresholdIndex G k).val = 3 * (k / 2) + 1 := by
      simp [thresholdIndex, hmid.1, hmid.2]
    simp only [ho, eq_self, and_true, Fin.ext_iff, hi]
    rcases j with ⟨g, e, a⟩ | ⟨r, a⟩
    · simp only [groupedDegreeIndex, groupedAssignedBlock, isSharedColumn]
      split_ifs <;> omega
    · simp only [groupedDegreeIndex, isSharedColumn, and_false]
      constructor
      · intro he
        have hk := hmid.1
        omega
      · exact False.elim
  · have ho : thresholdOffset G k ≠ 0 := by simp [thresholdOffset, hmid]
    simp only [ho, and_false]
    rcases j with ⟨g, e, a⟩ | ⟨r, a⟩
    · simp only [groupedAssignedBlock, isSharedColumn, false_iff]
      rintro ⟨hk, he⟩
      have hg : k = 2 * g.val := by simpa [he] using hk
      exact hmid ⟨by omega, by omega⟩
    · simp [isSharedColumn]

private theorem interval_iff_block (d : Fin (3 * G + 9) → ℕ) (hd : StrictMono d)
    (j : GroupedLeadingCol G) (i : ℕ) :
    (∀ k ∈ Finset.Ico (min i (groupedAssignedBlock j)) (max i (groupedAssignedBlock j)),
      groupedThreshold d k = groupedColumnDegree d j) ↔
      i = groupedAssignedBlock j ∨ i = groupedAssignedBlock j + 1 ∧ isSharedColumn j := by
  let b := groupedAssignedBlock j
  change (∀ k ∈ Finset.Ico (min i b) (max i b),
    groupedThreshold d k = groupedColumnDegree d j) ↔ i = b ∨ i = b + 1 ∧ isSharedColumn j
  simp only [groupedThreshold_eq_columnDegree_iff d hd, ← show b = groupedAssignedBlock j from rfl,
    Finset.mem_Ico]
  constructor
  · intro hi
    by_cases hb : i = b
    · exact Or.inl hb
    have hbi : b < i := by
      by_contra! h
      exact hb (hi i (by omega)).1
    have hs := (hi b (by omega)).2
    have hlt : i ≤ b + 1 := by
      by_contra! h
      have := (hi (b + 1) (by omega)).1
      omega
    exact Or.inr ⟨by omega, hs⟩
  · rintro (rfl | ⟨rfl, hs⟩) k hk
    · omega
    · exact ⟨by omega, hs⟩

/-- The natural order of the plane row pairs, followed by the root rows. -/
def groupedEvalBlock : GroupedLeadingRow G → ℕ
  | .inl (g, p, _) => 2 * g.val + p.val
  | .inr (r, _) => 2 * G + r.val

/-- A plane row meets the two edges adjacent to it, and a root row its own edge only. -/
def groupedLeadingIncidence : GroupedLeadingRow G → GroupedLeadingCol G → Prop
  | .inl (g, p, _), .inl (g', e, _) => g' = g ∧ (e = p.castSucc ∨ e = p.succ)
  | .inr (r, _), .inr (r', _) => r' = r
  | _, _ => False

/-- The interval between a row and the assigned block has the column degree
at every threshold exactly for the incidences of the leading block matrix. -/
theorem groupedThreshold_interval_iff (d : Fin (3 * G + 9) → ℕ) (hd : StrictMono d)
    (i : GroupedLeadingRow G) (j : GroupedLeadingCol G) :
    (∀ k ∈ Finset.Ico (min (groupedEvalBlock i) (groupedAssignedBlock j))
      (max (groupedEvalBlock i) (groupedAssignedBlock j)),
      groupedThreshold d k = groupedColumnDegree d j) ↔ groupedLeadingIncidence i j := by
  rw [interval_iff_block d hd]
  rcases i with ⟨g, p, a⟩ | ⟨r, a⟩ <;> rcases j with ⟨g', e, b⟩ | ⟨r', b⟩
  · simp only [groupedEvalBlock, groupedAssignedBlock, groupedLeadingIncidence,
      isSharedColumn, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · simp [groupedEvalBlock, groupedAssignedBlock, groupedLeadingIncidence, isSharedColumn]
    omega
  · fin_cases e <;>
      simp [groupedEvalBlock, groupedAssignedBlock, groupedLeadingIncidence, isSharedColumn] <;> omega
  · simp [groupedEvalBlock, groupedAssignedBlock, groupedLeadingIncidence, isSharedColumn, Fin.ext_iff,
      eq_comm]

end IdealGeneration.TripleNormal
