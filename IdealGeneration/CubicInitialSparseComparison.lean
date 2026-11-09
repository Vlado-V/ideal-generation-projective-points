module

public import IdealGeneration.CubicInitialMiddleData
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Compute each middle row from just its nonempty predecessor blocks. -/

namespace IdealGeneration.CubicInitial
open ConeMonomialChart CertifiedRank


private def group {n b : ℕ} {V : Type*}
    (index : Fin b → Fin n) (entry : V → Fin b → ℕ) (pred : Option V) :
    SparseRow n ℕ :=
  match pred with
  | none => []
  | some a => (List.ofFn fun j => (index j, entry a j)).filter fun e => e.2 != 0

/-- The same row in the same column order, skipping blocks with no predecessor. -/
def rawMiddleRowSparse (i : Fin 650) : SparseRow 542 ℕ :=
  (List.ofFn fun j : Fin 12 =>
    group (fun k => columnChart (.inl (j, k))) normalKernelEntry (normalLookup i j)).flatten ++
  (List.ofFn fun j : Fin 2 =>
    group (fun k => columnChart (.inr (j, k))) traceKernelEntry (traceLookup i j)).flatten

private theorem filter_ofFn_blocks {a b n : ℕ} {V : Type*}
    (index : Fin a → Fin b → Fin n) (entry : V → Fin b → ℕ) (pred : Fin a → Option V)
    (f : Fin (a * b) → Fin n × ℕ)
    (hf : ∀ i j, f (finProdFinEquiv (i, j)) =
      (index i j, ((pred i).map fun v => entry v j).getD 0)) :
    (List.ofFn f).filter (fun e => e.2 != 0) =
      (List.ofFn fun i => group (index i) entry (pred i)).flatten := by
  rw [List.ofFn_mul, List.filter_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  have hi : (List.ofFn fun j : Fin b => f ⟨i.val * b + j.val, by
      have := i.isLt
      have := j.isLt
      exact (Nat.add_lt_add_left j.isLt _).trans_le (by nlinarith)⟩) =
      List.ofFn (fun j => (index i j, ((pred i).map fun v => entry v j).getD 0)) := by
    apply congrArg List.ofFn
    funext j
    rw [← hf]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [Function.comp_apply]
  rw [hi]
  cases pred i with
  | none =>
    simp [group, List.filter_eq_nil_iff, List.mem_ofFn]
  | some v => rfl

theorem rawMiddleRow_eq_sparse (i : Fin 650) : rawMiddleRow i = rawMiddleRowSparse i := by
  unfold rawMiddleRow rawMiddleRowSparse
  let f : Fin (12 * 36 + 2 * 55) → Fin 542 × ℕ := fun j => (j, rawMiddleEntry i j)
  change (List.ofFn f).filter (fun e => e.2 != 0) = _
  rw [List.ofFn_add (n := 12 * 36) (m := 2 * 55), List.filter_append]
  congr 1
  · apply filter_ofFn_blocks _ normalKernelEntry (normalLookup i)
    intro j k
    have h : (finProdFinEquiv (j, k)).castAdd (2 * 55) = columnChart (.inl (j, k)) := by
      rfl
    change f ((finProdFinEquiv (j, k)).castAdd (2 * 55)) = _
    rw [h]
    simp only [f, rawMiddleEntry, Equiv.symm_apply_apply, Sum.elim_inl]
  · apply filter_ofFn_blocks _ traceKernelEntry (traceLookup i)
    intro j k
    have h : (finProdFinEquiv (j, k)).natAdd (12 * 36) = columnChart (.inr (j, k)) := by
      rfl
    rw [h]
    simp only [f, rawMiddleEntry, Equiv.symm_apply_apply, Sum.elim_inr]

end IdealGeneration.CubicInitial
