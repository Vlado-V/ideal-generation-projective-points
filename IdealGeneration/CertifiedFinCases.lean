module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace CertifiedRank

/-- Split a finite family of concrete checks without enumerating the full type. -/
theorem forall_fin_add {a b : ℕ} {P : Fin (a + b) → Prop}
    (h₁ : ∀ i : Fin a, P (i.castAdd b))
    (h₂ : ∀ j : Fin b, P (j.natAdd a)) : ∀ i, P i :=
  Fin.addCases h₁ h₂

theorem forall_fin_one {P : Fin 1 → Prop} (h : P 0) : ∀ i, P i := by
  intro i
  rw [Subsingleton.elim i 0]
  exact h


/-- A literal table of checked propositions covers every finite index. -/
theorem forall_fin_of_rows {n : ℕ} [NeZero n] {P : Fin n → Prop}
    (h : List.Forall (fun j => P (Fin.ofNat n j)) (List.range n)) : ∀ i, P i := by
  intro i
  have hi : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hi ▸ (List.forall_iff_forall_mem.mp h i.val (List.mem_range.mpr i.isLt))

end CertifiedRank
