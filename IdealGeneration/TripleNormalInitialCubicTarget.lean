module

public import IdealGeneration.TripleNormalInitialCubicSlots
public import IdealGeneration.TripleNormalInitialCubicLUData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Sparse rows for the actual selected cubic coefficients. Each multiplier
with a nonempty checked slot contributes one short coefficient block. -/

noncomputable section
namespace IdealGeneration.TripleNormalInitial
open CertifiedRank CubicLU Matrix
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

private def optionalBlocks {a b n : ℕ} (idx : Fin a × Fin b → Fin n)
    (values : Fin a → Option (Fin b → ℕ)) : SparseRow n ℕ :=
  (List.ofFn fun i => match values i with
    | none => []
    | some f => List.ofFn (fun j => (idx (i, j), f j))).flatten

private theorem rowValue_flatten {n : ℕ} (rs : List (SparseRow n ℕ)) (j : Fin n) :
    rowValue rs.flatten j = (rs.map (fun r => rowValue r j)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.flatten_cons, rowValue_append, List.map_cons, List.sum_cons, ih]

private theorem rowValue_optionalBlocks {a b n : ℕ} (idx : Fin a × Fin b → Fin n)
    (values : Fin a → Option (Fin b → ℕ)) (j : Fin n) :
    rowValue (optionalBlocks idx values) j =
      ∑ i, ∑ k, if idx (i, k) = j then (values i).elim 0 (fun f => f k) else 0 := by
  rw [optionalBlocks, rowValue_flatten, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : values i with
  | none => simp [h, rowValue]
  | some f => simp [h, rowValue, List.map_ofFn, List.sum_ofFn]

private theorem rowValue_optionalBlocks_at {a b n : ℕ} (idx : Fin a × Fin b → Fin n)
    (hi : Function.Injective idx) (values : Fin a → Option (Fin b → ℕ))
    (i : Fin a) (j : Fin b) :
    rowValue (optionalBlocks idx values) (idx (i, j)) = (values i).elim 0 (fun f => f j) := by
  rw [rowValue_optionalBlocks]
  simp only [hi.eq_iff, Prod.mk.injEq]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem rowValue_optionalBlocks_zero {a b n : ℕ} (idx : Fin a × Fin b → Fin n)
    (values : Fin a → Option (Fin b → ℕ)) (j : Fin n) (h : ∀ x, idx x ≠ j) :
    rowValue (optionalBlocks idx values) j = 0 := by
  simp [rowValue_optionalBlocks, h]

/-- The packed checker uses the LU column permutation of the paper order. -/
def packedColumnOrder : CubicColumn ≃ Fin 288 :=
  paperColumnOrder.trans columnEquiv.symm

def targetValue (i j : Fin 288) : ℕ :=
  (slotMiddleMod (rowPermutation i) (packedColumnOrder.symm j)).val

private def normalValues (i : Fin 288) (j : Fin 15) : Option (Fin 14 → ℕ) :=
  (normalSlot (rowPermutation i) j).map (fun a b => (normalKernelMod a b).val)

private def traceValues (i : Fin 288) (j : Fin 3) : Option (Fin 26 → ℕ) :=
  (traceSlot (rowPermutation i) j).map (fun a b => (traceKernelMod a b).val)

/-- A row has at most three nonempty normal blocks and one trace block. -/
def targetRows (i : Fin 288) : SparseRow 288 ℕ :=
  optionalBlocks (fun x => packedColumnOrder (.inl x)) (normalValues i) ++
    optionalBlocks (fun x => packedColumnOrder (.inr x)) (traceValues i)

@[simp] theorem targetRows_value (i j : Fin 288) : rowValue (targetRows i) j = targetValue i j := by
  obtain ⟨c, rfl⟩ := packedColumnOrder.surjective j
  rw [targetValue, Equiv.symm_apply_apply, targetRows, rowValue_append]
  cases c with
  | inl x =>
      obtain ⟨v, b⟩ := x
      rw [rowValue_optionalBlocks_at (fun x : Fin 15 × Fin 14 => packedColumnOrder (.inl x))
          (packedColumnOrder.injective.comp Sum.inl_injective) (normalValues i) v b,
        rowValue_optionalBlocks_zero _ _ _ (fun _ h => Sum.inr_ne_inl (packedColumnOrder.injective h)),
        add_zero]
      unfold normalValues slotMiddleMod
      simp only [Sum.elim_inl]
      cases normalSlot (rowPermutation i) v <;> rfl
  | inr x =>
      obtain ⟨v, b⟩ := x
      rw [rowValue_optionalBlocks_zero _ _ _ (fun _ h => Sum.inl_ne_inr (packedColumnOrder.injective h)),
        rowValue_optionalBlocks_at (fun x : Fin 3 × Fin 26 => packedColumnOrder (.inr x))
          (packedColumnOrder.injective.comp Sum.inr_injective) (traceValues i) v b,
        zero_add]
      unfold traceValues slotMiddleMod
      simp only [Sum.elim_inr]
      cases traceSlot (rowPermutation i) v <;> rfl

theorem targetMatrix_eq : residueMatrix 1009 targetRows =
    orderedMiddleMod.submatrix rowPermutation columnPermutation := by
  ext i j
  change ((rowValue (targetRows i) j : ℕ) : ModField) = _
  rw [targetRows_value]
  change ((slotMiddleMod (rowPermutation i) (packedColumnOrder.symm j)).val : ModField) = _
  rw [ZMod.natCast_zmod_val, slotMiddleMod_eq_fast, orderedMiddleMod_eq_fast]
  rfl

end IdealGeneration.TripleNormalInitial
