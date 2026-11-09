module

public import IdealGeneration.CubicB4RankTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The B.22 probe rows in the indexing of the assembled B.4 evaluation. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B22

variable {K : Type*} [Field K] {m r : ℕ}
variable (Q : Parameters K (m + 2))
variable (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)

private theorem rev_ne_self_two : ∀ b : Fin 2, b.rev ≠ b := by decide +kernel

private theorem eq_rev_of_ne_two : ∀ b d : Fin 2, b ≠ d → b = d.rev := by decide +kernel

private def finalIndex (r : ℕ) (j : Fin 4) : Fin (r + 2) × Fin 2 :=
  (Fin.natAdd r ((@finProdFinEquiv 2 2).symm j).1, ((@finProdFinEquiv 2 2).symm j).2)

private def fixedIndexTo : HigherColumn Q → NewIncidence Q ⊕ (Fin (r + 2) × Fin 2)
  | .inl (p, b) => if b = p.val.2 then .inl p else
    match pairing.symm p with
    | .inl (i, k) => .inr (Fin.castAdd 2 i, k)
    | .inr _ => .inr (finalIndex r 0)
  | .inr q => .inr (finalIndex r q.succ)

private def fixedIndexFrom : NewIncidence Q ⊕ (Fin (r + 2) × Fin 2) → HigherColumn Q
  | .inl p => .inl (p, p.val.2)
  | .inr (i, k) => Fin.addCases
      (fun j => let p := pairedIncidence Q pairing j k; .inl (p, p.val.2.rev))
      (fun j => finalHigherLabel Q pairing (finProdFinEquiv (j, k))) i

@[simp] private theorem fixedIndexFrom_final (j : Fin 4) :
    fixedIndexFrom Q pairing (.inr (finalIndex r j)) = finalHigherLabel Q pairing j := by
  simp [fixedIndexFrom, finalIndex]

@[simp] private theorem finalHigherLabel_zero :
    finalHigherLabel Q pairing 0 =
      .inl (unpairedIncidence Q pairing, (unpairedIncidence Q pairing).val.2.rev) := rfl

@[simp] private theorem finalHigherLabel_succ (q : Fin 3) :
    finalHigherLabel Q pairing q.succ = .inr q := by
  fin_cases q <;> rfl

/-- Reindex the higher columns by their corresponding edge and fixed free rows. -/
def fixedIndex : HigherColumn Q ≃ NewIncidence Q ⊕ (Fin (r + 2) × Fin 2) where
  toFun := fixedIndexTo Q pairing
  invFun := fixedIndexFrom Q pairing
  left_inv a := by
    rcases a with ⟨p, b⟩ | q
    · by_cases h : b = p.val.2
      · simp [fixedIndexTo, fixedIndexFrom, h]
      · obtain hb := eq_rev_of_ne_two b p.val.2 h
        cases hp : pairing.symm p with
        | inl ik =>
          rcases ik with ⟨i, k⟩
          have he : pairedIncidence Q pairing i k = p := by
            rw [pairedIncidence, ← hp, Equiv.apply_symm_apply]
          simp [fixedIndexTo, fixedIndexFrom, hp, he, hb, rev_ne_self_two]
        | inr u =>
          cases u
          have he : unpairedIncidence Q pairing = p := by
            rw [unpairedIncidence, ← hp, Equiv.apply_symm_apply]
          simp [fixedIndexTo, hp, he, hb, rev_ne_self_two]
    · simp [fixedIndexTo]
  right_inv a := by
    rcases a with p | ⟨i, k⟩
    · simp [fixedIndexTo, fixedIndexFrom]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [fixedIndexTo, fixedIndexFrom, pairedIncidence, rev_ne_self_two]
      · let c : Fin 4 := finProdFinEquiv (j, k)
        have hc : finalIndex r c = (Fin.natAdd r j, k) := by simp [finalIndex, c]
        rw [← hc, fixedIndexFrom_final]
        refine Fin.cases ?_ (fun q => ?_) c
        · simp [fixedIndexTo, unpairedIncidence, rev_ne_self_two]
        · simp [fixedIndexTo]

/-- The far probes are the paired probes followed by the two final C.4 probes. -/
def farPoint (x : Fin 2 → Fin 3 → K) : Fin (r + 2) → Fin (m + 2) → K :=
  Fin.addCases
    (fun i => pairProbe (pairedIncidence Q pairing i 0).val.1
      (pairedIncidence Q pairing i 1).val.1)
    (fun j => finalProbe (unpairedIncidence Q pairing).val.1 (x j))

@[simp] theorem farPoint_pair (x : Fin 2 → Fin 3 → K) (i : Fin r) :
    farPoint Q pairing x (Fin.castAdd 2 i) =
      pairProbe (pairedIncidence Q pairing i 0).val.1
        (pairedIncidence Q pairing i 1).val.1 := Fin.addCases_left i

@[simp] theorem farPoint_final (x : Fin 2 → Fin 3 → K) (j : Fin 2) :
    farPoint Q pairing x (Fin.natAdd r j) =
      finalProbe (unpairedIncidence Q pairing).val.1 (x j) := Fin.addCases_right j

/-- The indexed B.4 fixed rows are exactly the rows of the higher certificate. -/
theorem fixedEnumeration_eq_fixedProbeRow (x : Fin 2 → Fin 3 → K) (a : HigherColumn Q) :
    B4.fixedEnumeration Q (farPoint Q pairing x) (fixedIndex Q pairing) a =
      fixedProbeRow Q pairing x a := by
  rcases a with ⟨p, b⟩ | q
  · by_cases h : b = p.val.2
    · simp [B4.fixedEnumeration, fixedIndex, fixedIndexTo, fixedProbeRow, h]
    · cases hp : pairing.symm p with
      | inl ik =>
        rcases ik with ⟨i, k⟩
        simp [B4.fixedEnumeration, fixedIndex, fixedIndexTo, fixedProbeRow, h, hp]
      | inr u =>
        simp [B4.fixedEnumeration, fixedIndex, fixedIndexTo, fixedProbeRow, h, hp, finalIndex]
        rfl
  · simp [B4.fixedEnumeration, fixedIndex, fixedIndexTo, fixedProbeRow, finalIndex]
    rfl

/-- The assembled B.4 fixed higher block has the entries of the B.22 matrix. -/
theorem fixedHigherMatrix_eq_actual {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (x : Fin 2 → Fin 3 → K) :
    fixedHigherMatrix Q pairing x =
      Matrix.of (fun i j =>
        B4.fixedValue Q free h₂ h₆
          (B4.fixedEnumeration Q (farPoint Q pairing x) (fixedIndex Q pairing) i)
          (highParameter Q j)) := by
  ext i j
  rw [fixedHigherMatrix, Matrix.of_apply, Matrix.of_apply, fixedEnumeration_eq_fixedProbeRow,
    higherFixedValue_parameterPhi Q free h₂ h₆]
  rfl

end IdealGeneration.CubicSupported.B22
