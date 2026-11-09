module

public import IdealGeneration.CubicB7ChangedBasis
public import IdealGeneration.CubicB4RankTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual supported cubic pair step from its two nonsingular diagonal blocks. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B4

open B5 B22 Module

variable {K : Type*} [Field K] [Infinite K] {m f n l p : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)}
variable (old : Fin f → Fin m → K)
variable (nearPoint : Fin n → Fin m → K) (nearWeight : Fin n → Fin 2 → K)
variable (farPoint : Fin l → Fin (m + 2) → K) (base : Fin p → Fin (m + 2) → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (nearIndex : A ≃ Fin n × Fin 2)
variable (fixedIndex : B ≃ NewIncidence Q ⊕ (Fin l × Fin 2))
variable (low : A ≃ B7Column m) (high : B ≃ HigherColumn Q)

local notation "near" => nearEnumeration nearPoint nearWeight nearIndex
local notation "fixed" => fixedEnumeration Q farPoint fixedIndex

/-- A nonzero motion gives the genuine enlarged middle map. The source basis is
the actual lower and higher family, including the prescribed star changes. -/
theorem exists_supported_pair_step (h : Compatible P Q)
    (hP : ∀ e, P.single e = B5.single e) (hQ : ∀ e, Q.single e = B5.single e)
    (hpair : Q.single (newPairEdge m) = false)
    (hold : Function.Injective ((P.toConeConfiguration old).middleMultiplication 3))
    (h11 : (Matrix.of (fun i j => b7Value (actualB7Data Q) (near i).point
      (near i).weight (near i).component (low j)) : Matrix A A K).det ≠ 0)
    (h22 : (Matrix.of (fun i j => fixedValue Q base h₂ h₆ (fixed i)
      (highParameter Q (high j))) : Matrix B B K).det ≠ 0) :
    ∃ eps : K, eps ≠ 0 ∧ Function.Injective
      ((Q.toConeConfiguration (enlargedFree old nearPoint nearWeight farPoint eps)).middleMultiplication 3) := by
  have hold' := (P.middleMultiplication_injective_iff_markedEvaluation old h₂ h₆).mp hold
  let b : Basis (A ⊕ B) K h.restrictParameters.ker :=
    (h.actualNewBasis hP hQ old h₂ h₆ hpair hold').reindex (Equiv.sumCongr low high).symm
  have hlow (j : A) : (b (.inl j)).val = b7Parameter Q hQ (low j) := by
    simp [b, Basis.reindex_apply, Compatible.actualNewColumn]
  have hhigh (j : B) : (b (.inr j)).val = highParameter Q (high j) := by
    simp [b, Basis.reindex_apply, Compatible.actualNewColumn]
  obtain ⟨eps, hne, hinj⟩ :=
    exists_markedEvaluation_injective_of_b4_blocks old nearPoint nearWeight farPoint h nearIndex
      fixedIndex h₂ h₆ hQ base low high b hlow hhigh hold' h11 h22
  exact ⟨eps, hne, (Q.middleMultiplication_injective_iff_markedEvaluation _ h₂ h₆).mpr hinj⟩

end IdealGeneration.CubicSupported.B4
