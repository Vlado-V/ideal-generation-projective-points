module

public import IdealGeneration.MainStatement
public import IdealGeneration.Binary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The complete projective-line case of the target statement. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The target assertion in projective dimension one, at its initial degree. -/
theorem idealGenerationAt_projectiveLine (d : ℕ) : IdealGenerationAt K 1 d d := by
  obtain ⟨E, hE, hgood⟩ :=
    generic_pointHilbertFunction (K := K) (n := 1) (by omega) d
  refine ⟨E, hE, fun a ha => ?_⟩
  obtain ⟨hdistinct, hpost⟩ := hgood a ha
  refine ⟨hdistinct, hpost, Or.inr ?_⟩
  apply binary_pointMultiplication_surjective_of_postulation a
  · have hd0 : (1 + d).choose d = d + 1 := by
      rw [Nat.add_comm, Nat.choose_succ_self_right]
    simpa only [hd0, min_eq_right (Nat.le_succ d)] using hpost d
  · have hd1 : (1 + (d + 1)).choose (d + 1) = d + 2 := by
      rw [Nat.add_comm 1 (d + 1), Nat.choose_succ_self_right]
    simpa only [hd1, min_eq_right (by omega : d ≤ d + 2)] using hpost (d + 1)

/-- All point counts in the paper's initial-degree range on the projective line. -/
theorem idealGenerationAt_projectiveLine_of_cell (d p : ℕ) (hd : 2 ≤ d)
    (hlower : (1 + d - 1).choose (d - 1) ≤ p)
    (hupper : p < (1 + d).choose d) : IdealGenerationAt K 1 d p := by
  have hdpos : 1 ≤ d := by omega
  have hl : d ≤ p := by
    have he : (1 + d - 1).choose (d - 1) = d := by
      rw [show 1 + d - 1 = d by omega]
      simpa only [Nat.sub_add_cancel hdpos] using Nat.choose_succ_self_right (d - 1)
    simpa only [he] using hlower
  have hu : p < d + 1 := by
    simpa only [Nat.add_comm 1 d, Nat.choose_succ_self_right] using hupper
  have hp : p = d := by omega
  subst p
  exact idealGenerationAt_projectiveLine d

end IdealGeneration
