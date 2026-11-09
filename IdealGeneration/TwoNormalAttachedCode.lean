module

public import IdealGeneration.AttachedTrace
public import IdealGeneration.TwoNormalCode
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Simultaneous interpolation at attached and free labels

Once the attached rows are onto, each full-size subset can be completed by
its own free labels. A finite product of principal-open conditions gives
unisolvence for every subset on the same free configuration.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial AttachedTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n d p q : ℕ}
  (U : Submodule K (Forms K (n + 1) d))

local instance attachedSpaceGroup : AddCommGroup U := Module.addCommMonoidToAddCommGroup K

/-- Scalar evaluation on the union of the attached and free point labels. -/
def attachedFreeEvaluation (a : PointCoordinates K n p) (b : PointCoordinates K n q) :
    U →ₗ[K] ((Fin p ⊕ Fin q) → K) :=
  LinearMap.pi (Sum.elim
    (fun i => (LinearMap.proj i).comp (subspaceEvaluation U a))
    (fun i => (LinearMap.proj i).comp (subspaceEvaluation U b)))

/-- Select any subset of the union of the attached and free labels. -/
def selectedAttachedFreeEvaluation (a : PointCoordinates K n p)
    (b : PointCoordinates K n q) (s : Finset (Fin p ⊕ Fin q)) : U →ₗ[K] (s → K) :=
  selectedScalarEvaluation (fun i => (LinearMap.proj i).comp (attachedFreeEvaluation U a b)) s

/-- A full-size subset imposes independent conditions on a nonempty principal
open in the free point coordinates. -/
theorem generic_selectedAttachedFreeEvaluation [Infinite K]
    (a : PointCoordinates K n p) (ha : Function.Surjective (subspaceEvaluation U a))
    (s : Finset (Fin p ⊕ Fin q)) (hs : s.card = finrank K U) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ b : PointCoordinates K n q, eval b P ≠ 0) ∧
      ∀ b, eval b P ≠ 0 → Function.Injective (selectedAttachedFreeEvaluation U a b s) := by
  classical
  let eA : Fin s.toLeft.card ≃ s.toLeft := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let eB : Fin s.toRight.card ≃ s.toRight := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let E : U →ₗ[K] (Fin s.toLeft.card → K) := LinearMap.pi
    (fun i => (LinearMap.proj (eA i).val).comp (subspaceEvaluation U a))
  have hE : Function.Surjective E := by
    intro w
    let v : Fin p → K := fun i => if hi : i ∈ s.toLeft then w (eA.symm ⟨i, hi⟩) else 0
    obtain ⟨f, hf⟩ := ha v
    refine ⟨f, ?_⟩
    funext i
    change subspaceEvaluation U a f (eA i).val = w i
    rw [congrFun hf (eA i).val]
    dsimp [v]
    rw [ite_eq_left (eA i).property]
    exact congrArg w (eA.symm_apply_apply i)
  have hcard : s.toLeft.card + s.toRight.card = finrank K U :=
    (Finset.card_toLeft_add_card_toRight (u := s)).trans hs
  obtain ⟨P, hP, hgood⟩ := generic_evaluation_completion_of_surjective U E hE s.toRight.card
    (by omega)
  let j : Fin s.toRight.card × Fin n → Fin q × Fin n := fun ij => ((eB ij.1).val, ij.2)
  have hj : Function.Injective j := by
    intro x y hxy
    have h₁ : (eB x.1).val = (eB y.1).val := congrArg Prod.fst hxy
    have h₂ : x.2 = y.2 := congrArg (fun z : Fin q × Fin n => z.2) hxy
    exact Prod.ext (eB.injective (Subtype.ext h₁)) h₂
  have hPne : P ≠ 0 := by
    obtain ⟨b, hb⟩ := hP
    intro hzero
    simp [hzero] at hb
  have hrename : rename j P ≠ 0 := by
    intro hzero
    exact hPne ((rename_eq_zero_iff_of_injective P hj).mp hzero)
  have hnonempty : ∃ b : PointCoordinates K n q, eval b (rename j P) ≠ 0 := by
    by_contra! h
    exact hrename (MvPolynomial.funext h)
  refine ⟨rename j P, hnonempty, ?_⟩
  intro b hb f g hfg
  have hb' : eval (b ∘ j) P ≠ 0 := by simpa only [eval_rename] using hb
  apply hgood (b ∘ j) hb'
  apply Prod.ext
  · funext i
    have hi : Sum.inl (eA i).val ∈ s := Finset.mem_toLeft.mp (eA i).property
    exact congrFun hfg ⟨Sum.inl (eA i).val, hi⟩
  · funext i
    have hi : Sum.inr (eB i).val ∈ s := Finset.mem_toRight.mp (eB i).property
    exact congrFun hfg ⟨Sum.inr (eB i).val, hi⟩

/-- All full-size subsets are unisolvent on the same nonempty free-point open. -/
theorem generic_attachedFree_unisolvent [Infinite K]
    (a : PointCoordinates K n p) (ha : Function.Surjective (subspaceEvaluation U a))
    (q : ℕ) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ b : PointCoordinates K n q, eval b P ≠ 0) ∧
      ∀ b, eval b P ≠ 0 → ∀ s : Finset (Fin p ⊕ Fin q), s.card = finrank K U →
        Function.Injective (selectedAttachedFreeEvaluation U a b s) := by
  classical
  let J := {s : Finset (Fin p ⊕ Fin q) // s.card = finrank K U}
  have hJ : ∀ j : J, ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ b : PointCoordinates K n q, eval b P ≠ 0) ∧
      ∀ b, eval b P ≠ 0 → Function.Injective (selectedAttachedFreeEvaluation U a b j.val) :=
    fun j => generic_selectedAttachedFreeEvaluation U a ha j.val j.property
  choose P hP hgood using hJ
  have hne : ∀ j, P j ≠ 0 := by
    intro j hzero
    obtain ⟨b, hb⟩ := hP j
    simp [hzero] at hb
  obtain ⟨b₀, hb₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ j, P j, ⟨b₀, ?_⟩, ?_⟩
  · rw [map_prod, Finset.prod_ne_zero_iff]
    exact fun j _ => hb₀ j
  · intro b hb s hs
    rw [map_prod, Finset.prod_ne_zero_iff] at hb
    exact hgood ⟨s, hs⟩ b (hb ⟨s, hs⟩ (Finset.mem_univ _))

/-- The attached/free quotient has the uniform coordinate-class independence
required by the two-normal first response. -/
theorem generic_attachedFree_code [Infinite K]
    (a : PointCoordinates K n p) (ha : Function.Surjective (subspaceEvaluation U a))
    (q : ℕ) (hcount : finrank K U ≤ p + q) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ b : PointCoordinates K n q, eval b P ≠ 0) ∧
      ∀ b, eval b P ≠ 0 → Function.Injective (attachedFreeEvaluation U a b) ∧
        ∀ (r : ℕ) (f : Fin r ↪ (Fin p ⊕ Fin q)),
          r ≤ finrank K (((Fin p ⊕ Fin q) → K) ⧸ (attachedFreeEvaluation U a b).range) →
          LinearIndependent K (coordinateClass (attachedFreeEvaluation U a b) ∘ f) := by
  classical
  obtain ⟨P, hP, hgood⟩ := generic_attachedFree_unisolvent U a ha q
  refine ⟨P, hP, fun b hb => ?_⟩
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (show finrank K U ≤ (Finset.univ : Finset (Fin p ⊕ Fin q)).card by simpa using hcount)
  have hinj : Function.Injective (attachedFreeEvaluation U a b) := by
    intro f g hfg
    apply hgood b hb s hs
    funext i
    exact congrFun hfg i.val
  exact ⟨hinj, coordinateClasses_independent _ hinj (hgood b hb)⟩

end IdealGeneration.TwoNormalIntegral
