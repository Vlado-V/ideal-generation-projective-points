module

public import IdealGeneration.TwoNormalMarkedParameters
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Intersecting the marked opens while fixing the off-slice points

First specialize a joint open at the witness values of the other groups.
After choosing the off-slice points on this specialized open, the original
joint open still has a witness in the remaining variables. The residual
pair interpolation can then be imposed for that fixed ideal.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

private theorem eval_substitution {ι κ : Type*} (a : κ → K)
    (f : ι → MvPolynomial κ K) (P : MvPolynomial ι K) :
    eval a (aeval f P) = eval (fun i => eval a (f i)) P := by
  have h : (eval a).comp (aeval f).toRingHom = eval (fun i => eval a (f i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  exact congrArg (fun F : MvPolynomial ι K →+* K => F P) h

private theorem eval_specialize_right {ι κ : Type*} (x : ι → K) (y : κ → K)
    (D : MvPolynomial (ι ⊕ κ) K) :
    eval x (aeval (Sum.elim X (fun j => C (y j))) D) = eval (Sum.elim x y) D := by
  rw [eval_substitution]
  have h : (fun i : ι ⊕ κ => eval x (Sum.elim X (fun j => C (y j)) i)) = Sum.elim x y := by
    funext i
    cases i <;> simp
  rw [h]

private theorem eval_specialize_left {ι κ : Type*} (x : ι → K) (y : κ → K)
    (D : MvPolynomial (ι ⊕ κ) K) :
    eval y (aeval (Sum.elim (fun i => C (x i)) X) D) = eval (Sum.elim x y) D := by
  rw [eval_substitution]
  have h : (fun i : ι ⊕ κ => eval y (Sum.elim (fun i => C (x i)) X i)) = Sum.elim x y := by
    funext i
    cases i <;> simp
  rw [h]

/-- A joint nonempty principal open can be met along with a nonempty open
on the first group and a nonempty open on each good first-group fiber. -/
theorem exists_on_principal_open_with_fiber_open [Infinite K] {ι κ : Type*}
    (D : MvPolynomial (ι ⊕ κ) K) (hD : ∃ c : (ι ⊕ κ) → K, eval c D ≠ 0)
    (P : MvPolynomial ι K) (hP : ∃ x : ι → K, eval x P ≠ 0)
    (R : (ι → K) → (κ → K) → Prop)
    (hR : ∀ x : ι → K, eval x P ≠ 0 → ∃ Q : MvPolynomial κ K,
      (∃ y : κ → K, eval y Q ≠ 0) ∧ ∀ y, eval y Q ≠ 0 → R x y) :
    ∃ (x : ι → K) (y : κ → K), eval (Sum.elim x y) D ≠ 0 ∧ eval x P ≠ 0 ∧ R x y := by
  obtain ⟨c₀, hc₀⟩ := hD
  let x₀ : ι → K := c₀ ∘ Sum.inl
  let y₀ : κ → K := c₀ ∘ Sum.inr
  have hc : Sum.elim x₀ y₀ = c₀ := by
    funext i
    cases i <;> rfl
  let D₁ : MvPolynomial ι K := aeval (Sum.elim X (fun j => C (y₀ j))) D
  have hD₁ : eval x₀ D₁ ≠ 0 := by
    change eval x₀ (aeval (Sum.elim X (fun j => C (y₀ j))) D) ≠ 0
    rw [eval_specialize_right, hc]
    exact hc₀
  obtain ⟨x, hxD, hxP⟩ := principal_opens_meet D₁ P ⟨x₀, hD₁⟩ hP
  let D₂ : MvPolynomial κ K := aeval (Sum.elim (fun i => C (x i)) X) D
  have hD₂ : eval y₀ D₂ ≠ 0 := by
    change eval y₀ (aeval (Sum.elim (fun i => C (x i)) X) D) ≠ 0
    rw [eval_specialize_left, ← eval_specialize_right]
    exact hxD
  obtain ⟨Q, hQ, hgood⟩ := hR x hxP
  obtain ⟨y, hyD, hyQ⟩ := principal_opens_meet D₂ Q ⟨y₀, hD₂⟩ hQ
  refine ⟨x, y, ?_, hxP, hgood y hyQ⟩
  rw [← eval_specialize_left]
  exact hyD

/-- All marked parameters except those of the off-slice group. -/
abbrev MarkedRestIndex (n b l : ℕ) :=
  (Fin b × Fin (n + 1)) ⊕ ((Fin b × Fin (n + 1)) ⊕ (Fin l × Fin n))

/-- Separate the off-slice parameters from the remaining marked parameters. -/
def markedOffSliceSplit (n b q l : ℕ) :
    MarkedIndex n b q l ≃ (Fin q × Fin (n + 2)) ⊕ MarkedRestIndex n b l where
  toFun
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inl i
    | Sum.inr (Sum.inr (Sum.inr i)) => Sum.inr (Sum.inr (Sum.inr i))
  invFun
    | Sum.inl i => Sum.inr (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr (Sum.inr i)) => Sum.inr (Sum.inr (Sum.inr i))
  left_inv i := by rcases i with i | i | i | i <;> rfl
  right_inv i := by rcases i with i | i | i | i <;> rfl

/-- Pair interpolation for a fixed good off-slice ideal can be imposed on
the same marked configuration as all independently witnessed joint opens. -/
theorem exists_marked_on_joint_and_pair_opens [Infinite K] {n b q l : ℕ}
    (D : MvPolynomial (MarkedIndex n b q l) K)
    (hD : ∃ c : MarkedParameters K n b q l, eval c D ≠ 0)
    (P : MvPolynomial (Fin q × Fin (n + 2)) K)
    (hP : ∃ x : PointCoordinates K (n + 2) q, eval x P ≠ 0)
    (R : PointCoordinates K (n + 2) q → PointCoordinates K (n + 1) b →
      PointCoordinates K (n + 1) b → Prop)
    (hR : ∀ x : PointCoordinates K (n + 2) q, eval x P ≠ 0 →
      ∃ Q : MvPolynomial ((Fin b × Fin (n + 1)) ⊕ (Fin b × Fin (n + 1))) K,
        (∃ c, eval c Q ≠ 0) ∧ ∀ c, eval c Q ≠ 0 → R x (c ∘ Sum.inl) (c ∘ Sum.inr)) :
    ∃ c : MarkedParameters K n b q l, eval c D ≠ 0 ∧ eval (markedOffSlice c) P ≠ 0 ∧
      R (markedOffSlice c) (markedSliceA c) (markedSliceB c) := by
  let e := markedOffSliceSplit n b q l
  let D' := rename e D
  have hD' : ∃ c : ((Fin q × Fin (n + 2)) ⊕ MarkedRestIndex n b l) → K,
      eval c D' ≠ 0 := (principalOpen_pullback e.toEmbedding D hD).1
  let R' : (Fin q × Fin (n + 2) → K) → (MarkedRestIndex n b l → K) → Prop :=
    fun x y => R x (y ∘ Sum.inl) (fun ij => y (Sum.inr (Sum.inl ij)))
  have hR' : ∀ x : PointCoordinates K (n + 2) q, eval x P ≠ 0 →
      ∃ Q : MvPolynomial (MarkedRestIndex n b l) K,
        (∃ y, eval y Q ≠ 0) ∧ ∀ y, eval y Q ≠ 0 → R' x y := by
    intro x hx
    obtain ⟨Q, hQ, hgood⟩ := hR x hx
    let j : ((Fin b × Fin (n + 1)) ⊕ (Fin b × Fin (n + 1))) ↪ MarkedRestIndex n b l :=
      Function.Embedding.sumMap (Function.Embedding.refl _) Function.Embedding.inl
    obtain ⟨hnonempty, hpull⟩ := principalOpen_pullback j Q hQ
    exact ⟨rename j Q, hnonempty, fun y hy => hgood (y ∘ j) (hpull y hy)⟩
  obtain ⟨x, y, hxy, hx, hgood⟩ := exists_on_principal_open_with_fiber_open
    D' hD' P hP R' hR'
  refine ⟨Sum.elim x y ∘ e, ?_, hx, hgood⟩
  simpa only [D', eval_rename] using hxy

end IdealGeneration.TwoNormalIntegral
