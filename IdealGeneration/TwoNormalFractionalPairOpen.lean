module

public import IdealGeneration.TwoNormalFractionalMarkedParameters
public import IdealGeneration.TwoNormalMarkedOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Residual pair interpolation on the fractional marked family -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial TwoNormalIntegral
set_option maxHeartbeats 900000

private def exchangeRight {A B C : Type*} : ((A ⊕ B) ⊕ C) ≃ ((A ⊕ C) ⊕ B) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr b
    | Sum.inr c => Sum.inl (Sum.inr c)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr c
    | Sum.inr b => Sum.inl (Sum.inr b)
  left_inv i := by rcases i with (i | i) | i <;> rfl
  right_inv i := by rcases i with (i | i) | i <;> rfl

private def singleRowEquiv (s : ℕ) : Fin s ≃ Fin 1 × Fin s where
  toFun j := (0, j)
  invFun := Prod.snd
  left_inv _ := rfl
  right_inv _ij := Prod.ext (Subsingleton.elim _ _) rfl

private def pointArrayJoin (q s : ℕ) :
    ((Fin q × Fin s) ⊕ Fin s) ≃ Fin (q + 1) × Fin s :=
  (Equiv.sumCongr (Equiv.refl _) (singleRowEquiv s)).trans
    ((Equiv.sumProdDistrib _ _ _).symm.trans
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl _)))

/-- Separate all off-slice coordinates from the independent slice and extra
trace coordinates. The last off-slice row is the free point. -/
def fractionalOffSliceSplit (n b q l : ℕ) :
    FractionalIndex n b q l ≃ (Fin (q + 1) × Fin (n + 2)) ⊕ MarkedRestIndex n b l :=
  (Equiv.sumCongr (markedOffSliceSplit n b q l) (Equiv.refl _)).trans
    (exchangeRight.trans (Equiv.sumCongr (pointArrayJoin q (n + 2)) (Equiv.refl _)))

variable {K : Type*} [Field K] {n b q l : ℕ}

omit [Field K] in
private theorem fractionalOffCoordinates_join
    (x : PointCoordinates K (n + 2) (q + 1))
    (y : MarkedRestIndex n b l → K) :
    fractionalOffCoordinates (Sum.elim x y ∘ fractionalOffSliceSplit n b q l) = x := by
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [fractionalOffCoordinates_last]
    change x (finSumFinEquiv (Sum.inr (0 : Fin 1)), j) = x (Fin.last q, j)
    simp only [finSumFinEquiv_apply_right]
    rfl
  · rw [fractionalOffCoordinates_castSucc]
    change x (finSumFinEquiv (Sum.inl i), j) = x (i.castSucc, j)
    simp only [finSumFinEquiv_apply_left]
    rfl

/-- On any nonempty joint open, one can impose a further nonempty off-slice
open and a nonempty slice-pair open for each good fixed off-slice ideal. -/
theorem exists_fractional_on_joint_and_pair_opens [Infinite K]
    (D : MvPolynomial (FractionalIndex n b q l) K)
    (hD : ∃ c : FractionalParameters K n b q l, eval c D ≠ 0)
    (P : MvPolynomial (Fin (q + 1) × Fin (n + 2)) K)
    (hP : ∃ x : PointCoordinates K (n + 2) (q + 1), eval x P ≠ 0)
    (R : PointCoordinates K (n + 2) (q + 1) → PointCoordinates K (n + 1) b →
      PointCoordinates K (n + 1) b → Prop)
    (hR : ∀ x : PointCoordinates K (n + 2) (q + 1), eval x P ≠ 0 →
      ∃ Q : MvPolynomial ((Fin b × Fin (n + 1)) ⊕ (Fin b × Fin (n + 1))) K,
        (∃ c, eval c Q ≠ 0) ∧ ∀ c, eval c Q ≠ 0 → R x (c ∘ Sum.inl) (c ∘ Sum.inr)) :
    ∃ c : FractionalParameters K n b q l, eval c D ≠ 0 ∧
      eval (fractionalOffCoordinates c) P ≠ 0 ∧
      R (fractionalOffCoordinates c) (markedSliceA (c ∘ Sum.inl)) (markedSliceB (c ∘ Sum.inl)) := by
  let e := fractionalOffSliceSplit n b q l
  let D' := rename e D
  have hD' : ∃ c : ((Fin (q + 1) × Fin (n + 2)) ⊕ MarkedRestIndex n b l) → K,
      eval c D' ≠ 0 := (principalOpen_pullback e.toEmbedding D hD).1
  let R' : (Fin (q + 1) × Fin (n + 2) → K) → (MarkedRestIndex n b l → K) → Prop :=
    fun x y => R x (y ∘ Sum.inl) (fun ij => y (Sum.inr (Sum.inl ij)))
  have hR' : ∀ x : PointCoordinates K (n + 2) (q + 1), eval x P ≠ 0 →
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
  let c := Sum.elim x y ∘ e
  have hcX : fractionalOffCoordinates c = x := fractionalOffCoordinates_join x y
  refine ⟨c, ?_, ?_, ?_⟩
  · simpa only [c, D', eval_rename] using hxy
  · rwa [hcX]
  · rw [hcX]
    exact hgood

end IdealGeneration.TwoNormalFractional
