module

public import IdealGeneration.TwoNormalMarkedParameters
public import IdealGeneration.TwoNormalSliceOpen
public import IdealGeneration.TwoNormalSlice

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Both slice codes on one marked parameter space

For each slice separately, fix its good residual configuration and let all
trace labels other than its attached projections vary freely. A polynomial
rank detector transfers these witnesses to a principal open in the common
marked parameters.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial AttachedTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d r : ℕ}

/-- Select and order a set of point coordinates by an embedding of labels. -/
def selectedTraceCoordinates {N : ℕ} (z : PointCoordinates K n N) (f : Fin r ↪ Fin N) :
    PointCoordinates K n r := fun ij => z (f ij.1, ij.2)

/-- A selected row agrees with its attached/free row after reindexing. -/
theorem selectedTrace_evaluation_row {p t N : ℕ}
    (U : Submodule K (Forms K (n + 1) d))
    (a : PointCoordinates K n p) (a' : PointCoordinates K n t)
    (z : PointCoordinates K n N) (e : (Fin p ⊕ Fin t) ≃ Fin N)
    (hc : ∀ label j, z (e label, j) = Sum.elim (fun i => a (i, j)) (fun i => a' (i, j)) label)
    (f : Fin r ↪ Fin N) (v : U) (i : Fin r) :
    attachedFreeEvaluation U a a' v (e.symm (f i)) =
      subspaceEvaluation U (selectedTraceCoordinates z f) v i := by
  have h (j : Fin n) := hc (e.symm (f i)) j
  simp only [Equiv.apply_symm_apply] at h
  generalize hj : e.symm (f i) = label at h ⊢
  rcases label with k | k
  · change eval (chartPoint K a k) v.val.val =
      eval (chartPoint K (selectedTraceCoordinates z f) i) v.val.val
    have hp : chartPoint K (selectedTraceCoordinates z f) i = chartPoint K a k := by
      unfold chartPoint
      rw [show (fun j => selectedTraceCoordinates z f (i, j)) = fun j => a (k, j) from funext h]
    rw [hp]
  · change eval (chartPoint K a' k) v.val.val =
      eval (chartPoint K (selectedTraceCoordinates z f) i) v.val.val
    have hp : chartPoint K (selectedTraceCoordinates z f) i = chartPoint K a' k := by
      unfold chartPoint
      rw [show (fun j => selectedTraceCoordinates z f (i, j)) = fun j => a' (k, j) from funext h]
    rw [hp]

/-- Uniform full-size attached/free interpolation implies unisolvence for
any ordered full-size selection of the same trace. -/
theorem selectedTrace_injective_of_attachedFree {p t N : ℕ}
    (U : Submodule K (Forms K (n + 1) d))
    (a : PointCoordinates K n p) (a' : PointCoordinates K n t)
    (z : PointCoordinates K n N) (e : (Fin p ⊕ Fin t) ≃ Fin N)
    (hc : ∀ label j, z (e label, j) = Sum.elim (fun i => a (i, j)) (fun i => a' (i, j)) label)
    (hgood : ∀ s : Finset (Fin p ⊕ Fin t), s.card = finrank K U →
      Function.Injective (selectedAttachedFreeEvaluation U a a' s))
    (hr : r = finrank K U) (f : Fin r ↪ Fin N) :
    Function.Injective (subspaceEvaluation U (selectedTraceCoordinates z f)) := by
  classical
  let j := e.symm ∘ f
  let s := Finset.univ.image j
  have hs : s.card = finrank K U := by
    change (Finset.univ.image j).card = finrank K U
    rw [Finset.card_image_of_injective _ (e.symm.injective.comp f.injective),
      Finset.card_univ, Fintype.card_fin, hr]
  intro v w hvw
  apply hgood s hs
  funext k
  have hk : k.val ∈ Finset.univ.image j := k.property
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hk
  change attachedFreeEvaluation U a a' v k.val = attachedFreeEvaluation U a a' w k.val
  rw [← hi]
  exact (selectedTrace_evaluation_row U a a' z e hc f v i).trans
    ((congrFun hvw i).trans (selectedTrace_evaluation_row U a a' z e hc f w i).symm)

/-- Label the points other than one chosen slice in their group order. -/
def markedFreeLabelsEquiv (b q l : ℕ) :
    (Fin b ⊕ (Fin q ⊕ Fin l)) ≃ Fin (b + (q + l)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

/-- Exchange the two slice groups of labels. -/
def swapMarkedSlices (b q l : ℕ) : MarkedLabels b q l ≃ MarkedLabels b q l where
  toFun := Sum.elim (fun i => Sum.inr (Sum.inl i)) (Sum.elim Sum.inl (fun i => Sum.inr (Sum.inr i)))
  invFun := Sum.elim (fun i => Sum.inr (Sum.inl i)) (Sum.elim Sum.inl (fun i => Sum.inr (Sum.inr i)))
  left_inv := by
    intro i
    rcases i with i | i
    · rfl
    · rcases i with i | i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · rfl
    · rcases i with i | i <;> rfl

/-- Read the chosen slice's attached labels first, then the free labels. -/
def markedSliceTraceEquiv (b q l : ℕ) (side : Bool) :
    (Fin b ⊕ Fin (b + (q + l))) ≃ Fin (b + (b + (q + l))) :=
  ((Equiv.sumCongr (Equiv.refl _) (markedFreeLabelsEquiv b q l).symm).trans
    (if side then swapMarkedSlices b q l else Equiv.refl _)).trans (markedLabelsEquiv b q l)

/-- Select one slice from the independent marked parameters. -/
def markedSliceSideIndex (n b q l : ℕ) (side : Bool) :
    (Fin b × Fin (n + 1)) → MarkedIndex n b q l :=
  if side then fun ij => Sum.inr (Sum.inl ij) else Sum.inl

/-- Fill the other groups with prescribed free trace coordinates. -/
def joinMarkedSliceWitness (side : Bool) (a : PointCoordinates K (n + 1) b)
    (free : PointCoordinates K n (b + (q + l))) : MarkedParameters K n b q l :=
  let e := markedFreeLabelsEquiv b q l
  let other : PointCoordinates K (n + 1) b := liftMarkedSlice (fun ij => free (e (Sum.inl ij.1), ij.2)) (fun _ => 1)
  let X : PointCoordinates K (n + 2) q := liftMarkedOffSlice
    (fun ij => free (e (Sum.inr (Sum.inl ij.1)), ij.2)) (fun _ => 1) (fun _ => 1)
  let Z : PointCoordinates K n l := fun ij => free (e (Sum.inr (Sum.inr ij.1)), ij.2)
  if side then joinMarkedParameters other a X Z else joinMarkedParameters a other X Z

/-- Filling free trace coordinates leaves the chosen slice unchanged. -/
theorem joinMarkedSliceWitness_slice (side : Bool) (a : PointCoordinates K (n + 1) b)
    (free : PointCoordinates K n (b + (q + l))) :
    joinMarkedSliceWitness side a free ∘ markedSliceSideIndex n b q l side = a := by
  cases side <;> rfl

/-- The witness has exactly the prescribed attached and free trace rows. -/
theorem joinMarkedSliceWitness_trace (side : Bool) (a : PointCoordinates K (n + 1) b)
    (free : PointCoordinates K n (b + (q + l)))
    (label : Fin b ⊕ Fin (b + (q + l))) (j : Fin n) :
    markedTraceCoordinates (joinMarkedSliceWitness side a free)
      (markedSliceTraceEquiv b q l side label, j) =
      Sum.elim (fun i => projectedCoordinates a (i, j)) (fun i => free (i, j)) label := by
  rcases label with i | i
  · cases side <;> simp [markedSliceTraceEquiv, swapMarkedSlices,
      joinMarkedSliceWitness, projectedCoordinates]
  · obtain ⟨label, rfl⟩ := (markedFreeLabelsEquiv b q l).surjective i
    rcases label with k | label
    · cases side <;> simp [markedSliceTraceEquiv, swapMarkedSlices, joinMarkedSliceWitness]
    · rcases label with k | k
      · cases side <;> simp [markedSliceTraceEquiv, swapMarkedSlices, joinMarkedSliceWitness]
      · cases side <;> simp [markedSliceTraceEquiv, swapMarkedSlices, joinMarkedSliceWitness]

/-- A selected trace row reads just its marked coordinates. -/
def markedTraceSelectionIndex (f : Fin r ↪ Fin (b + (b + (q + l)))) :
    (Fin r × Fin n) → MarkedIndex n b q l :=
  fun ij => markedTraceIndex n b q l (f ij.1, ij.2)

/-- One good slice and freely chosen remaining trace rows witness every
full-size unisolvent selection for that slice in the marked space. -/
theorem exists_markedSliceCode_witness [CharZero K] (side : Bool)
    (a : PointCoordinates K (n + 1) b)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0)
    (hprojected : Function.Surjective (projectedEvaluation a (d + 1)))
    (hr : r = finrank K (sliceProductSpace a d)) :
    ∃ c : MarkedParameters K n b q l,
      c ∘ markedSliceSideIndex n b q l side = a ∧
      ∀ f : Fin r ↪ Fin (b + (b + (q + l))),
        Function.Injective (subspaceEvaluation (sliceProductSpace a d)
          (c ∘ markedTraceSelectionIndex f)) := by
  let U := sliceProductSpace a d
  have hA : Function.Surjective (subspaceEvaluation U (projectedCoordinates a)) := by
    change Function.Surjective ((pointEvaluation K (projectedCoordinates a) (d + 1 + 1)).comp
      (tangentPointProductForm a (d + 1)).range.subtype)
    rw [← projectedEvaluation_eq]
    exact traceProductImage_evaluation_surjective_of_projected a d ha hprojected
  obtain ⟨P, ⟨free, hf⟩, hgood⟩ := generic_attachedFree_unisolvent U
    (projectedCoordinates a) hA (b + (q + l))
  let c := joinMarkedSliceWitness side a free
  refine ⟨c, joinMarkedSliceWitness_slice side a free, ?_⟩
  intro f
  exact selectedTrace_injective_of_attachedFree U (projectedCoordinates a) free
    (markedTraceCoordinates c) (markedSliceTraceEquiv b q l side)
    (joinMarkedSliceWitness_trace side a free) (hgood free hf) hr f

/-- All full-size selections for one varying slice are unisolvent on a
single nonempty principal open of marked parameters. -/
theorem generic_markedSliceCode_unisolvent [CharZero K] (side : Bool)
    (a : PointCoordinates K (n + 1) b)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hprojected : Function.Surjective (projectedEvaluation a (d + 1)))
    (hr : r = finrank K (sliceProductSpace a d)) :
    ∃ P : MvPolynomial (MarkedIndex n b q l) K,
      (∃ c : MarkedParameters K n b q l, eval c P ≠ 0) ∧
      ∀ c, eval c P ≠ 0 → ∀ f : Fin r ↪ Fin (b + (b + (q + l))),
        Function.Injective (subspaceEvaluation
          (sliceProductSpace (c ∘ markedSliceSideIndex n b q l side) d)
          (c ∘ markedTraceSelectionIndex f)) := by
  classical
  let I := Fin r ↪ Fin (b + (b + (q + l)))
  let e := markedSliceSideIndex n b q l side
  obtain ⟨c₀, hslice, heval⟩ := exists_markedSliceCode_witness (q := q) (l := l) (d := d) (r := r)
    side a ha hprojected hr
  have hA : ∀ i, chartPoint K (c₀ ∘ e) i (0 : Fin (n + 2)) ≠ 0 := by
    rw [show c₀ ∘ e = a from hslice]
    exact ha
  have hM : Function.Injective (pointMultiplication (c₀ ∘ e) (d + 1)) := by
    rw [show c₀ ∘ e = a from hslice]
    exact hmul
  have hW (f : I) : Function.Injective (subspaceEvaluation
      (tangentPointProductForm (c₀ ∘ e) (d + 1)).range
      (c₀ ∘ markedTraceSelectionIndex f)) := by
    rw [show c₀ ∘ e = a from hslice]
    exact heval f
  choose P hP hgood using fun f : I => generic_sliceCode_open_of_witness
    e (markedTraceSelectionIndex f) c₀ hA hM (hW f)
  refine ⟨∏ f, P f, ⟨c₀, ?_⟩, ?_⟩
  · rw [map_prod, Finset.prod_ne_zero_iff]
    exact fun f _ => hP f
  · intro c hc f
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    exact hgood f c (hc f (Finset.mem_univ f))

/-- The two varying slice codes have simultaneous uniform interpolation on
a nonempty principal open of the common marked parameters. -/
theorem generic_markedSliceCodes_unisolvent [CharZero K]
    (a₀ b₀ : PointCoordinates K (n + 1) b)
    (ha : ∀ i, chartPoint K a₀ i (0 : Fin (n + 2)) ≠ 0)
    (hb : ∀ i, chartPoint K b₀ i (0 : Fin (n + 2)) ≠ 0)
    (hMulA : Function.Injective (pointMultiplication a₀ (d + 1)))
    (hMulB : Function.Injective (pointMultiplication b₀ (d + 1)))
    (hProjA : Function.Surjective (projectedEvaluation a₀ (d + 1)))
    (hProjB : Function.Surjective (projectedEvaluation b₀ (d + 1)))
    (hrA : r = finrank K (sliceProductSpace a₀ d))
    (hrB : r = finrank K (sliceProductSpace b₀ d)) :
    ∃ P : MvPolynomial (MarkedIndex n b q l) K,
      (∃ c : MarkedParameters K n b q l, eval c P ≠ 0) ∧
      ∀ c, eval c P ≠ 0 → ∀ f : Fin r ↪ Fin (b + (b + (q + l))),
        Function.Injective (subspaceEvaluation (sliceProductSpace (markedSliceA c) d)
          (c ∘ markedTraceSelectionIndex f)) ∧
        Function.Injective (subspaceEvaluation (sliceProductSpace (markedSliceB c) d)
          (c ∘ markedTraceSelectionIndex f)) := by
  obtain ⟨P, hP, hgoodP⟩ := generic_markedSliceCode_unisolvent (q := q) (l := l) (d := d) (r := r)
    false a₀ ha hMulA hProjA hrA
  obtain ⟨Q, hQ, hgoodQ⟩ := generic_markedSliceCode_unisolvent (q := q) (l := l) (d := d) (r := r)
    true b₀ hb hMulB hProjB hrB
  have hPn : P ≠ 0 := by
    obtain ⟨c, hc⟩ := hP
    intro hz
    simp [hz] at hc
  have hQn : Q ≠ 0 := by
    obtain ⟨c, hc⟩ := hQ
    intro hz
    simp [hz] at hc
  have hex : ∃ c : MarkedParameters K n b q l, eval c (P * Q) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hPn hQn (MvPolynomial.funext h)
  refine ⟨P * Q, hex, ?_⟩
  intro c hc f
  have hc' : eval c P ≠ 0 ∧ eval c Q ≠ 0 := by simpa using hc
  exact ⟨hgoodP c hc'.1 f, hgoodQ c hc'.2 f⟩

/-- The ordered trace quotient has independent coordinate classes whenever
all full-size selections are unisolvent for the actual slice product space. -/
theorem orderedTraceProduct_coordinateClasses {N : ℕ}
    (a : PointCoordinates K (n + 1) b) (z : PointCoordinates K n N)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hr : r = finrank K (sliceProductSpace a d)) (hcount : r ≤ N)
    (hselected : ∀ f : Fin r ↪ Fin N,
      Function.Injective (subspaceEvaluation (sliceProductSpace a d)
        (selectedTraceCoordinates z f))) :
    Function.Injective ((TwoNormalSlice.scalarEvaluation (chartPoint K z) (d + 1 + 1)).comp
      (tangentPointProductForm a (d + 1)).range.subtype) ∧
    ∀ (k : ℕ) (f : Fin k ↪ Fin N),
      k ≤ finrank K ((Fin N → K) ⧸
        ((TwoNormalSlice.scalarEvaluation (chartPoint K z) (d + 1 + 1)).comp
          (tangentPointProductForm a (d + 1))).range) →
      LinearIndependent K (coordinateClass
        ((TwoNormalSlice.scalarEvaluation (chartPoint K z) (d + 1 + 1)).comp
          (tangentPointProductForm a (d + 1))) ∘ f) := by
  classical
  let T := tangentPointProductForm a (d + 1)
  let U := sliceProductSpace a d
  let E := (TwoNormalSlice.scalarEvaluation (chartPoint K z) (d + 1 + 1)).comp T
  let C := Fin (n + 1) → pointPolynomialPiece a (d + 1)
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  have hT : Function.Injective T := tangentPointProductForm_injective a ha hmul
  have hdim : finrank K C = r := (LinearMap.finrank_range_of_inj hT).symm.trans hr.symm
  have hU : Function.Injective (subspaceEvaluation U z) := by
    intro v w hvw
    let f : Fin r ↪ Fin N := ⟨Fin.castLE hcount, Fin.castLE_injective hcount⟩
    apply hselected f
    funext i
    exact congrFun hvw (f i)
  have hE : Function.Injective E := by
    intro v w hvw
    apply hT
    have h : T.rangeRestrict v = T.rangeRestrict w := hU hvw
    exact congrArg Subtype.val h
  have hgood (s : Finset (Fin N)) (hs : s.card = finrank K C) :
      Function.Injective (selectedScalarEvaluation (fun i => (LinearMap.proj i).comp E) s) := by
    let e : Fin r ≃ s := (Fintype.equivFinOfCardEq
      ((Fintype.card_coe _).trans (hs.trans hdim))).symm
    let f : Fin r ↪ Fin N := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
    intro v w hvw
    apply hT
    have h : T.rangeRestrict v = T.rangeRestrict w := by
      apply hselected f
      funext i
      exact congrFun hvw (e i)
    exact congrArg Subtype.val h
  exact ⟨hU, coordinateClasses_independent E hE hgood⟩

end IdealGeneration.TwoNormalIntegral
