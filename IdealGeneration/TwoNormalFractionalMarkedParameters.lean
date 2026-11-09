module

public import IdealGeneration.TwoNormalMarkedParameters
public import IdealGeneration.TwoNormalFractionalFreePoint

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Independent marked parameters with one free projection -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open TwoNormalIntegral Function
set_option maxHeartbeats 600000

abbrev FractionalIndex (n b q l : ℕ) := MarkedIndex n b q l ⊕ Fin (n + 2)
abbrev FractionalParameters (K : Type*) (n b q l : ℕ) := FractionalIndex n b q l → K

variable {K : Type*} {n b q l : ℕ}

private def pointArraySplit (p s : ℕ) :
    (Fin (p + 1) × Fin s) ≃ ((Fin p × Fin s) ⊕ (Fin 1 × Fin s)) :=
  (Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumProdDistrib _ _ _)

private def singletonRow (s : ℕ) : (Fin 1 × Fin s) ↪ Fin s :=
  ⟨Prod.snd, fun _ _ h => Prod.ext (Subsingleton.elim _ _) h⟩

/-- All off-slice points, including the independent last one, are freely selectable. -/
def fractionalOffIndex (n b q l : ℕ) :
    (Fin (q + 1) × Fin (n + 2)) ↪ FractionalIndex n b q l :=
  (pointArraySplit q (n + 2)).toEmbedding.trans
    (Embedding.sumMap ⟨fun j => Sum.inr (Sum.inr (Sum.inl j)), by
      intro x y h
      simpa using h⟩ (singletonRow (n + 2)))

/-- The trace and the free projected last point are independently selectable. -/
def fractionalAugmentedTraceIndex (n b q l : ℕ) :
    (Fin (b + (b + (q + l)) + 1) × Fin n) ↪ FractionalIndex n b q l :=
  (pointArraySplit (b + (b + (q + l))) n).toEmbedding.trans
    (Embedding.sumMap (markedTraceIndex n b q l)
      ((singletonRow n).trans ((Fin.succEmb n).trans (Fin.succEmb (n + 1)))))

def fractionalOffCoordinates (c : FractionalParameters K n b q l) :
    PointCoordinates K (n + 2) (q + 1) :=
  c ∘ fractionalOffIndex n b q l

def fractionalAugmentedTraceCoordinates (c : FractionalParameters K n b q l) :
    PointCoordinates K n (b + (b + (q + l)) + 1) :=
  c ∘ fractionalAugmentedTraceIndex n b q l

@[simp] theorem fractionalOffCoordinates_castSucc
    (c : FractionalParameters K n b q l) (i : Fin q) (j : Fin (n + 2)) :
    fractionalOffCoordinates c (i.castSucc, j) = markedOffSlice (c ∘ Sum.inl) (i, j) := by
  unfold fractionalOffCoordinates fractionalOffIndex pointArraySplit
  simp [markedOffSlice]
  rfl

@[simp] theorem fractionalOffCoordinates_last
    (c : FractionalParameters K n b q l) (j : Fin (n + 2)) :
    fractionalOffCoordinates c (Fin.last q, j) = c (Sum.inr j) := by
  unfold fractionalOffCoordinates fractionalOffIndex pointArraySplit
  simp [singletonRow]
  rfl

@[simp] theorem fractionalAugmentedTraceCoordinates_castSucc
    (c : FractionalParameters K n b q l) (i : Fin (b + (b + (q + l)))) (j : Fin n) :
    fractionalAugmentedTraceCoordinates c (i.castSucc, j) =
      markedTraceCoordinates (c ∘ Sum.inl) (i, j) := by
  unfold fractionalAugmentedTraceCoordinates fractionalAugmentedTraceIndex pointArraySplit
  simp [markedTraceCoordinates]

@[simp] theorem fractionalAugmentedTraceCoordinates_last
    (c : FractionalParameters K n b q l) (j : Fin n) :
    fractionalAugmentedTraceCoordinates c (Fin.last (b + (b + (q + l))), j) =
      c (Sum.inr j.succ.succ) := by
  unfold fractionalAugmentedTraceCoordinates fractionalAugmentedTraceIndex pointArraySplit
  simp [singletonRow]
  rfl

/-- Removing the free point recovers the attached off-slice array. -/
@[simp] theorem attachedOffPoints_fractionalOffCoordinates
    (c : FractionalParameters K n b q l) :
    attachedOffPoints (fractionalOffCoordinates c) = markedOffSlice (c ∘ Sum.inl) := by
  funext ij
  exact fractionalOffCoordinates_castSucc c ij.1 ij.2

variable [Field K]

/-- The augmented ordered trace has the geometric projection as its last point. -/
theorem chartPoint_fractionalAugmentedTrace
    (c : FractionalParameters K n b q l) :
    chartPoint K (fractionalAugmentedTraceCoordinates c) =
      (Fin.snoc (chartPoint K (markedTraceCoordinates (c ∘ Sum.inl)))
        (commonProjection (chartPoint K (fractionalOffCoordinates c) (Fin.last q))) :
        Fin (b + (b + (q + l)) + 1) → Fin (n + 1) → K) := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · change chartPoint K (fractionalAugmentedTraceCoordinates c) (Fin.last _) (Fin.last n) =
        chartPoint K (fractionalOffCoordinates c) (Fin.last q) (Fin.last n).succ.succ
      simp
    · change chartPoint K (fractionalAugmentedTraceCoordinates c) (Fin.last _) j.castSucc =
        chartPoint K (fractionalOffCoordinates c) (Fin.last q) j.castSucc.succ.succ
      simp only [Fin.succ_castSucc, chartPoint_castSucc,
        fractionalAugmentedTraceCoordinates_last, fractionalOffCoordinates_last]
  · rw [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp

end IdealGeneration.TwoNormalFractional
