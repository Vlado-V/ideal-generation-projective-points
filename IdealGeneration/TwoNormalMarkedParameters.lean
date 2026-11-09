module

public import IdealGeneration.RankOpen
public import IdealGeneration.Points
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Affine parameters for the marked two-normal configuration

The slice heights and the two off-slice heights are free coordinates. The
trace coordinates are obtained by retaining disjoint coordinate sets from
the four groups, so prescribing the ordered trace does not constrain any
normal height.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial Function

/-- The labels of the two attached slices, the attached off-slice group,
and the additional trace group, in that order. -/
abbrev MarkedLabels (b q l : ℕ) := Fin b ⊕ (Fin b ⊕ (Fin q ⊕ Fin l))

/-- All independent affine parameters for the four groups. -/
abbrev MarkedIndex (n b q l : ℕ) :=
  (Fin b × Fin (n + 1)) ⊕ ((Fin b × Fin (n + 1)) ⊕
    ((Fin q × Fin (n + 2)) ⊕ (Fin l × Fin n)))

abbrev MarkedParameters (K : Type*) (n b q l : ℕ) := MarkedIndex n b q l → K

/-- The ordinary ordered labels underlying the disjoint group labels. -/
def markedLabelsEquiv (b q l : ℕ) : MarkedLabels b q l ≃ Fin (b + (b + (q + l))) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

private def distributeMarkedLabels (n b q l : ℕ) :
    (MarkedLabels b q l × Fin n) ≃
      ((Fin b × Fin n) ⊕ ((Fin b × Fin n) ⊕ ((Fin q × Fin n) ⊕ (Fin l × Fin n)))) :=
  (Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumProdDistrib _ _ _).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.sumProdDistrib _ _ _))))

private def markedTraceFromLabels (n b q l : ℕ) :
    (MarkedLabels b q l × Fin n) ↪ MarkedIndex n b q l :=
  (distributeMarkedLabels n b q l).toEmbedding.trans
    (Embedding.sumMap ((Embedding.refl _).prodMap (Fin.succEmb n))
      (Embedding.sumMap ((Embedding.refl _).prodMap (Fin.succEmb n))
        (Embedding.sumMap ((Embedding.refl _).prodMap ((Fin.succEmb n).trans (Fin.succEmb (n + 1))))
          (Embedding.refl _))))

/-- The ordered trace parameters are a subset of the independent marked parameters. -/
def markedTraceIndex (n b q l : ℕ) :
    (Fin (b + (b + (q + l))) × Fin n) ↪ MarkedIndex n b q l :=
  (Equiv.prodCongr (markedLabelsEquiv b q l).symm (Equiv.refl _)).toEmbedding.trans
    (markedTraceFromLabels n b q l)

variable {K : Type*} {n b q l : ℕ}

/-- The first slice parameters. -/
def markedSliceA (c : MarkedParameters K n b q l) : PointCoordinates K (n + 1) b :=
  c ∘ Sum.inl

/-- The second slice parameters. -/
def markedSliceB (c : MarkedParameters K n b q l) : PointCoordinates K (n + 1) b :=
  fun ij => c (Sum.inr (Sum.inl ij))

/-- The points away from both slices. -/
def markedOffSlice (c : MarkedParameters K n b q l) : PointCoordinates K (n + 2) q :=
  fun ij => c (Sum.inr (Sum.inr (Sum.inl ij)))

/-- The additional trace parameters. -/
def markedExtraTrace (c : MarkedParameters K n b q l) : PointCoordinates K n l :=
  fun ij => c (Sum.inr (Sum.inr (Sum.inr ij)))

/-- The full trace consists of the three attached projections and the extra points. -/
def markedTraceCoordinates (c : MarkedParameters K n b q l) :
    PointCoordinates K n (b + (b + (q + l))) := c ∘ markedTraceIndex n b q l

/-- Assemble arbitrary configurations in the four independent marked groups. -/
def joinMarkedParameters (A B : PointCoordinates K (n + 1) b)
    (X : PointCoordinates K (n + 2) q) (Z : PointCoordinates K n l) :
    MarkedParameters K n b q l := Sum.elim A (Sum.elim B (Sum.elim X Z))

@[simp] theorem markedSliceA_join (A B : PointCoordinates K (n + 1) b)
    (X : PointCoordinates K (n + 2) q) (Z : PointCoordinates K n l) :
    markedSliceA (joinMarkedParameters A B X Z) = A := rfl

@[simp] theorem markedSliceB_join (A B : PointCoordinates K (n + 1) b)
    (X : PointCoordinates K (n + 2) q) (Z : PointCoordinates K n l) :
    markedSliceB (joinMarkedParameters A B X Z) = B := rfl

@[simp] theorem markedOffSlice_join (A B : PointCoordinates K (n + 1) b)
    (X : PointCoordinates K (n + 2) q) (Z : PointCoordinates K n l) :
    markedOffSlice (joinMarkedParameters A B X Z) = X := rfl

@[simp] theorem markedExtraTrace_join (A B : PointCoordinates K (n + 1) b)
    (X : PointCoordinates K (n + 2) q) (Z : PointCoordinates K n l) :
    markedExtraTrace (joinMarkedParameters A B X Z) = Z := rfl

@[simp] theorem markedTraceCoordinates_A (c : MarkedParameters K n b q l)
    (i : Fin b) (j : Fin n) :
    markedTraceCoordinates c (markedLabelsEquiv b q l (Sum.inl i), j) =
      markedSliceA c (i, j.succ) := by
  change c (markedTraceFromLabels n b q l
    ((markedLabelsEquiv b q l).symm (markedLabelsEquiv b q l (Sum.inl i)), j)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem markedTraceCoordinates_B (c : MarkedParameters K n b q l)
    (i : Fin b) (j : Fin n) :
    markedTraceCoordinates c (markedLabelsEquiv b q l (Sum.inr (Sum.inl i)), j) =
      markedSliceB c (i, j.succ) := by
  change c (markedTraceFromLabels n b q l
    ((markedLabelsEquiv b q l).symm (markedLabelsEquiv b q l (Sum.inr (Sum.inl i))), j)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem markedTraceCoordinates_X (c : MarkedParameters K n b q l)
    (i : Fin q) (j : Fin n) :
    markedTraceCoordinates c (markedLabelsEquiv b q l (Sum.inr (Sum.inr (Sum.inl i))), j) =
      markedOffSlice c (i, j.succ.succ) := by
  change c (markedTraceFromLabels n b q l
    ((markedLabelsEquiv b q l).symm
      (markedLabelsEquiv b q l (Sum.inr (Sum.inr (Sum.inl i)))), j)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem markedTraceCoordinates_extra (c : MarkedParameters K n b q l)
    (i : Fin l) (j : Fin n) :
    markedTraceCoordinates c (markedLabelsEquiv b q l (Sum.inr (Sum.inr (Sum.inr i))), j) =
      markedExtraTrace c (i, j) := by
  change c (markedTraceFromLabels n b q l
    ((markedLabelsEquiv b q l).symm
      (markedLabelsEquiv b q l (Sum.inr (Sum.inr (Sum.inr i)))), j)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Prescribing the ordered trace leaves all normal heights free. -/
theorem markedTraceCoordinates_surjective [Zero K] :
    Function.Surjective (markedTraceCoordinates (K := K) (n := n) (b := b) (q := q) (l := l)) := by
  intro z
  let e := markedTraceIndex n b q l
  refine ⟨Function.extend e z (fun _ => 0), ?_⟩
  funext ij
  change Function.extend e z (fun _ => 0) (e ij) = z ij
  exact e.injective.extend_apply z _ ij

/-- Attach any chosen normal heights to a prescribed slice projection. -/
def liftMarkedSlice (z : PointCoordinates K n b) (height : Fin b → K) :
    PointCoordinates K (n + 1) b := fun ij =>
  Fin.cons (α := fun _ => K) (height ij.1) (fun j => z (ij.1, j)) ij.2

/-- Attach any chosen pair of normal heights to a prescribed off-slice projection. -/
def liftMarkedOffSlice (z : PointCoordinates K n q) (s t : Fin q → K) :
    PointCoordinates K (n + 2) q := fun ij =>
  Fin.cons (α := fun _ => K) (s ij.1)
    (Fin.cons (α := fun _ => K) (t ij.1) (fun j => z (ij.1, j))) ij.2

@[simp] theorem liftMarkedSlice_projection (z : PointCoordinates K n b)
    (h : Fin b → K) (i : Fin b) (j : Fin n) : liftMarkedSlice z h (i, j.succ) = z (i, j) := by
  simp [liftMarkedSlice]

@[simp] theorem liftMarkedOffSlice_projection (z : PointCoordinates K n q)
    (s t : Fin q → K) (i : Fin q) (j : Fin n) :
    liftMarkedOffSlice z s t (i, j.succ.succ) = z (i, j) := by
  simp [liftMarkedOffSlice]

/-- A witnessed principal open remains witnessed when pulled back along
an injective selection of independent affine parameters. -/
theorem principalOpen_pullback [Field K] {ι κ : Type*} (e : ι ↪ κ)
    (P : MvPolynomial ι K) (hP : ∃ a : ι → K, eval a P ≠ 0) :
    (∃ c : κ → K, eval c (rename e P) ≠ 0) ∧
      ∀ c : κ → K, eval c (rename e P) ≠ 0 → eval (c ∘ e) P ≠ 0 := by
  obtain ⟨a, ha⟩ := hP
  refine ⟨⟨Function.extend e a (fun _ => 0), ?_⟩, ?_⟩
  · rw [eval_rename]
    have he : Function.extend e a (fun _ => 0) ∘ e = a :=
      funext (fun i => e.injective.extend_apply a _ i)
    rwa [he]
  · intro c hc
    simpa only [eval_rename] using hc

end IdealGeneration.TwoNormalIntegral
