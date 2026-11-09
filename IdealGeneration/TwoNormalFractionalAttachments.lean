module

public import IdealGeneration.TwoNormalFractionalConfiguration

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The actual geometric attachments in the fractional marked family -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open TwoNormalIntegral TwoNormalSlice TwoNormalTrace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d g : ℕ}

/-- Every slice point projects to its attached trace label. -/
theorem fractional_slice_attachments (c : FractionalParameters K n b q l) :
    (∀ i : Fin b, ∃ j, (fun k => chartPoint K (markedSliceA (c ∘ Sum.inl)) i k.succ) =
      chartPoint K (fractionalTraceCoordinates c) j) ∧
    (∀ i : Fin b, ∃ j, (fun k => chartPoint K (markedSliceB (c ∘ Sum.inl)) i k.succ) =
      chartPoint K (fractionalTraceCoordinates c) j) := by
  constructor
  · intro i
    refine ⟨markedLabelsEquiv b q l (Sum.inl i), ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp only [Fin.succ_castSucc, chartPoint_castSucc, fractionalTraceCoordinates,
        markedTraceCoordinates_A]
  · intro i
    refine ⟨markedLabelsEquiv b q l (Sum.inr (Sum.inl i)), ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp only [Fin.succ_castSucc, chartPoint_castSucc, fractionalTraceCoordinates,
        markedTraceCoordinates_B]

/-- The retained off-slice points are attached at their common projections. -/
theorem fractional_off_attachments (c : FractionalParameters K n b q l) :
    ∀ i : Fin q, ∃ j, commonProjection (chartPoint K (fractionalOffCoordinates c) i.castSucc) =
      chartPoint K (fractionalTraceCoordinates c) j := by
  intro i
  refine ⟨markedLabelsEquiv b q l (Sum.inr (Sum.inr (Sum.inl i))), ?_⟩
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [commonProjection]
  · simp only [commonProjection, Fin.succ_castSucc, chartPoint_castSucc,
      fractionalOffCoordinates_castSucc, fractionalTraceCoordinates, markedTraceCoordinates_X]

/-- Translate the marked rank conditions to the slice and source conditions
of the actual ambient Euler kernel. -/
theorem fractional_conditions_of_marked (c : FractionalParameters K n b q l)
    (h : FractionalMarkedGood c d g) :
    SliceConditions (markedSliceA (c ∘ Sum.inl)) (markedSliceB (c ∘ Sum.inl))
      (chartPoint K (fractionalTraceCoordinates c)) d ∧
    SourceConditions (markedSliceA (c ∘ Sum.inl)) (markedSliceB (c ∘ Sum.inl))
      (fractionalOffCoordinates c) (chartPoint K (fractionalTraceCoordinates c)) d := by
  obtain ⟨ha, hb⟩ := fractional_slice_attachments c
  refine ⟨⟨ha, hb, h.firstSlice.slice.normal, h.secondSlice.slice.normal,
    h.firstSlice.slice.multiplication, h.secondSlice.slice.multiplication,
    h.firstSlice.evaluation, h.secondSlice.evaluation⟩, ?_⟩
  refine ⟨fractional_off_attachments c, ?_, h.offSlice.sNonzero, h.offSlice.tNonzero,
    h.firstSlice.slice.lowerScalar, h.secondSlice.slice.lowerScalar,
    h.enlarged.first, h.enlarged.second, h.trace.lowerScalar⟩
  rw [← chartPoint_fractionalAugmentedTrace c]
  exact h.trace.augmented

end IdealGeneration.TwoNormalFractional
