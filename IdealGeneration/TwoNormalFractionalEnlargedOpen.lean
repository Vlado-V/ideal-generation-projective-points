module

public import IdealGeneration.TwoNormalFractionalConfiguration
public import IdealGeneration.TwoNormalFractionalSourceOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The two enlarged product ranks on the common fractional family -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoNormalIntegral TwoNormalTrace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d : ℕ}

/-- A good attached off-slice ideal gives a common rank-open witness for
both enlarged slice evaluations. -/
theorem fractional_enlarged_open [Infinite K]
    (x : PointCoordinates K (n + 2) q)
    (ht : Function.Injective ((restrictTraceForm K (n + 1) d).comp
      (pointDegreePiece K x d).subtype))
    (hm : Function.Injective (traceProduct K (n + 1) d (pointDegreePiece K x d)))
    (hb : (n + 2) * finrank K (pointDegreePiece K x d) ≤ b) :
    ContainsPrincipalOpen (fun c : FractionalParameters K n b q l => FractionalEnlargedGood c d) := by
  let G := pointDegreePiece K x d
  obtain ⟨a, ha⟩ := exists_enlargedProductEvaluation_injective G (sliceAProduct K (n + 1) G)
    (sliceAProduct_injective K (n + 1) G ht hm) hb
  obtain ⟨b', hb'⟩ := exists_enlargedProductEvaluation_injective G (sliceBProduct K (n + 1) G)
    (sliceBProduct_injective K (n + 1) G ht hm) hb
  let c₀ : FractionalParameters K n b q l :=
    Sum.elim (joinMarkedParameters a b' x (fun _ => 0)) (fun _ => 0)
  let eX : (Fin q × Fin (n + 2)) → FractionalIndex n b q l :=
    fun i => Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))
  let eA : (Fin b × Fin (n + 1)) → FractionalIndex n b q l := fun i => Sum.inl (Sum.inl i)
  let eB : (Fin b × Fin (n + 1)) → FractionalIndex n b q l :=
    fun i => Sum.inl (Sum.inr (Sum.inl i))
  obtain ⟨A, hA, hgoodA⟩ := enlargedProductEvaluation_open_of_witness eX eA
    (restrictAForm K (n + 1) (d + 1)) (normalFormMul K (n + 2) d) c₀ ha
  obtain ⟨B, hB, hgoodB⟩ := enlargedProductEvaluation_open_of_witness eX eB
    (restrictForm K (n + 2) (d + 1)) (secondNormalMul K (n + 1) d) c₀ hb'
  refine ⟨A * B, ⟨c₀, by simpa using mul_ne_zero hA hB⟩, ?_⟩
  intro c hc
  have hparts : eval c A ≠ 0 ∧ eval c B ≠ 0 := by simpa using hc
  constructor
  · change Function.Injective ((pointEvaluation K (markedSliceA (c ∘ Sum.inl)) (d + 1)).comp
      (sliceAProduct K (n + 1) (pointDegreePiece K (attachedOffPoints (fractionalOffCoordinates c)) d)))
    rw [attachedOffPoints_fractionalOffCoordinates]
    exact hgoodA c hparts.1
  · change Function.Injective ((pointEvaluation K (markedSliceB (c ∘ Sum.inl)) (d + 1)).comp
      (sliceBProduct K (n + 1) (pointDegreePiece K (attachedOffPoints (fractionalOffCoordinates c)) d)))
    rw [attachedOffPoints_fractionalOffCoordinates]
    exact hgoodB c hparts.2

end IdealGeneration.TwoNormalFractional
