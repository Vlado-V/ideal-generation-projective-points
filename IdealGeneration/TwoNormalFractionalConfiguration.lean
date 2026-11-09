module

public import IdealGeneration.TwoNormalFractionalMarkedInputs
public import IdealGeneration.TwoNormalFractionalPairOpen
public import IdealGeneration.TwoNormalAmbientComparison

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # A common marked configuration for the fractional trace -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoNormalTrace TwoNormalSlice TwoNormalIntegral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q l d g : ℕ}

private abbrev aOf (c : FractionalParameters K n b q l) := markedSliceA (c ∘ Sum.inl)
private abbrev bOf (c : FractionalParameters K n b q l) := markedSliceB (c ∘ Sum.inl)
private abbrev zOf (c : FractionalParameters K n b q l) := chartPoint K (fractionalTraceCoordinates c)
private abbrev xOf (c : FractionalParameters K n b q l) := fractionalOffCoordinates c

/-- The independent rank conditions on the common trace and its augmentation. -/
structure FractionalTraceGood (c : FractionalParameters K n b q l) (d : ℕ) : Prop where
  euler : Function.Surjective (traceFiberEvaluation (zOf c) (d + 1 + 1))
  augmented : Function.Injective (relationEvaluation
    (chartPoint K (fractionalAugmentedTraceCoordinates c)) (d + 1 + 1))
  scalar : Function.Surjective (pointEvaluation K (fractionalTraceCoordinates c) (d + 1 + 1))
  lowerScalar : Function.Injective (scalarEvaluation (zOf c) (d + 1))

/-- The two enlarged product evaluations after deleting the free point. -/
structure FractionalEnlargedGood (c : FractionalParameters K n b q l) (d : ℕ) : Prop where
  first : Function.Injective ((pointEvaluation K (aOf c) (d + 1)).comp
    (sliceAProduct K (n + 1) (pointDegreePiece K (attachedOffPoints (xOf c)) d)))
  second : Function.Injective ((pointEvaluation K (bOf c) (d + 1)).comp
    (sliceBProduct K (n + 1) (pointDegreePiece K (attachedOffPoints (xOf c)) d)))

/-- All interpolations on the same marked fractional configuration. -/
structure FractionalMarkedGood (c : FractionalParameters K n b q l) (d g : ℕ) : Prop where
  firstSlice : FractionalSliceCodeGood (q := q) (l := l) (aOf c) (zOf c) d
  secondSlice : FractionalSliceCodeGood (q := q) (l := l) (bOf c) (zOf c) d
  trace : FractionalTraceGood c d
  enlarged : FractionalEnlargedGood c d
  offSlice : IntegralOffSliceGood (xOf c) d g
  pair : Function.Surjective (pairEvaluation K (n + 1) (aOf c) (bOf c) (xOf c) d)

/-- The jointly open slice and trace conditions can be met along with
residual pair interpolation for a chosen off-slice ideal. -/
theorem exists_fractionalMarkedGood [CharZero K]
    (hSlice : ContainsPrincipalOpen (fun a : PointCoordinates K (n + 1) b => IntegralSliceGood a d))
    (hTrace : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l => FractionalTraceGood c d))
    (hEnlarged : ContainsPrincipalOpen (fun c : FractionalParameters K n b q l =>
      FractionalEnlargedGood c d))
    (hOff : ContainsPrincipalOpen (fun x : PointCoordinates K (n + 2) (q + 1) =>
      IntegralOffSliceGood x d g))
    (hcodeBudget : (n + 1) * (N (n + 2) (d + 1) - b) ≤ b + (b + (q + l)))
    (hpureBudget : (n + 2) * g ≤ b)
    (hpairBudget : 2 * b ≤ (n + 1) * g + (N (n + 3) (d + 1) - (q + 1))) :
    ∃ c : FractionalParameters K n b q l, FractionalMarkedGood c d g := by
  obtain ⟨D, hD, hgood⟩ := ((fractional_slice_codes_open hSlice hcodeBudget).inter hTrace).inter hEnlarged
  obtain ⟨P, hP, hPgood⟩ := hOff
  let R := fun (x : PointCoordinates K (n + 2) (q + 1)) (a c : PointCoordinates K (n + 1) b) =>
    Function.Surjective (pairEvaluation K (n + 1) a c x d)
  have hR : ∀ x : PointCoordinates K (n + 2) (q + 1), eval x P ≠ 0 →
      ∃ Q : MvPolynomial ((Fin b × Fin (n + 1)) ⊕ (Fin b × Fin (n + 1))) K,
        (∃ c, eval c Q ≠ 0) ∧ ∀ c, eval c Q ≠ 0 → R x (c ∘ Sum.inl) (c ∘ Sum.inr) := by
    intro x hx
    have hX := hPgood x hx
    have hpure : (n + 2) * finrank K (pointDegreePiece K x d) ≤ b := by
      rw [hX.dimension]
      exact hpureBudget
    obtain ⟨Q, hQ, hQgood⟩ := generic_residualPair_conditions x hX.sNonzero hX.tNonzero
      hX.trace hX.product b hpure
    refine ⟨Q, hQ, fun c hc => ?_⟩
    let a := c ∘ Sum.inl
    let b' := c ∘ Sum.inr
    apply pairEvaluation_surjective_of_kernel_finrank K (n + 1) a b' x d
    have he : finrank K (pairEvaluation K (n + 1) a b' x d).ker =
        finrank K (twoGroupEvaluation (residualPairSpace x d) a b').ker :=
      (pairEvaluationRangeKernelEquiv K (n + 1) a b' x
        (residualPair_injective K (n + 1) x hX.sNonzero hX.trace hX.product)).finrank_eq
    have hk := (hQgood c hc).1
    change finrank K (pairEvaluation K (n + 1) a b' x d).ker + (b + b) = _
    rw [he, hk, hX.dimension, hX.nextDimension]
    omega
  obtain ⟨c, hcD, hcP, hpair⟩ := exists_fractional_on_joint_and_pair_opens D hD P hP R hR
  obtain ⟨⟨⟨ha, hb⟩, hz⟩, he⟩ := hgood c hcD
  exact ⟨c, ha, hb, hz, he, hPgood _ hcP, hpair⟩

end IdealGeneration.TwoNormalFractional
