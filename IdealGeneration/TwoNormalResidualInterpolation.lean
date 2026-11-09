module

public import IdealGeneration.TwoNormalPureDimensions
public import IdealGeneration.TwoGroupInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Interpolation of the actual residual polynomial pairs

Applying the two-group interpolation theorem to (4.8), with its pure-side
dimensions computed from the point ideal, gives the residual kernel count
in (4.9). No residual evaluation rank is assumed.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial Module TwoNormalTrace TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m q d : ℕ}

/-- The polynomial-pair image in (4.8). -/
def residualPairSpace (x : PointCoordinates K (m + 1) q) (d : ℕ) :
    Submodule K (Forms K (m + 1) (d + 1) × Forms K (m + 1) (d + 1)) :=
  (residualPair K m (d := d) x).range

/-- General equal-size slice groups impose the exact residual kernel count,
and each pure-side evaluation is injective. -/
theorem generic_residualPair_conditions [Infinite K]
    (x : PointCoordinates K (m + 1) q)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp
      (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d)))
    (b : ℕ) (hb : (m + 1) * finrank K (pointDegreePiece K x d) ≤ b) :
    ∃ P : MvPolynomial ((Fin b × Fin m) ⊕ (Fin b × Fin m)) K,
      (∃ c, eval c P ≠ 0) ∧
      ∀ c, eval c P ≠ 0 →
        finrank K (twoGroupEvaluation (residualPairSpace x d)
          (c ∘ Sum.inl) (c ∘ Sum.inr)).ker =
            m * finrank K (pointDegreePiece K x d) +
              finrank K (pointDegreePiece K x (d + 1)) - 2 * b ∧
        Function.Injective ((leftGroupEvaluation (residualPairSpace x d) (c ∘ Sum.inl)).comp
          (rightProjection (residualPairSpace x d)).ker.subtype) ∧
        Function.Injective ((rightGroupEvaluation (residualPairSpace x d) (c ∘ Sum.inr)).comp
          (leftProjection (residualPairSpace x d)).ker.subtype) := by
  have hA : finrank K (rightProjection (residualPairSpace x d)).ker ≤ b := by
    rw [residualPairSpace, finrank_rightProjection_residualPair_ker x hs htrace hproduct]
    exact hb
  have hB : finrank K (leftProjection (residualPairSpace x d)).ker ≤ b := by
    rw [residualPairSpace, finrank_leftProjection_residualPair_ker x hs ht htrace hproduct]
    exact hb
  obtain ⟨P, hP, hgood⟩ := generic_twoGroupInterpolation (residualPairSpace x d) b hA hB
  refine ⟨P, hP, fun c hc => ?_⟩
  obtain ⟨hk, hleft, hright⟩ := hgood c hc
  refine ⟨?_, hleft, hright⟩
  rw [residualPairSpace, finrank_residualPair_range x hs htrace hproduct] at hk
  exact hk

end IdealGeneration.TwoNormalIntegral
