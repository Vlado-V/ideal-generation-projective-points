module

public import IdealGeneration.MinimalGenerators
public import IdealGeneration.PointTensorMultiplication
public import IdealGeneration.ProjectiveChartPoints
public import IdealGeneration.PointIdealReduced

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Theorem 1.1 on the ordered configuration space of the standard projective chart. -/

namespace IdealGeneration

open MvPolynomial

/-- The maximal-rank and minimal-generator assertions on the same nonempty open.
The index `n` is projective dimension, so the homogeneous ring has `n + 1` variables. -/
def TheoremOneOne (K : Type*) [Field K] : Prop :=
  ∀ n d p : ℕ, 1 ≤ n → 2 ≤ d →
    N (n + 1) (d - 1) ≤ p → p < N (n + 1) d →
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a : PointCoordinates K n p, eval a Δ ≠ 0 →
        Function.Injective (projectivePointFamily a) ∧
        (pointIdeal K a).IsRadical ∧
        (∀ e, pointHilbertFunction K a e = min (N (n + 1) e) p) ∧
        HasMaximalRank (pointTensorMultiplication a d) ∧
        ∃ r : ℕ,
          (r : ℚ) = max 0 ((n : ℚ) * (E (n + 1) d - (N (n + 1) d - p : ℕ))) ∧
          ∃ g : Fin (N (n + 1) d - p) ⊕ Fin r → Poly K (n + 1),
            (∀ i, (g (.inl i)).IsHomogeneous d) ∧
            (∀ i, (g (.inr i)).IsHomogeneous (d + 1)) ∧
            Ideal.span (Set.range g) = pointIdeal K a ∧
            (∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i})) ∧
            Function.Injective g

variable {K : Type*} [Field K] [CharZero K]

/-- The maximal-rank assertion yields the full statement, with the same parameter polynomial. -/
theorem theoremOneOne_of_idealGenerationConjecture
    (h : IdealGenerationConjecture K) : TheoremOneOne K := by
  intro n d p hn hd hlo hhi
  have hlo' : (n + d - 1).choose (d - 1) ≤ p := by
    simpa only [N_chart, show n + (d - 1) = n + d - 1 by omega] using hlo
  have hhi' : p < (n + d).choose d := by simpa only [N_chart] using hhi
  obtain ⟨Δ, hΔ, hopen⟩ := h n d p hn hd hlo' hhi'
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨hdistinct, hpost, hrank⟩ := hopen a ha
  have hpost' (e : ℕ) : pointHilbertFunction K a e = min (N (n + 1) e) p := by
    simpa only [N_chart] using hpost e
  refine ⟨(distinctPoints_iff_projectivePointFamily_injective a).mp hdistinct,
    pointIdeal_isRadical a, hpost', (pointTensorMultiplication_maximalRank_iff a d).mpr hrank, ?_⟩
  exact pointIdeal_exact_minimal_generators a d (by omega) hlo hhi.le hpost' hrank

end IdealGeneration
