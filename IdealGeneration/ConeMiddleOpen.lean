module

public import IdealGeneration.ConeMiddleFamily
public import IdealGeneration.HomogeneousTraceOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Openness and independent trace choice for the cone middle map

A special middle-rank witness yields a nonempty principal open in the marked
cone family. This open meets any independently witnessed trace principal
open. Full scalar evaluation ranks and nonzero normal coordinates and
heights can all be maintained at the resulting configuration.
-/

noncomputable section
namespace IdealGeneration.ConeMiddleFamily
open MvPolynomial Module ConeParameterSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {c m p q : ℕ}

local instance (priority := 2000) openSubmoduleCanonicalGroup
    {A : Type*} [AddCommMonoid A] [Module K A] (S : Submodule K A) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup K

/-- The native and fixed-ambient presentations have the same injectivity. -/
theorem middle_constrained_injective_iff (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) :
    Function.Injective ((configuration support a).middleMultiplication d) ↔
      Function.Injective (constrainedMiddle support a d) := by
  constructor
  · intro h f g hfg
    obtain ⟨f, rfl⟩ := (sourceKernelEquiv support a d).surjective f
    obtain ⟨g, rfl⟩ := (sourceKernelEquiv support a d).surjective g
    apply congrArg (sourceKernelEquiv support a d)
    apply h
    apply (targetKernelEquiv support a d).injective
    simpa only [← middle_constrained_commutes] using hfg
  · intro h f g hfg
    apply (sourceKernelEquiv support a d).injective
    apply h
    rw [middle_constrained_commutes, middle_constrained_commutes, hfg]

/-- The native and fixed-ambient presentations have the same surjectivity. -/
theorem middle_constrained_surjective_iff (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) :
    Function.Surjective ((configuration support a).middleMultiplication d) ↔
      Function.Surjective (constrainedMiddle support a d) := by
  constructor
  · intro h f
    obtain ⟨f, rfl⟩ := (targetKernelEquiv support a d).surjective f
    obtain ⟨g, hg⟩ := h f
    exact ⟨sourceKernelEquiv support a d g, by rw [middle_constrained_commutes, hg]⟩
  · intro h f
    obtain ⟨g, hg⟩ := h (targetKernelEquiv support a d f)
    obtain ⟨g, rfl⟩ := (sourceKernelEquiv support a d).surjective g
    refine ⟨g, (targetKernelEquiv support a d).injective ?_⟩
    simpa only [← middle_constrained_commutes] using hg

/-- Scalar postulation on the fixed spaces used by the middle map. -/
def FullEvaluation (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) : Prop :=
  Function.Surjective (normalEvaluation support a d) ∧
    Function.Surjective (traceEvaluation a d) ∧
    Function.Surjective (targetEvaluation support a d)

/-- Degree-`d` scalar postulation on nonzero cone representatives supplies
all scalar postulation required by the middle-map openness argument. -/
theorem fullEvaluation_of_degree (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ)
    (hpoint : ∀ i, (configuration support a).point i ≠ 0)
    (hnormal : Function.Surjective (normalEvaluation support a d))
    (htrace : Function.Surjective (traceEvaluation a d)) : FullEvaluation support a d :=
  ⟨hnormal, htrace, targetEvaluation_surjective_of_normalEvaluation support a d hpoint hnormal⟩

theorem middle_injective_principal_open (support : Fin p → Fin q)
    (a₀ : Parameters K c m p q) (d : ℕ)
    (h : Function.Injective ((configuration support a₀).middleMultiplication d)) :
    ∃ P : MvPolynomial (Index c m p q) K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        Function.Injective ((configuration support a).middleMultiplication d) := by
  obtain ⟨P, hP, hgood⟩ := ConstrainedRankOpen.constrainedMap_injective_principal_open
    (fun a => sourceEvaluation support a d) (fun a => targetEvaluation support a d)
    (fun _ => ambientMiddle (K := K) (c := c) (m := m) d)
    (fun a => ambientMiddle_preserves support a d)
    (sourceEvaluation_isPolynomialFamily support d) (ConstrainedRankOpen.isPolynomialMapFamily_const _)
    a₀ ((middle_constrained_injective_iff support a₀ d).mp h)
  exact ⟨P, hP, fun a ha => (middle_constrained_injective_iff support a d).mpr (hgood a ha)⟩

theorem middle_surjective_principal_open (support : Fin p → Fin q)
    (a₀ : Parameters K c m p q) (d : ℕ) (hpost : FullEvaluation support a₀ d)
    (h : Function.Surjective ((configuration support a₀).middleMultiplication d)) :
    ∃ P : MvPolynomial (Index c m p q) K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 →
        Function.Surjective ((configuration support a).middleMultiplication d) := by
  obtain ⟨P, hP, hgood⟩ := ConstrainedRankOpen.constrainedMap_surjective_principal_open
    (fun a => sourceEvaluation support a d) (fun a => targetEvaluation support a d)
    (fun _ => ambientMiddle (K := K) (c := c) (m := m) d)
    (fun a => ambientMiddle_preserves support a d)
    (sourceEvaluation_isPolynomialFamily support d)
    (targetEvaluation_isPolynomialFamily support d) (ConstrainedRankOpen.isPolynomialMapFamily_const _)
    a₀ (sourceEvaluation_surjective support a₀ d hpost.1 hpost.2.1) hpost.2.2
    ((middle_constrained_surjective_iff support a₀ d).mp h)
  exact ⟨P, hP, fun a ha => (middle_constrained_surjective_iff support a d).mpr (hgood a ha)⟩

theorem middle_maximalRank_principal_open (support : Fin p → Fin q)
    (a₀ : Parameters K c m p q) (d : ℕ) (hpost : FullEvaluation support a₀ d)
    (h : HasMaximalRank ((configuration support a₀).middleMultiplication d)) :
    ∃ P : MvPolynomial (Index c m p q) K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 → HasMaximalRank ((configuration support a).middleMultiplication d) := by
  rcases h with hi | hs
  · obtain ⟨P, hP, hgood⟩ := middle_injective_principal_open support a₀ d hi
    exact ⟨P, hP, fun a ha => Or.inl (hgood a ha)⟩
  · obtain ⟨P, hP, hgood⟩ := middle_surjective_principal_open support a₀ d hpost hs
    exact ⟨P, hP, fun a ha => Or.inr (hgood a ha)⟩

private theorem surjective_principal_open {ι V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (F : (ι → K) → V →ₗ[K] W) (hF : IsPolynomialFamily F)
    (a₀ : ι → K) (hs : Function.Surjective (F a₀)) :
    ∃ P : MvPolynomial ι K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 → Function.Surjective (F a) := by
  obtain ⟨P, hP, hgood⟩ := rank_polynomial_principal_open F hF a₀
  refine ⟨P, hP, fun a ha => LinearMap.range_eq_top.mp ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hlow := hgood a ha
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hlow
  exact le_antisymm (Submodule.finrank_le _) hlow

/-- Full scalar evaluation ranks and maximal middle rank persist together. -/
theorem middle_fullRank_principal_open (support : Fin p → Fin q)
    (a₀ : Parameters K c m p q) (d : ℕ) (hpost : FullEvaluation support a₀ d)
    (h : HasMaximalRank ((configuration support a₀).middleMultiplication d)) :
    ∃ P : MvPolynomial (Index c m p q) K, eval a₀ P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 → FullEvaluation support a d ∧
        HasMaximalRank ((configuration support a).middleMultiplication d) := by
  obtain ⟨P, hP, hPgood⟩ := middle_maximalRank_principal_open support a₀ d hpost h
  obtain ⟨Q, hQ, hQgood⟩ := surjective_principal_open
    (fun a => normalEvaluation support a d) (normalEvaluation_isPolynomialFamily support d) a₀ hpost.1
  obtain ⟨R, hR, hRgood⟩ := surjective_principal_open
    (fun a => traceEvaluation a d) (traceEvaluation_isPolynomialFamily d) a₀ hpost.2.1
  obtain ⟨S, hS, hSgood⟩ := surjective_principal_open
    (fun a => targetEvaluation support a d) (targetEvaluation_isPolynomialFamily support d) a₀ hpost.2.2
  refine ⟨P * Q * R * S, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero (mul_ne_zero (mul_ne_zero hP hQ) hR) hS
  · intro a ha
    have hparts : eval a P ≠ 0 ∧ eval a Q ≠ 0 ∧ eval a R ≠ 0 ∧ eval a S ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff, and_assoc] using ha
    exact ⟨⟨hQgood a hparts.2.1, hRgood a hparts.2.2.1, hSgood a hparts.2.2.2⟩,
      hPgood a hparts.1⟩

/-- A special middle witness and an independent homogeneous trace open admit
a common marked cone configuration with all scalar ranks maintained. -/
theorem exists_middle_trace_open [Infinite K] (support : Fin p → Fin q)
    (a₀ : Parameters K c m p q) (d : ℕ) (hpost : FullEvaluation support a₀ d)
    (h : HasMaximalRank ((configuration support a₀).middleMultiplication d))
    (j : Fin p → Fin c) (D : MvPolynomial (Fin q × Fin m) K) (hD : ∃ t, eval t D ≠ 0) :
    ∃ a : Parameters K c m p q, FullEvaluation support a d ∧
      HasMaximalRank ((configuration support a).middleMultiplication d) ∧
      eval (traceCoordinates a) D ≠ 0 ∧
      (∀ i, normalCoordinates a (i, j i) ≠ 0) ∧ (∀ i, heights a i ≠ 0) := by
  obtain ⟨P, hP, hgood⟩ := middle_fullRank_principal_open support a₀ d hpost h
  obtain ⟨a, ha, htrace, hnormal, hheight⟩ :=
    compatible_trace_open_nonzero j P ⟨a₀, hP⟩ D hD
  exact ⟨a, (hgood a ha).1, (hgood a ha).2, htrace, hnormal, hheight⟩

/-- The same choice applies to an inductive trace open stated in normalized
affine chart coordinates. -/
theorem exists_middle_affine_trace_open [Infinite K] {n : ℕ} (support : Fin p → Fin q)
    (a₀ : Parameters K c (n + 1) p q) (d : ℕ) (hpost : FullEvaluation support a₀ d)
    (h : HasMaximalRank ((configuration support a₀).middleMultiplication d))
    (j : Fin p → Fin c) (D : MvPolynomial (Fin q × Fin n) K) (hD : ∃ t, eval t D ≠ 0) :
    ∃ a : Parameters K c (n + 1) p q, FullEvaluation support a d ∧
      HasMaximalRank ((configuration support a).middleMultiplication d) ∧
      (∀ i, traceCoordinates a (i, Fin.last n) ≠ 0) ∧
      eval (HomogeneousTraceOpen.normalize (traceCoordinates a)) D ≠ 0 ∧
      (∀ i, normalCoordinates a (i, j i) ≠ 0) ∧ (∀ i, heights a i ≠ 0) := by
  obtain ⟨E, hE, hgood⟩ := HomogeneousTraceOpen.exists_homogeneous_trace_open D hD
  obtain ⟨a, ha, hmiddle, htrace, hnormal, hheight⟩ :=
    exists_middle_trace_open support a₀ d hpost h j E hE
  exact ⟨a, ha, hmiddle, (hgood _ htrace).1, (hgood _ htrace).2, hnormal, hheight⟩

end IdealGeneration.ConeMiddleFamily
