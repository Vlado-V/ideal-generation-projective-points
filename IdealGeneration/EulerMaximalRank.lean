module

public import IdealGeneration.MultiplicationOpen
public import IdealGeneration.PointDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Expected dimensions of Euler evaluation kernels

The component evaluation target contains one redundant Euler equation at each
point. Passing to the fiber kernel gives the dimension `n * p` that enters
partial trace interpolation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace IdealGeneration
open Module MvPolynomial

variable {K : Type*} [Field K] {n p d : ℕ}

local instance eulerRankRelationGroup : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

/-- Evaluating into the full component space or into the Euler fiber gives the
same kernel. -/
theorem eulerEvaluation_ker_eq (a : PointCoordinates K n p) (d : ℕ) :
    (eulerEvaluation a d).ker = (pointEulerSquare a d).leftOnKernel.ker := by
  ext f
  simp only [LinearMap.mem_ker]
  constructor
  · intro hf
    exact Subtype.ext hf
  · intro hf
    exact congrArg Subtype.val hf

/-- Scalar postulation and maximal-rank multiplication give the expected
number of Euler relations vanishing on the points. -/
theorem eulerEvaluation_kernel_finrank_of_maximalRank [CharZero K]
    (a : PointCoordinates K n p)
    (hscalar : Function.Surjective (pointEvaluation K a d))
    (hmax : HasMaximalRank (pointMultiplication a d)) :
    finrank K (eulerEvaluation a d).ker =
      finrank K (EulerRelations K n d) - n * p := by
  rcases hmax with hinj | hsurj
  · have hinjE : Function.Injective (eulerEvaluation a d) :=
      (eulerEvaluation_injective_iff a d).mpr
        ((pointEulerSquare a d).injective_iff.mp
          ((pointMultiplication_injective_iff a d).mp hinj))
    have hzero : finrank K (eulerEvaluation a d).ker = 0 := by
      have hk : (eulerEvaluation a d).ker = ⊥ := by
        ext f
        simp only [LinearMap.mem_ker, Submodule.mem_bot]
        exact ⟨fun hf => hinjE (hf.trans (map_zero _).symm), fun hf => by simp [hf]⟩
      rw [hk, finrank_bot]
    have hdim : finrank K (EulerRelations K n d) ≤ n * p := by
      have hle := Submodule.finrank_mono (eulerEvaluation_range_le a d)
      rwa [LinearMap.finrank_range_of_inj hinjE,
        finrank_fiberMultiplication_ker] at hle
    omega
  · have hsurjE : Function.Surjective (pointEulerSquare a d).leftOnKernel :=
      (pointEulerSquare a d).surjective_iff
        (formMultiplication_surjective (n + 1) d)
        (componentEvaluation_surjective a hscalar) |>.mp
        ((pointMultiplication_surjective_iff a d).mp hsurj)
    have hr := (eulerEvaluation_range_eq_iff a d).mpr hsurjE
    have hd : finrank K (eulerEvaluation a d).range +
        finrank K (eulerEvaluation a d).ker = finrank K (EulerRelations K n d) := by
      exact (LinearMap.finrank_range_add_finrank_ker
        (K := K) (V := EulerRelations K n d) (V₂ := Fin (n + 1) → Fin p → K)
        (eulerEvaluation a d))
    rw [hr, finrank_fiberMultiplication_ker] at hd
    omega

/-- The ideal-generation assertion supplies the expected Euler kernel
dimension on its nonempty principal open. -/
theorem generic_eulerEvaluation_kernel_finrank [CharZero K]
    (hp : p ≤ N (n + 1) d) (h : IdealGenerationAt K n d p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        finrank K (eulerEvaluation a d).ker =
          finrank K (EulerRelations K n d) - n * p := by
  obtain ⟨D, hD, hgood⟩ := h
  refine ⟨D, hD, fun a ha => ?_⟩
  obtain ⟨_, hpost, hmax⟩ := hgood a ha
  have hscalar : Function.Surjective (pointEvaluation K a d) := by
    apply pointEvaluation_surjective_of_hilbert_eq a
    simpa only [← N_chart, min_eq_right hp] using hpost d
  exact eulerEvaluation_kernel_finrank_of_maximalRank a hscalar hmax

end IdealGeneration
