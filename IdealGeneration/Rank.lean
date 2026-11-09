module

public import IdealGeneration.Multiplication

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Dimension formulas for maximal-rank linear maps. -/

noncomputable section
namespace IdealGeneration
open Module

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The injective-or-surjective formulation is equivalent to the usual rank formula. -/
theorem maximalRank_iff_rank_eq_min (f : V →ₗ[K] W) :
    HasMaximalRank f ↔ finrank K f.range = min (finrank K V) (finrank K W) := by
  constructor
  · rintro (hinj | hsurj)
    · rw [LinearMap.finrank_range_of_inj hinj]
      exact (min_eq_left (by
        simpa only [LinearMap.finrank_range_of_inj hinj] using
          Submodule.finrank_le f.range)).symm
    · have htop := LinearMap.range_eq_top.mpr hsurj
      rw [htop, finrank_top]
      exact (min_eq_right (LinearMap.finrank_le_finrank_of_surjective hsurj)).symm
  · intro hr
    rcases le_total (finrank K V) (finrank K W) with h | h
    · left
      rw [min_eq_left h] at hr
      apply LinearMap.ker_eq_bot.mp
      apply Submodule.finrank_eq_zero.mp
      have hn := f.finrank_range_add_finrank_ker
      omega
    · right
      rw [min_eq_right h] at hr
      exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)

/-- The cokernel of a maximal-rank map has the expected truncated dimension difference. -/
theorem cokernel_finrank_of_maximalRank (f : V →ₗ[K] W) (h : HasMaximalRank f) :
    finrank K (W ⧸ f.range) = finrank K W - finrank K V := by
  have hr := (maximalRank_iff_rank_eq_min f).mp h
  have hq := f.range.finrank_quotient_add_finrank
  rw [hr] at hq
  rcases le_total (finrank K V) (finrank K W) with hle | hle
  · rw [min_eq_left hle] at hq
    omega
  · rw [min_eq_right hle] at hq
    omega

/-- The kernel has the opposite truncated dimension difference. -/
theorem kernel_finrank_of_maximalRank (f : V →ₗ[K] W) (h : HasMaximalRank f) :
    finrank K f.ker = finrank K V - finrank K W := by
  have hr := (maximalRank_iff_rank_eq_min f).mp h
  have hn := f.finrank_range_add_finrank_ker
  rw [hr] at hn
  rcases le_total (finrank K V) (finrank K W) with hle | hle
  · rw [min_eq_left hle] at hn
    omega
  · rw [min_eq_right hle] at hn
    omega

end IdealGeneration
