module

public import IdealGeneration.MainStatement
public import IdealGeneration.Numerics
public import IdealGeneration.Rank
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimensions of point-ideal multiplication

The scalar Hilbert function gives the source and target dimensions of the
actual multiplication map. Maximal rank therefore gives injection or
surjection on the respective side of the critical value.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial

variable {K : Type*} [Field K] {n p d : ℕ}

/-- The paper's monomial count in the affine-chart indexing convention. -/
theorem N_chart (n d : ℕ) : N (n + 1) d = (n + d).choose d := by
  unfold N
  congr 1
  omega

/-- The degree-`d` ideal dimension given by scalar postulation. -/
theorem pointDegreePiece_finrank (a : PointCoordinates K n p)
    (h : pointHilbertFunction K a d = min (N (n + 1) d) p) :
    finrank K (pointDegreePiece K a d) = N (n + 1) d - p := by
  rw [N_chart] at h ⊢
  exact ideal_piece_finrank_of_postulation a h

/-- There is one copy of the degree-`d` ideal component for each variable. -/
theorem pointMultiplication_source_finrank (a : PointCoordinates K n p)
    (h : pointHilbertFunction K a d = min (N (n + 1) d) p) :
    finrank K (Fin (n + 1) → pointDegreePiece K a d) =
      (n + 1) * (N (n + 1) d - p) := by
  have : Module.Free K (pointDegreePiece K a d) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K a d)
  rw [Module.finrank_pi_fintype]
  simp [pointDegreePiece_finrank a h]

/-- The target is the degree-`d+1` ideal component. -/
theorem pointMultiplication_target_finrank (a : PointCoordinates K n p)
    (h : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p) :
    finrank K (pointDegreePiece K a (d + 1)) = N (n + 1) (d + 1) - p :=
  pointDegreePiece_finrank a h

section LinearAlgebra
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- On the smaller-source side, a maximal-rank map is injective. -/
theorem injective_of_maximalRank_of_finrank_le (f : V →ₗ[K] W)
    (h : HasMaximalRank f) (hdim : finrank K V ≤ finrank K W) :
    Function.Injective f := by
  have hk := kernel_finrank_of_maximalRank f h
  have hz : finrank K f.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

/-- On the smaller-target side, a maximal-rank map is surjective. -/
theorem surjective_of_maximalRank_of_finrank_le (f : V →ₗ[K] W)
    (h : HasMaximalRank f) (hdim : finrank K W ≤ finrank K V) :
    Function.Surjective f := by
  have hr := (maximalRank_iff_rank_eq_min f).mp h
  rw [min_eq_right hdim] at hr
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
end LinearAlgebra

/-- Scalar postulation and the numerical dimension inequality force injection. -/
theorem pointMultiplication_injective_of_postulation
    (a : PointCoordinates K n p)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (h : HasMaximalRank (pointMultiplication a d))
    (hcount : (n + 1) * (N (n + 1) d - p) ≤ N (n + 1) (d + 1) - p) :
    Function.Injective (pointMultiplication a d) := by
  have hdim : finrank K (Fin (n + 1) → pointDegreePiece K a d) ≤
      finrank K (pointDegreePiece K a (d + 1)) := by
    rw [pointMultiplication_source_finrank a hd, pointMultiplication_target_finrank a hd1]
    exact hcount
  with_unfolding_all exact (injective_of_maximalRank_of_finrank_le
    (K := K) (V := Fin (n + 1) → pointDegreePiece K a d)
    (W := pointDegreePiece K a (d + 1)) (pointMultiplication a d) h hdim)

/-- Scalar postulation and the opposite dimension inequality force surjection. -/
theorem pointMultiplication_surjective_of_postulation
    (a : PointCoordinates K n p)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (h : HasMaximalRank (pointMultiplication a d))
    (hcount : N (n + 1) (d + 1) - p ≤ (n + 1) * (N (n + 1) d - p)) :
    Function.Surjective (pointMultiplication a d) := by
  have hdim : finrank K (pointDegreePiece K a (d + 1)) ≤
      finrank K (Fin (n + 1) → pointDegreePiece K a d) := by
    rw [pointMultiplication_source_finrank a hd, pointMultiplication_target_finrank a hd1]
    exact hcount
  with_unfolding_all exact (surjective_of_maximalRank_of_finrank_le
    (K := K) (V := Fin (n + 1) → pointDegreePiece K a d)
    (W := pointDegreePiece K a (d + 1)) (pointMultiplication a d) h hdim)


/-- Compare the actual source and target counts with the rational critical value. -/
theorem point_count_source_le_target_iff (hn : 1 ≤ n) (hp : p ≤ N (n + 1) d) :
    (n + 1) * (N (n + 1) d - p) ≤ N (n + 1) (d + 1) - p ↔
      ((N (n + 1) d - p : ℕ) : ℚ) ≤ E (n + 1) d := by
  have hmono : N (n + 1) d ≤ N (n + 1) (d + 1) := by
    simpa using N_pred_le (n + 1) (d + 1) (by omega) (by omega)
  have hpnext := hp.trans hmono
  have hmain := source_le_target_iff (n + 1) d (by omega)
    ((N (n + 1) d : ℚ) - p)
  have hrhs : (N (n + 1) (d + 1) : ℚ) - N (n + 1) d +
      ((N (n + 1) d : ℚ) - p) = (N (n + 1) (d + 1) : ℚ) - p := by ring
  rw [hrhs] at hmain
  constructor
  · intro h
    have hq : (((n + 1) * (N (n + 1) d - p) : ℕ) : ℚ) ≤
        ((N (n + 1) (d + 1) - p : ℕ) : ℚ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hpnext] at hq
    simpa only [Nat.cast_sub hp] using hmain.mp hq
  · intro h
    have hq := hmain.mpr (by simpa only [Nat.cast_sub hp] using h)
    have hcast : (((n + 1) * (N (n + 1) d - p) : ℕ) : ℚ) ≤
        ((N (n + 1) (d + 1) - p : ℕ) : ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hpnext] using hq
    exact_mod_cast hcast

/-- The reverse count inequality is equivalent to the surjective critical range. -/
theorem point_count_target_le_source_iff (hn : 1 ≤ n) (hp : p ≤ N (n + 1) d) :
    N (n + 1) (d + 1) - p ≤ (n + 1) * (N (n + 1) d - p) ↔
      E (n + 1) d ≤ ((N (n + 1) d - p : ℕ) : ℚ) := by
  have hmono : N (n + 1) d ≤ N (n + 1) (d + 1) := by
    simpa using N_pred_le (n + 1) (d + 1) (by omega) (by omega)
  have hpnext := hp.trans hmono
  have hmain := target_le_source_iff (n + 1) d (by omega)
    ((N (n + 1) d : ℚ) - p)
  have hrhs : (N (n + 1) (d + 1) : ℚ) - N (n + 1) d +
      ((N (n + 1) d : ℚ) - p) = (N (n + 1) (d + 1) : ℚ) - p := by ring
  rw [hrhs] at hmain
  constructor
  · intro h
    have hq : ((N (n + 1) (d + 1) - p : ℕ) : ℚ) ≤
        (((n + 1) * (N (n + 1) d - p) : ℕ) : ℚ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hpnext] at hq
    simpa only [Nat.cast_sub hp] using hmain.mp hq
  · intro h
    have hq := hmain.mpr (by simpa only [Nat.cast_sub hp] using h)
    have hcast : ((N (n + 1) (d + 1) - p : ℕ) : ℚ) ≤
        (((n + 1) * (N (n + 1) d - p) : ℕ) : ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hpnext] using hq
    exact_mod_cast hcast

/-- Maximal rank gives injection throughout the lower critical range. -/
theorem pointMultiplication_injective_below_critical (hn : 1 ≤ n)
    (a : PointCoordinates K n p) (hp : p ≤ N (n + 1) d)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (h : HasMaximalRank (pointMultiplication a d))
    (hcritical : ((N (n + 1) d - p : ℕ) : ℚ) ≤ E (n + 1) d) :
    Function.Injective (pointMultiplication a d) :=
  pointMultiplication_injective_of_postulation a hd hd1 h
    ((point_count_source_le_target_iff hn hp).mpr hcritical)

/-- Maximal rank gives surjection throughout the upper critical range. -/
theorem pointMultiplication_surjective_above_critical (hn : 1 ≤ n)
    (a : PointCoordinates K n p) (hp : p ≤ N (n + 1) d)
    (hd : pointHilbertFunction K a d = min (N (n + 1) d) p)
    (hd1 : pointHilbertFunction K a (d + 1) = min (N (n + 1) (d + 1)) p)
    (h : HasMaximalRank (pointMultiplication a d))
    (hcritical : E (n + 1) d ≤ ((N (n + 1) d - p : ℕ) : ℚ)) :
    Function.Surjective (pointMultiplication a d) :=
  pointMultiplication_surjective_of_postulation a hd hd1 h
    ((point_count_target_le_source_iff hn hp).mpr hcritical)


/-- The general-points assertion is injective on the lower critical side. -/
theorem idealGenerationAt_injective_open (hn : 1 ≤ n) (hp : p ≤ N (n + 1) d)
    (hcritical : ((N (n + 1) d - p : ℕ) : ℚ) ≤ E (n + 1) d)
    (h : IdealGenerationAt K n d p) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a : PointCoordinates K n p, eval a Δ ≠ 0 →
        DistinctPoints K a ∧
        (∀ j, pointHilbertFunction K a j = min ((n + j).choose j) p) ∧
        Function.Injective (pointMultiplication a d) := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨hdistinct, hpost, hmax⟩ := hgood a ha
  refine ⟨hdistinct, hpost, pointMultiplication_injective_below_critical hn a hp ?_ ?_ hmax hcritical⟩
  · simpa only [N_chart] using hpost d
  · simpa only [N_chart] using hpost (d + 1)

/-- The general-points assertion is surjective on the upper critical side. -/
theorem idealGenerationAt_surjective_open (hn : 1 ≤ n) (hp : p ≤ N (n + 1) d)
    (hcritical : E (n + 1) d ≤ ((N (n + 1) d - p : ℕ) : ℚ))
    (h : IdealGenerationAt K n d p) :
    ∃ Δ : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
      ∀ a : PointCoordinates K n p, eval a Δ ≠ 0 →
        DistinctPoints K a ∧
        (∀ j, pointHilbertFunction K a j = min ((n + j).choose j) p) ∧
        Function.Surjective (pointMultiplication a d) := by
  obtain ⟨Δ, hΔ, hgood⟩ := h
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨hdistinct, hpost, hmax⟩ := hgood a ha
  refine ⟨hdistinct, hpost, pointMultiplication_surjective_above_critical hn a hp ?_ ?_ hmax hcritical⟩
  · simpa only [N_chart] using hpost d
  · simpa only [N_chart] using hpost (d + 1)

end IdealGeneration
