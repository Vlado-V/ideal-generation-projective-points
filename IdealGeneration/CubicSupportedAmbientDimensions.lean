module

public import IdealGeneration.CubicSupportedGraph
public import Mathlib.Data.Fintype.Prod

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The two dimension counts for the supported cubic coefficient chart. -/

namespace IdealGeneration.CubicSupported

open Module

/-- Increasing pairs are counted by the two-element subsets of the trace coordinates. -/
theorem card_edge (m : ℕ) : Fintype.card (Edge m) = m.choose 2 := by
  change Fintype.card {p : Fin m × Fin m // p.1 < p.2} = _
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- Ordered pairs consist of both orientations of each edge and the diagonal. -/
theorem two_mul_card_edge_add (m : ℕ) : 2 * Fintype.card (Edge m) + m = m * m := by
  cases m with
  | zero => simp
  | succ m =>
    have h : (m + 1) * m = (m + 1).choose 2 * 2 := by
      simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq m 1
    rw [card_edge]
    change 2 * (m + 1).choose 2 + (m + 1) = (m + 1) * (m + 1)
    rw [Nat.mul_comm 2, ← h]
    ring

private theorem choose_cubic_difference (m : ℕ) :
    (2 + m + 3 - 1).choose 3 = (m + 3 - 1).choose 3 + (m + 2) ^ 2 := by
  rw [Nat.add_comm 2 m]
  change (m + 2 + 1 + 1).choose 3 = (m + 2).choose 3 + (m + 2) ^ 2
  rw [Nat.choose_succ_succ' (m + 2 + 1) 2, Nat.choose_succ_succ' (m + 2) 2,
    Nat.choose_succ_succ' (m + 2) 1, Nat.choose_one_right]
  have h : (m + 2) * (m + 1) = (m + 2).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (m + 1) 1
  rw [show (m + 2) ^ 2 = (m + 2) * (m + 1) + (m + 2) by ring, h]
  norm_num
  omega

/-- Cubic forms with zero trace have dimension `(m+2)^2`. -/
theorem finrank_cubic_restriction_ker (K : Type*) [Field K] (m : ℕ) :
    finrank K (LinearMap.ker (coneRestrictForm K 2 m 3)) = (m + 2) ^ 2 := by
  have honto : Function.Surjective (coneRestrictForm K 2 m 3) :=
    fun f => ⟨coneExtendForm K 2 m 3 f, coneRestrictForm_extendForm K 2 m f⟩
  have hdim := (coneRestrictForm K 2 m 3).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr honto, finrank_top, finrank_forms K m 3,
    finrank_forms K (2 + m) 3, choose_cubic_difference] at hdim
  omega

end IdealGeneration.CubicSupported
