module

public import IdealGeneration.TwoNormalIntegralMarkedTransfer
public import IdealGeneration.TwoNormalIntegralCountAssembly

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimensions of the actual ambient Euler fiber problem

Each normalized Euler fiber loses one coordinate. The source dimension is
rank-nullity for the onto Euler product map, so their signed difference is
exactly the critical discrepancy in the paper.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module TwoNormalSlice
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q p : ℕ}

/-- Normalized point representatives have `n` independent Euler coordinates each. -/
theorem traceFibers_finrank_of_last_one (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) : finrank K (TraceFibers z) = n * p := by
  have hs : Function.Surjective (traceFiberDot z) :=
    fun v => ⟨insertLastComponent n v, traceFiberDot_insertLast z hz v⟩
  have h := (traceFiberDot z).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
  have hp : finrank K (Fin p → K) = p := by simp
  have hdim : finrank K (Fin p → Fin (n + 1) → K) = (n + 1) * p := by
    simp [Module.finrank_pi_fintype, Nat.mul_comm]
  rw [hp, hdim, Nat.add_mul, one_mul] at h
  change p + finrank K (TraceFibers z) = n * p + p at h
  omega

/-- Embedding a normalized trace point into the ambient space preserves its last coordinate. -/
theorem commonTracePoint_chart_last (z : PointCoordinates K n p) (i : Fin p) :
    commonTracePoint (chartPoint K z i) (Fin.last (n + 2)) = 1 := by
  rw [show Fin.last (n + 2) = (Fin.last n).succ.succ by rfl]
  simp [commonTracePoint]

/-- The dimension of the genuine four-group ambient Euler target. -/
theorem marked_ambientFiber_finrank (a b' : PointCoordinates K (n + 1) b)
    (x : PointCoordinates K (n + 2) q) (z : PointCoordinates K n p) :
    finrank K (AmbientFiberValues a b' (chartPoint K z) (chartPoint K x)) =
      (n + 2) * (b + (b + (q + p))) := by
  have ha (i : Fin b) : ambientPointA a i (Fin.last (n + 2)) = 1 := by
    rw [show Fin.last (n + 2) = (Fin.last n).succ.succ by rfl]
    simp [ambientPointA]
  have hb (i : Fin b) : ambientPointB b' i (Fin.last (n + 2)) = 1 := by
    rw [show Fin.last (n + 2) = (Fin.last n).succ.succ by rfl]
    simp [ambientPointB]
  have hz (i : Fin p) : ambientTracePoint (chartPoint K z) i (Fin.last (n + 2)) = 1 :=
    commonTracePoint_chart_last z i
  change finrank K (TraceFibers (ambientPointA a) × (TraceFibers (ambientPointB b') ×
    (TraceFibers (ambientTracePoint (chartPoint K z)) × TraceFibers (chartPoint K x)))) = _
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    traceFibers_finrank_of_last_one _ ha, traceFibers_finrank_of_last_one _ hb,
    traceFibers_finrank_of_last_one _ hz,
    traceFibers_finrank_of_last_one (chartPoint K x) (chartPoint_last x)]
  ring

/-- The Euler source minus fiber-target count is the signed discrepancy (2.4). -/
theorem ambientEuler_discrepancy [CharZero K] (n d r p : ℕ)
    (hr : r ≤ N (n + 3) (d + 1 + 1))
    (hp : p = N (n + 3) (d + 1 + 1) - r) :
    (((finrank K (AmbientEuler K (n + 1) d) : ℤ) - ((n + 2) * p : ℕ) : ℤ) : ℚ) =
      ((n : ℚ) + 2) * criticalDeviation (n + 1) (d + 1 + 1) r := by
  let D := d + 1 + 1
  have hsource : N (n + 3) (D + 1) + finrank K (AmbientEuler K (n + 1) d) =
      (n + 3) * N (n + 3) D := by
    have h := (formMultiplication K (n + 3) D).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (formMultiplication_surjective (n + 3) D), finrank_top] at h
    have hdom : finrank K (Fin (n + 3) → Forms K (n + 3) D) = (n + 3) * N (n + 3) D := by
      simp [Module.finrank_pi_fintype, finrank_forms, N]
    have htgt : finrank K (Forms K (n + 3) (D + 1)) = N (n + 3) (D + 1) :=
      finrank_forms K (n + 3) (D + 1)
    rw [hdom, htgt] at h
    exact h
  have hsourceQ : (N (n + 3) (D + 1) : ℚ) + finrank K (AmbientEuler K (n + 1) d) =
      ((n : ℚ) + 3) * N (n + 3) D := by exact_mod_cast hsource
  have hpQ : (p : ℚ) = (N (n + 3) D : ℚ) - r := by
    rw [hp, Nat.cast_sub hr]
  have hdim := multiplication_dimension_difference_points (n + 3) D p (by omega)
  rw [hpQ] at hdim
  push_cast at hdim ⊢
  change (finrank K (AmbientEuler K (n + 1) d) : ℚ) - ((n : ℚ) + 2) * p =
    ((n : ℚ) + 2) * ((r : ℚ) - E (n + 3) D)
  nlinarith [hsourceQ, hdim, hpQ]

end IdealGeneration.TwoNormalIntegral
