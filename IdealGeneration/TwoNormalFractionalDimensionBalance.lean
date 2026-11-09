module

public import IdealGeneration.TwoNormalFractionalNumerics
public import IdealGeneration.PointDimensions
public import IdealGeneration.TwoNormalFractionalKernel
public import IdealGeneration.TwoNormalIntegralAssembly

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Fractional trace dimension balance for the actual evaluation maps

The numerical identities apply to the actual Euler relation source, Euler
fibers, residual pair kernel, and both slice quotient codes.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module TwoNormalTrace TwoNormalSlice TwoNormalIntegral

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n m b q k d : ℕ}

private theorem finrank_forms_of_pos (n d : ℕ) (hn : 0 < n) :
    finrank K (Forms K n d) = N n d := by
  cases n with
  | zero => omega
  | succ n => rw [finrank_chart_forms, N_chart]

/-- The dimension of the homogeneous Euler relation source, without subtraction. -/
theorem eulerRelation_finrank_add [CharZero K] (n d : ℕ) (hn : 0 < n) :
    finrank K (HyperplaneEuler.Relations K n d) + N n (d + 1) = n * N n d := by
  have h := TwoGroup.rank_nullity_monoid (formMultiplication K n d)
  rw [LinearMap.range_eq_top.mpr (formMultiplication_surjective (K := K) n d), finrank_top] at h
  change finrank K (Forms K n (d + 1)) + finrank K (HyperplaneEuler.Relations K n d) =
    finrank K (Fin n → Forms K n d) at h
  rw [Module.finrank_pi_fintype, finrank_forms_of_pos n (d + 1) hn,
    finrank_forms_of_pos n d hn] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, add_comm] using h

/-- A fixed nonzero coordinate makes the Euler contraction onto at every point. -/
theorem traceFibers_finrank_of_coordinate (z : Fin q → Fin n → K)
    (j₀ : Fin n) (hz : ∀ i, z i j₀ ≠ 0) :
    finrank K (TraceFibers z) = (n - 1) * q := by
  classical
  have hs : Function.Surjective (traceFiberDot z) := by
    intro v
    refine ⟨fun i j => if j = j₀ then v i / z i j₀ else 0, ?_⟩
    funext i
    change (∑ j, z i j * (if j = j₀ then v i / z i j₀ else 0)) = v i
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_comm, div_mul_cancel₀ _ (hz i)]
  have h := (traceFiberDot z).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
  change finrank K (Fin q → K) + finrank K (TraceFibers z) =
    finrank K (Fin q → Fin n → K) at h
  have h₁ : finrank K (Fin q → K) = q := by simp
  have h₂ : finrank K (Fin q → Fin n → K) = q * n := by simp [Module.finrank_pi_fintype]
  rw [h₁, h₂] at h
  cases n with
  | zero => exact Fin.elim0 j₀
  | succ n =>
      simp only [Nat.succ_sub_one]
      rw [Nat.mul_succ] at h
      rw [Nat.mul_comm n q]
      omega

private theorem pointPiece_finrank_of_scalar (x : PointCoordinates K n q) (d : ℕ)
    (hs : Function.Surjective (pointEvaluation K x d)) :
    finrank K (pointDegreePiece K x d) + q = N (n + 1) d := by
  have h := (pointEvaluation K x d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
  change finrank K (Fin q → K) + finrank K (pointDegreePiece K x d) =
    finrank K (Forms K (n + 1) d) at h
  rw [finrank_forms_of_pos (n + 1) d (by omega)] at h
  simpa only [show finrank K (Fin q → K) = q by simp, add_comm] using h

/-- Surjective scalar pair evaluation yields the exact normal kernel count
from the two residual ideal dimensions. -/
theorem pairEvaluation_kernel_finrank_of_surjective
    (a c : PointCoordinates K m b) (x : PointCoordinates K (m + 1) q)
    (hs : Function.Surjective (pairEvaluation K m a c x d)) :
    finrank K (pairEvaluation K m a c x d).ker + (b + b) =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1)) := by
  let : AddCommGroup (pointDegreePiece K x d) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (pointDegreePiece K x (d + 1)) := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K (pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  let : Module.Free K (pointDegreePiece K x (d + 1)) := Module.Free.of_divisionRing K _
  let : Module.Free K (Fin m → pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  have h := TwoGroup.rank_nullity_monoid (pairEvaluation K m a c x d)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
  change finrank K ((Fin b → K) × (Fin b → K)) +
    finrank K (pairEvaluation K m a c x d).ker = finrank K (ResidualParameters K m x d) at h
  have h₁ : finrank K ((Fin b → K) × (Fin b → K)) = b + b := by
    rw [Module.finrank_prod]
    simp
  have h₂ : finrank K (ResidualParameters K m x d) =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1)) := by
    unfold ResidualParameters
    rw [Module.finrank_prod, Module.finrank_pi_fintype]
    simp
  rw [h₁, h₂] at h
  exact (add_comm _ _).trans h

/-- The numerical counts in Proposition 5.1 give the precise balance needed
by the marked Euler motion. -/
theorem fractional_marked_dimension_balance [CharZero K]
    (r : ℕ) (hD : 4 ≤ d + 1 + 1)
    (hm : (d + 1 + 1) * (d + 1 + 1 - 1) < m)
    (hr : r = lowerCritical (m + 2) (d + 1 + 1) ∨ r = upperCritical (m + 2) (d + 1 + 1))
    (a c : PointCoordinates K m b) (x : PointCoordinates K (m + 1) q)
    (z : Fin k → Fin m → K)
    (hb : b = sliceCount m (d + 1 + 1))
    (hq : q = offSlicePointCount m (d + 1 + 1) r)
    (hk : k = tracePointCount m (d + 1 + 1))
    (hc : SliceConditions a c z d)
    (j₀ : Fin m) (hz : ∀ i, z i j₀ ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1 + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a (d + 1)))
    (hscalarB : Function.Surjective (pointEvaluation K c (d + 1)))
    (hscalarG : Function.Surjective (pointEvaluation K x d))
    (hscalarH : Function.Surjective (pointEvaluation K x (d + 1)))
    (hpair : Function.Surjective (pairEvaluation K m a c x d)) :
    (finrank K (traceFiberEvaluation z (d + 1 + 1)).ker : ℤ) +
        finrank K (pairEvaluation K m a c x d).ker -
        ((finrank K (AmbientEuler K m d) : ℤ) -
          finrank K (AmbientFiberValues a c z (chartPoint K x))) =
      (finrank K (TraceProductQuotient a z (d + 1)) : ℤ) +
        finrank K (TraceProductQuotient c z (d + 1)) := by
  let D := d + 1 + 1
  change b = sliceCount m D at hb
  change q = offSlicePointCount m D r at hq
  change k = tracePointCount m D at hk
  have hm₂ : 2 ≤ m := by
    have h := (fractional_dimension_bounds m D hD hm).1
    omega
  have hrLe : r ≤ N (m + 2) D := by
    rcases hr with hr | hr
    · exact hr ▸ (lowerCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
    · exact hr ▸ (upperCritical_mem_cell (m + 2) D (by omega) (by omega)).2.trans (Nat.sub_le _ _)
  have htr := TwoGroup.rank_nullity_monoid (traceFiberEvaluation z D)
  rw [LinearMap.range_eq_top.mpr htrace, finrank_top, traceFibers_finrank_of_coordinate z j₀ hz,
    congrArg (fun p => (m - 1) * p) hk] at htr
  have htrS := eulerRelation_finrank_add (K := K) m D (by omega)
  have htrQ : (finrank K (traceFiberEvaluation z D).ker : ℚ) = traceKernel m D := by
    have h₁ := congrArg (fun a : ℕ => (a : ℚ)) htr
    have h₂ := congrArg (fun a : ℕ => (a : ℚ)) htrS
    push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at h₁ h₂
    linarith [trace_kernel_from_counts m D hm₂ (by omega)]
  have hAf := traceFibers_finrank_of_coordinate (ambientPointA a) 0 hc.normalA
  have hBf := traceFibers_finrank_of_coordinate (ambientPointB c)
    (0 : Fin (m + 1)).succ hc.normalB
  have hZf := traceFibers_finrank_of_coordinate (ambientTracePoint z) j₀.succ.succ hz
  have hXf := traceFibers_finrank_of_coordinate (chartPoint K x) (Fin.last (m + 1))
    (fun i => by simp)
  have hAmbF : finrank K (AmbientFiberValues a c z (chartPoint K x)) =
      (m + 1) * ambientPointCount m D r := by
    have hCount : b + (b + (k + q)) = ambientPointCount m D r := by
      rw [ambientPointCount_decomposition m D r hD hm hr, ← hb, ← hq, ← hk]
      omega
    calc
      _ = (m + 1) * (b + (b + (k + q))) := by
        unfold AmbientFiberValues
        rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, hAf, hBf, hZf, hXf]
        change (m + 1) * b + ((m + 1) * b + ((m + 1) * k + (m + 1) * q)) = _
        ring
      _ = _ := congrArg (fun p => (m + 1) * p) hCount
  have hAmbS := eulerRelation_finrank_add (K := K) (m + 2) D (by omega)
  have hAmbQ : (finrank K (AmbientEuler K m d) : ℚ) -
      finrank K (AmbientFiberValues a c z (chartPoint K x)) = ambientDiscrepancy m D r := by
    have h₁ := congrArg (fun a : ℕ => (a : ℚ)) hAmbS
    have h₂ := congrArg (fun a : ℕ => (a : ℚ)) hAmbF
    push_cast at h₁ h₂
    change (finrank K (AmbientEuler K m d) : ℚ) + N (m + 2) (D + 1) =
      ((m : ℚ) + 2) * N (m + 2) D at h₁
    linarith [ambient_discrepancy_from_counts m D r hrLe]
  have hG := pointPiece_finrank_of_scalar x d hscalarG
  have hH := pointPiece_finrank_of_scalar x (d + 1) hscalarH
  have hG' : finrank K (pointDegreePiece K x d) = residualCount m D r := by
    change finrank K (pointDegreePiece K x d) = N (m + 2) d - offSlicePointCount m D r
    apply Nat.eq_sub_of_add_eq
    rw [← hq]
    exact hG
  have hH' : finrank K (pointDegreePiece K x (d + 1)) =
      N (m + 1) (d + 1) + residualCount m D r := by
    have hP : N (m + 2) (d + 1) = N (m + 1) (d + 1) + N (m + 2) d :=
      N_pascal (m + 2) (d + 1) (by omega) (by omega)
    rw [hP, ← hG, hG'] at hH
    omega
  have hPair := pairEvaluation_kernel_finrank_of_surjective a c x hpair
  rw [hG', hH'] at hPair
  have hPair' : finrank K (pairEvaluation K m a c x d).ker =
      N (m + 1) (D - 1) + (m + 1) * residualCount m D r - 2 * sliceCount m D := by
    change finrank K (pairEvaluation K m a c x d).ker =
      N (m + 1) (d + 1) + (m + 1) * residualCount m D r - 2 * sliceCount m D
    apply Nat.eq_sub_of_add_eq
    rw [two_mul, ← hb, hPair]
    ring
  have hcasts := kernelCounts_cast m D r hD hm hr
  have hPairQ : (finrank K (pairEvaluation K m a c x d).ker : ℚ) =
      normalKernelDimension m D r := by
    rw [hPair']
    exact hcasts.2
  have hQA := traceProductQuotient_finrank a z (d + 1) hc.normalA hscalarA hc.multA hc.codeA
  have hQB := traceProductQuotient_finrank c z (d + 1) hc.normalB hscalarB hc.multB hc.codeB
  rw [finrank_forms_of_pos (m + 1) (d + 1) (by omega)] at hQA hQB
  have hQAQ : (finrank K (TraceProductQuotient a z (d + 1)) : ℚ) = sliceCokernel m D := by
    rw [hQA, hk, hb]
    exact hcasts.1
  have hQBQ : (finrank K (TraceProductQuotient c z (d + 1)) : ℚ) = sliceCokernel m D := by
    rw [hQB, hk, hb]
    exact hcasts.1
  have hQ : (finrank K (traceFiberEvaluation z D).ker : ℚ) +
        finrank K (pairEvaluation K m a c x d).ker -
        ((finrank K (AmbientEuler K m d) : ℚ) -
          finrank K (AmbientFiberValues a c z (chartPoint K x))) =
      (finrank K (TraceProductQuotient a z (d + 1)) : ℚ) +
        finrank K (TraceProductQuotient c z (d + 1)) := by
    rw [htrQ, hPairQ, hAmbQ, hQAQ, hQBQ]
    linarith [normal_kernel_identity m D r (by omega) (by omega)]
  exact_mod_cast hQ

end IdealGeneration.TwoNormalFractional
