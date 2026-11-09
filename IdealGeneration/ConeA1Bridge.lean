module

public import IdealGeneration.ConeMiddleOpen
public import IdealGeneration.ConeChart
public import IdealGeneration.PointDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The marked-cone trace induction step

A special witness for the middle map and a separate inductive trace theorem
give a common marked cone. At the balanced trace count, the trace block is
bijective, and the cone splitting and chart transport give the ambient
ideal-generation assertion.
-/

noncomputable section
namespace IdealGeneration.ConeA1Bridge
open MvPolynomial Module ConeParameterSpace ConeMiddleFamily
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {c m p q : ℕ}

/-- Separate full scalar evaluation on the trace and normal-ideal spaces
gives the expected scalar dimension of the split union. -/
theorem scalar_finrank_of_full_evaluation (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) (hpost : FullEvaluation support a d) :
    finrank K ((configuration support a).tracePiece d) +
      finrank K ((configuration support a).residualPiece d) + (p + q) =
        finrank K (Forms K (c + m) d) := by
  have htrace := TwoGroup.rank_nullity_monoid (K := K)
    (U := Forms K m d) (C := Fin q → K) (traceEvaluation a d)
  rw [LinearMap.range_eq_top.mpr hpost.2.1, finrank_top, traceEvaluation_ker support a d] at htrace
  have hnormal := TwoGroup.rank_nullity_monoid (K := K)
    (U := normalForms K c m d) (C := Fin p → K) (normalEvaluation support a d)
  rw [LinearMap.range_eq_top.mpr hpost.1, finrank_top,
    ← (normalKernelEquiv support a d).finrank_eq] at hnormal
  have hpdim : finrank K (Fin p → K) = p := by simp
  have hqdim : finrank K (Fin q → K) = q := by simp
  rw [hqdim] at htrace
  rw [hpdim] at hnormal
  have honto : Function.Surjective (coneRestrictForm K c m d) :=
    fun f => ⟨coneExtendForm K c m d f, coneRestrictForm_extendForm K c m f⟩
  have hsplit := TwoGroup.rank_nullity_monoid (K := K)
    (U := Forms K (c + m) d) (C := Forms K m d) (coneRestrictForm K c m d)
  rw [LinearMap.range_eq_top.mpr honto, finrank_top] at hsplit
  change finrank K (Forms K m d) + finrank K (normalForms K c m d) = _ at hsplit
  omega

/-- Rescaling trace representatives preserves bijectivity of their block. -/
theorem traceMultiplication_bijective_of_chart {n : ℕ} (support : Fin p → Fin q)
    (a : Parameters K c (n + 1) p q) (d : ℕ)
    (hlast : ∀ i, traceCoordinates a (i, Fin.last n) ≠ 0)
    (h : Function.Bijective
      (pointMultiplication (HomogeneousTraceOpen.normalize (traceCoordinates a)) d)) :
    Function.Bijective ((configuration support a).traceMultiplication d) := by
  let z := (configuration support a).trace
  have hz : ∀ i, z i (Fin.last n) ≠ 0 := hlast
  exact ⟨(normalization_multiplication_injective_iff (d := d) z hz).mpr h.1,
    (normalization_multiplication_surjective_iff (d := d) z hz).mpr h.2⟩

/-- Appendix A.1. A middle-map witness with scalar postulation can be chosen
together with the independently given inductive trace open. At a balanced
trace count this produces the ambient general-points assertion. -/
theorem idealGenerationAt_of_special_middle [CharZero K] {n : ℕ}
    (hc : 0 < c) (hAmbient : 2 ≤ c + (n + 1)) (support : Fin p → Fin q)
    (a₀ : Parameters K c (n + 1) p q) (d : ℕ)
    (hpoint : ∀ i, (configuration support a₀).point i ≠ 0)
    (hnormal : Function.Surjective (normalEvaluation support a₀ d))
    (htrace : Function.Surjective (traceEvaluation a₀ d))
    (hmiddle : HasMaximalRank ((configuration support a₀).middleMultiplication d))
    (hbalance : (n + 1) * (N (n + 1) d - q) = N (n + 1) (d + 1) - q)
    (hinduction : IdealGenerationAt K n d q) :
    IdealGenerationAt K (c + (n + 1) - 1) d (p + q) := by
  obtain ⟨D, hD, hDgood⟩ := hinduction
  let j : Fin p → Fin c := fun _ => ⟨0, hc⟩
  obtain ⟨a, hpost, hmid, hlast, hDtrace, hnormalCoords, _⟩ :=
    exists_middle_affine_trace_open support a₀ d
      (fullEvaluation_of_degree support a₀ d hpoint hnormal htrace) hmiddle j D hD
  let C := configuration support a
  have hnz : ∀ i, C.normal i ≠ 0 := by
    intro i hi
    exact hnormalCoords i (congrFun hi (j i))
  have htz : ∀ i, C.trace i ≠ 0 := by
    intro i hi
    exact hlast i (congrFun hi (Fin.last n))
  let t := HomogeneousTraceOpen.normalize (traceCoordinates a)
  obtain ⟨_, hpostTrace, htraceMax⟩ := hDgood t hDtrace
  have hd : pointHilbertFunction K t d = min (N (n + 1) d) q := by
    rw [N_chart]
    exact hpostTrace d
  have hd1 : pointHilbertFunction K t (d + 1) = min (N (n + 1) (d + 1)) q := by
    rw [N_chart]
    exact hpostTrace (d + 1)
  have htbij : Function.Bijective (C.traceMultiplication d) :=
    traceMultiplication_bijective_of_chart support a d hlast
      ⟨pointMultiplication_injective_of_postulation t hd hd1 htraceMax hbalance.le,
        pointMultiplication_surjective_of_postulation t hd hd1 htraceMax hbalance.symm.le⟩
  exact C.idealGenerationAt_of_middle hAmbient (C.representatives_ne_zero hnz htz)
    (scalar_finrank_of_full_evaluation support a d hpost) htbij hmid

end IdealGeneration.ConeA1Bridge
