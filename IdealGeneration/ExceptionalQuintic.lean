module

public import IdealGeneration.HigherIntegral
public import IdealGeneration.PlaneCase
public import IdealGeneration.FractionalTraceNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The exceptional four-variable quintic step in Proposition 6.1. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K]

/-- The four-variable quintic exception uses only the preceding quartic assertion. -/
theorem quintic_three_of_quartic
    (hquartic : ∀ p, IdealGenerationAt K 3 4 p) :
    ∀ p, IdealGenerationAt K 3 5 p := by
  have hres : ScalarInjectionAt K 3 4 6 :=
    scalarInjectionAt_of_idealGenerationAt (by omega) 6
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) (hquartic _)
  have hTI : ∃ Δ : MvPolynomial (Fin (N 3 5 - 3) × Fin 2) K,
      (∃ a : PointCoordinates K 2 (N 3 5 - 3), eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 → Function.Injective (pointMultiplication a 5) := by
    obtain ⟨Δ, hΔ, hgood⟩ := plane_residual_open (K := K) 5 3
      (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose])
      (idealGenerationAt_projectivePlane 5 (by omega) _)
    exact ⟨Δ, hΔ, fun a ha => (hgood a ha).2.1⟩
  have hTS : ∃ Δ : MvPolynomial (Fin (N 3 5 - 4) × Fin 2) K,
      (∃ a : PointCoordinates K 2 (N 3 5 - 4), eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 → Function.Surjective (pointEvaluation K a 5) ∧
        Function.Surjective (pointMultiplication a 5) := by
    obtain ⟨Δ, hΔ, hgood⟩ := idealGenerationAt_surjective_open (K := K)
      (n := 2) (d := 5) (by omega) (Nat.sub_le _ _)
      (by norm_num [E, N, Nat.choose])
      (idealGenerationAt_projectivePlane 5 (by omega) (N 3 5 - 4))
    refine ⟨Δ, hΔ, fun a ha => ?_⟩
    obtain ⟨_, hpost, hsurj⟩ := hgood a ha
    have hs : pointHilbertFunction K a 5 = N 3 5 - 4 := by
      simpa only [← N_chart 2 5, min_eq_right (Nat.sub_le _ _)] using hpost 5
    exact ⟨pointEvaluation_surjective_of_hilbert_eq a hs, hsurj⟩
  have hI := ordinary_hyperplane_injective_cell (K := K) (m := 2) (d := 4)
    6 3 (by norm_num [N, Nat.choose]) (by norm_num [N, Nat.choose]) hres hTI
    (by norm_num [N, Nat.choose])
  have hS := ordinary_hyperplane_surjective_cell (K := K) (m := 2) (d := 4)
    6 4 (by norm_num [N, Nat.choose]) (by norm_num [N, Nat.choose]) hres hTS
    (by norm_num [N, Nat.choose])
  have hl : lowerCritical 4 5 = 9 := by
    rw [lowerCritical_successor_trace 4 5 (by omega)]
    norm_num [N, Nat.choose]
  have hu : upperCritical 4 5 = 10 := by
    unfold upperCritical
    apply (Nat.ceil_eq_iff (by decide : 10 ≠ 0)).2
    norm_num [E, N, Nat.choose]
  apply idealGenerationAt_all_of_critical (by omega) (by omega)
  · simpa only [hl] using hI
  · simpa only [hu] using hS

/-- The cubic assertion also supplies the preceding quartic needed by the exception. -/
theorem quintic_three_of_cubic
    (hcubic : ∀ p, IdealGenerationAt K 3 3 p) :
    ∀ p, IdealGenerationAt K 3 5 p := by
  apply quintic_three_of_quartic
  apply integral_hyperplane_transfer_of_maximal_rank (m := 2) (d := 3) 3
    (by omega) (by omega) (by norm_num [E, N, Nat.choose])
  · exact idealGenerationAt_projectivePlane 4 (by omega) _
  · exact hcubic _

end IdealGeneration
