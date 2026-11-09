module

public import IdealGeneration.IntegralTraceNumerics
public import IdealGeneration.OrdinaryHyperplaneGeneric
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The integral-trace corollary of ordinary hyperplane specialization. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K]

/-- Corollary 3.2. An integral trace critical value and the single ceiling
residual injection imply maximal rank for every ambient point count. -/
theorem integral_hyperplane_transfer (m d r₂ : ℕ) (hm : 1 ≤ m)
    (htrace : E (m + 1) (d + 1) = (r₂ : ℚ))
    (hG : IdealGenerationAt K m (d + 1) (N (m + 1) (d + 1) - r₂))
    (hres : ScalarInjectionAt K (m + 1) d
      ⌈hyperplaneResidualRatio (m + 2) (d + 1)⌉₊) :
    ∀ p, IdealGenerationAt K (m + 1) (d + 1) p := by
  let rI := ⌊hyperplaneResidualRatio (m + 2) (d + 1)⌋₊
  let rS := ⌈hyperplaneResidualRatio (m + 2) (d + 1)⌉₊
  have htrace' : E (m + 2 - 1) (d + 1) = (r₂ : ℚ) := by simpa using htrace
  have hr₂ : r₂ ≤ N (m + 1) (d + 1) := by
    have hc := (integral_trace_mem_cell (m + 2) (d + 1) r₂ (by omega) (by omega) htrace').2
    have hc' : r₂ ≤ N (m + 1) (d + 1) - N (m + 1) d := by simpa using hc
    omega
  have hrS : rS ≤ N (m + 2) d := by
    obtain ⟨D, ⟨a, ha⟩, hgood⟩ := hres
    have hdim := (hgood a ha).2.2
    have hbound := Submodule.finrank_le (pointDegreePiece K a d)
    rw [hdim, finrank_chart_forms] at hbound
    simpa only [← N_chart (m + 1) d] using hbound
  have hIS : rI ≤ rS := Nat.floor_le_ceil _
  have hrI : rI ≤ N (m + 2) d := hIS.trans hrS
  have hresI : ScalarInjectionAt K (m + 1) d rI :=
    scalarInjectionAt_mono (by omega) hIS hrS hres
  have hTI : ∃ D : MvPolynomial (Fin (N (m + 1) (d + 1) - r₂) × Fin m) K,
      (∃ b : PointCoordinates K m (N (m + 1) (d + 1) - r₂), eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Injective (pointMultiplication b (d + 1)) := by
    obtain ⟨D, hD, hgood⟩ := idealGenerationAt_injective_open hm (Nat.sub_le _ _)
      (by rw [Nat.sub_sub_self hr₂]; exact le_of_eq htrace.symm) hG
    exact ⟨D, hD, fun b hb => (hgood b hb).2.2⟩
  have hTS : ∃ D : MvPolynomial (Fin (N (m + 1) (d + 1) - r₂) × Fin m) K,
      (∃ b : PointCoordinates K m (N (m + 1) (d + 1) - r₂), eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Surjective (pointEvaluation K b (d + 1)) ∧
        Function.Surjective (pointMultiplication b (d + 1)) := by
    obtain ⟨D, hD, hgood⟩ := idealGenerationAt_surjective_open hm (Nat.sub_le _ _)
      (by rw [Nat.sub_sub_self hr₂]; exact le_of_eq htrace) hG
    refine ⟨D, hD, fun b hb => ?_⟩
    obtain ⟨_, hpost, hsurj⟩ := hgood b hb
    have hs : pointHilbertFunction K b (d + 1) = N (m + 1) (d + 1) - r₂ := by
      simpa only [← N_chart m (d + 1), min_eq_right (Nat.sub_le _ _)] using hpost (d + 1)
    exact ⟨pointEvaluation_surjective_of_hilbert_eq b hs, hsurj⟩
  have hGI : IdealGenerationAt K (m + 1) (d + 1)
      (N (m + 2) (d + 1) - lowerCritical (m + 2) (d + 1)) := by
    have hb : (m + 1) * rI + r₂ ≤ N (m + 1) (d + 1) := by
      simpa only [show m + 2 - 1 = m + 1 by omega] using
        integral_trace_floor_budget (m + 2) (d + 1) r₂ (by omega) (by omega) htrace'
    have hh := ordinary_hyperplane_injective_cell rI r₂ hrI hr₂ hresI hTI hb
    have hcrit := lowerCritical_integral_trace (m + 2) (d + 1) r₂
      (by omega) (by omega) htrace'
    simpa only [hcrit, Nat.add_comm] using hh
  have hGS : IdealGenerationAt K (m + 1) (d + 1)
      (N (m + 2) (d + 1) - upperCritical (m + 2) (d + 1)) := by
    have hb : N (m + 1) (d + 1) ≤ (m + 1) * rS + r₂ := by
      simpa only [show m + 2 - 1 = m + 1 by omega] using
        integral_trace_ceil_budget (m + 2) (d + 1) r₂ (by omega) (by omega) htrace'
    have hh := ordinary_hyperplane_surjective_cell rS r₂ hrS hr₂ hres hTS hb
    have hcrit := upperCritical_integral_trace (m + 2) (d + 1) r₂
      (by omega) (by omega) htrace'
    simpa only [hcrit, Nat.add_comm] using hh
  exact idealGenerationAt_all_of_critical (by omega) (by omega) hGI hGS

end IdealGeneration
