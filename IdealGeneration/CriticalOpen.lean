module

public import IdealGeneration.PointDimensions
public import IdealGeneration.CriticalReduction
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Directional open conditions and their critical-count consequences. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n d : ℕ}

/-- An injective multiplication open with scalar interpolation and specified ideal dimension. -/
def ScalarInjectionAt (K : Type*) [Field K] (n d r : ℕ) : Prop :=
  ∃ Δ : MvPolynomial (Fin (N (n + 1) d - r) × Fin n) K,
    (∃ a : PointCoordinates K n (N (n + 1) d - r), eval a Δ ≠ 0) ∧
    ∀ a, eval a Δ ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
      Function.Injective (pointMultiplication a d) ∧
      finrank K (pointDegreePiece K a d) = r

/-- A single injective witness produces the directional scalar-postulation open. -/
theorem scalarInjectionAt_of_witness [CharZero K] (hn : 1 ≤ n) (r : ℕ)
    (hr : r ≤ N (n + 1) d)
    (a₀ : PointCoordinates K n (N (n + 1) d - r))
    (hi : Function.Injective (pointMultiplication a₀ d)) : ScalarInjectionAt K n d r := by
  obtain ⟨D, hD, hgoodD⟩ := pointMultiplication_injective_principal_open a₀ hi
  obtain ⟨E, hE, hgoodE⟩ := generic_pointHilbertFunction (K := K) hn (N (n + 1) d - r)
  obtain ⟨a, haD, haE⟩ := principal_opens_meet D E ⟨a₀, hD⟩ hE
  refine ⟨D * E, ⟨a, by simpa using mul_ne_zero haD haE⟩, ?_⟩
  intro b hb
  have hparts : eval b D ≠ 0 ∧ eval b E ≠ 0 := by simpa using hb
  have hpost := (hgoodE b hparts.2).2
  have hd : pointHilbertFunction K b d = N (n + 1) d - r := by
    simpa only [← N_chart n d, min_eq_right (Nat.sub_le _ _)] using hpost d
  have hdim : finrank K (pointDegreePiece K b d) = r := by
    rw [pointDegreePiece_finrank b (by simpa only [N_chart] using hpost d)]
    exact Nat.sub_sub_self hr
  exact ⟨pointEvaluation_surjective_of_hilbert_eq b hd, hgoodD b hparts.1, hdim⟩

/-- Adding points reduces the ideal dimension and preserves the injection open. -/
theorem scalarInjectionAt_mono [CharZero K] (hn : 1 ≤ n) {r s : ℕ}
    (hrs : r ≤ s) (hs : s ≤ N (n + 1) d)
    (h : ScalarInjectionAt K n d s) : ScalarInjectionAt K n d r := by
  obtain ⟨D, ⟨a, ha⟩, hgood⟩ := h
  have hi := (hgood a ha).2.1
  have hcounts : N (n + 1) d - s ≤ N (n + 1) d - r := by omega
  let b := extendPoints a (N (n + 1) d - r)
  have hb : Function.Injective (pointMultiplication b d) := by
    apply pointMultiplication_injective_of_restriction b (Fin.castLE hcounts)
    rw [show restrictPoints b (Fin.castLE hcounts) = a from restrict_extendPoints a hcounts]
    exact hi
  exact scalarInjectionAt_of_witness hn r (hrs.trans hs) b hb

/-- A maximal-rank assertion on the injective side supplies the directional open. -/
theorem scalarInjectionAt_of_idealGenerationAt (hn : 1 ≤ n) (r : ℕ)
    (hr : r ≤ N (n + 1) d) (hc : (r : ℚ) ≤ E (n + 1) d)
    (h : IdealGenerationAt K n d (N (n + 1) d - r)) : ScalarInjectionAt K n d r := by
  obtain ⟨D, hD, hgood⟩ := idealGenerationAt_injective_open hn (Nat.sub_le _ _)
    (by simpa only [Nat.sub_sub_self hr] using hc) h
  refine ⟨D, hD, fun a ha => ?_⟩
  obtain ⟨_, hpost, hi⟩ := hgood a ha
  have hd : pointHilbertFunction K a d = N (n + 1) d - r := by
    simpa only [← N_chart n d, min_eq_right (Nat.sub_le _ _)] using hpost d
  have hdim : finrank K (pointDegreePiece K a d) = r := by
    rw [pointDegreePiece_finrank a (by simpa only [N_chart] using hpost d)]
    exact Nat.sub_sub_self hr
  exact ⟨pointEvaluation_surjective_of_hilbert_eq a hd, hi, hdim⟩

/-- The lower critical general-points assertion supplies an injective witness. -/
theorem critical_injective_witness (hn : 1 ≤ n) (hd : 1 ≤ d)
    (h : IdealGenerationAt K n d (N (n + 1) d - lowerCritical (n + 1) d)) :
    ∃ a : PointCoordinates K n (N (n + 1) d - lowerCritical (n + 1) d),
      Function.Injective (pointMultiplication a d) := by
  have hr : lowerCritical (n + 1) d ≤ N (n + 1) d := by
    have hh := (lowerCritical_mem_cell (n + 1) d (by omega) hd).2
    omega
  have hc : (lowerCritical (n + 1) d : ℚ) ≤ E (n + 1) d :=
    (le_E_iff_le_lowerCritical _ _ _).mpr le_rfl
  obtain ⟨D, ⟨a, ha⟩, hgood⟩ := scalarInjectionAt_of_idealGenerationAt hn _ hr hc h
  exact ⟨a, (hgood a ha).2.1⟩

/-- The upper critical general-points assertion supplies a scalar-postulated surjective witness. -/
theorem critical_surjective_witness (hn : 1 ≤ n) (hd : 1 ≤ d)
    (h : IdealGenerationAt K n d (N (n + 1) d - upperCritical (n + 1) d)) :
    ∃ a : PointCoordinates K n (N (n + 1) d - upperCritical (n + 1) d),
      Function.Surjective (pointEvaluation K a d) ∧
      Function.Surjective (pointMultiplication a d) := by
  have hr : upperCritical (n + 1) d ≤ N (n + 1) d := by
    have hh := (upperCritical_mem_cell (n + 1) d (by omega) hd).2
    omega
  have hp := Nat.sub_le (N (n + 1) d) (upperCritical (n + 1) d)
  obtain ⟨D, ⟨a, ha⟩, hgood⟩ := idealGenerationAt_surjective_open hn hp
    (by rw [Nat.sub_sub_self hr]; exact (E_le_iff_upperCritical_le _ _ _).mpr le_rfl) h
  obtain ⟨_, hpost, hsurj⟩ := hgood a ha
  have hd' : pointHilbertFunction K a d = N (n + 1) d - upperCritical (n + 1) d := by
    simpa only [← N_chart n d, min_eq_right hp] using hpost d
  exact ⟨a, pointEvaluation_surjective_of_hilbert_eq a hd', hsurj⟩

/-- Maximal rank at the two critical counts gives every point count. -/
theorem idealGenerationAt_all_of_critical [CharZero K] (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hI : IdealGenerationAt K n d (N (n + 1) d - lowerCritical (n + 1) d))
    (hS : IdealGenerationAt K n d (N (n + 1) d - upperCritical (n + 1) d)) :
    ∀ p, IdealGenerationAt K n d p :=
  reduction_to_critical_counts hn (critical_injective_witness hn hd hI)
    (critical_surjective_witness hn hd hS)

end IdealGeneration
