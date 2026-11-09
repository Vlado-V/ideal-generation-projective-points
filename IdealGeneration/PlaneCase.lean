module

public import IdealGeneration.OrdinaryHyperplaneGeneric
public import IdealGeneration.PlaneArithmetic
public import IdealGeneration.PointDimensions
public import IdealGeneration.Binary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The projective-plane case

The proof uses ordinary hyperplane specialization with a projective-line trace.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- The projective-line trace supplies both ranks on the same scalar open. -/
theorem plane_trace_open [CharZero K] (D : ℕ) :
    ∃ Δ : MvPolynomial (Fin D × Fin 1) K,
      (∃ a : PointCoordinates K 1 D, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        Function.Surjective (pointEvaluation K a D) ∧
        Function.Injective (pointMultiplication a D) ∧
        Function.Surjective (pointMultiplication a D) := by
  obtain ⟨Δ, hΔ, hgood⟩ := generic_pointHilbertFunction (K := K) (n := 1) (by omega) D
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost⟩ := hgood a ha
  have hd : pointHilbertFunction K a D = D := by
    have hc : (1 + D).choose D = D + 1 := by
      rw [Nat.add_comm, Nat.choose_succ_self_right]
    simpa only [hc, min_eq_right (Nat.le_succ D)] using hpost D
  have hd1 : pointHilbertFunction K a (D + 1) = D := by
    have hc : (1 + (D + 1)).choose (D + 1) = D + 2 := by
      rw [Nat.add_comm 1 (D + 1), Nat.choose_succ_self_right]
    simpa only [hc, min_eq_right (by omega : D ≤ D + 2)] using hpost (D + 1)
  have hdim : finrank K (pointDegreePiece K a D) = 1 := by
    have h := (pointDegreePiece K a D).finrank_quotient_add_finrank
    rw [finrank_chart_forms] at h
    change pointHilbertFunction K a D + _ = _ at h
    rw [hd] at h
    have hc : (1 + D).choose D = D + 1 := by
      rw [Nat.add_comm, Nat.choose_succ_self_right]
    rw [hc] at h
    omega
  exact ⟨pointEvaluation_surjective_of_hilbert_eq a hd,
    pointMultiplication_injective_of_finrank_one a hdim,
    binary_pointMultiplication_surjective_of_postulation a hd hd1⟩

/-- Degree-one rank-one residual equations start the plane induction. -/
theorem plane_linear_residual_open [CharZero K] :
    ∃ Δ : MvPolynomial (Fin 2 × Fin 2) K,
      (∃ a : PointCoordinates K 2 2, eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        Function.Surjective (pointEvaluation K a 1) ∧
        Function.Injective (pointMultiplication a 1) ∧
        finrank K (pointDegreePiece K a 1) = 1 := by
  obtain ⟨Δ, hΔ, hgood⟩ := generic_pointHilbertFunction (K := K) (n := 2) (by omega) 2
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost⟩ := hgood a ha
  have hscalar : pointHilbertFunction K a 1 = 2 := by
    simpa using hpost 1
  have hdim : finrank K (pointDegreePiece K a 1) = 1 := by
    have h := (pointDegreePiece K a 1).finrank_quotient_add_finrank
    rw [finrank_chart_forms] at h
    change pointHilbertFunction K a 1 + _ = _ at h
    rw [hscalar] at h
    norm_num at h
    omega
  exact ⟨pointEvaluation_surjective_of_hilbert_eq a hscalar,
    pointMultiplication_injective_of_finrank_one a hdim, hdim⟩

/-- Extract a residual injection open from an already-proved plane statement. -/
theorem plane_residual_open (e r : ℕ) (hr : r ≤ N 3 e)
    (hcritical : (r : ℚ) ≤ E 3 e)
    (hplane : IdealGenerationAt K 2 e (N 3 e - r)) :
    ∃ Δ : MvPolynomial (Fin (N 3 e - r) × Fin 2) K,
      (∃ a : PointCoordinates K 2 (N 3 e - r), eval a Δ ≠ 0) ∧
      ∀ a, eval a Δ ≠ 0 →
        Function.Surjective (pointEvaluation K a e) ∧
        Function.Injective (pointMultiplication a e) ∧
        finrank K (pointDegreePiece K a e) = r := by
  have hp : N 3 e - r ≤ N 3 e := Nat.sub_le _ _
  have hres : ((N 3 e - (N 3 e - r) : ℕ) : ℚ) ≤ E 3 e := by
    simpa only [Nat.sub_sub_self hr] using hcritical
  obtain ⟨Δ, hΔ, hgood⟩ := idealGenerationAt_injective_open (K := K)
    (n := 2) (d := e) (by omega) hp hres hplane
  refine ⟨Δ, hΔ, fun a ha => ?_⟩
  obtain ⟨_, hpost, hinj⟩ := hgood a ha
  have he : pointHilbertFunction K a e = N 3 e - r := by
    have hh := hpost e
    rw [← N_chart 2 e, min_eq_right hp] at hh
    exact hh
  have hdim : finrank K (pointDegreePiece K a e) = r := by
    rw [pointDegreePiece_finrank a (by simpa only [N_chart] using hpost e)]
    exact Nat.sub_sub_self hr
  exact ⟨pointEvaluation_surjective_of_hilbert_eq a he, hinj, hdim⟩

/-- The lower critical maximal-rank assertion supplies an injection witness. -/
theorem plane_lower_critical_witness (D : ℕ) (hD : 1 ≤ D)
    (hG : IdealGenerationAt K 2 D (N 3 D - lowerCritical 3 D)) :
    ∃ a : PointCoordinates K 2 (N 3 D - lowerCritical 3 D),
      Function.Injective (pointMultiplication a D) := by
  have hrle : lowerCritical 3 D ≤ N 3 D := by
    have h := (lowerCritical_mem_cell 3 D (by omega) hD).2
    omega
  have hp : N 3 D - lowerCritical 3 D ≤ N 3 D := Nat.sub_le _ _
  have hcritical : ((N 3 D - (N 3 D - lowerCritical 3 D) : ℕ) : ℚ) ≤ E 3 D := by
    rw [Nat.sub_sub_self hrle]
    exact (le_E_iff_le_lowerCritical 3 D _).mpr le_rfl
  obtain ⟨Δ, hΔ, hgood⟩ := idealGenerationAt_injective_open (K := K)
    (n := 2) (d := D) (by omega) hp hcritical hG
  obtain ⟨a, ha⟩ := hΔ
  exact ⟨a, (hgood a ha).2.2⟩

/-- The upper critical assertion supplies a scalar-interpolating surjection witness. -/
theorem plane_upper_critical_witness (D : ℕ) (hD : 1 ≤ D)
    (hG : IdealGenerationAt K 2 D (N 3 D - upperCritical 3 D)) :
    ∃ a : PointCoordinates K 2 (N 3 D - upperCritical 3 D),
      Function.Surjective (pointEvaluation K a D) ∧
      Function.Surjective (pointMultiplication a D) := by
  have hrle : upperCritical 3 D ≤ N 3 D := by
    have h := (upperCritical_mem_cell 3 D (by omega) hD).2
    omega
  have hp : N 3 D - upperCritical 3 D ≤ N 3 D := Nat.sub_le _ _
  have hcritical : E 3 D ≤ ((N 3 D - (N 3 D - upperCritical 3 D) : ℕ) : ℚ) := by
    rw [Nat.sub_sub_self hrle]
    exact (E_le_iff_upperCritical_le 3 D _).mpr le_rfl
  obtain ⟨Δ, hΔ, hgood⟩ := idealGenerationAt_surjective_open (K := K)
    (n := 2) (d := D) (by omega) hp hcritical hG
  obtain ⟨a, ha⟩ := hΔ
  obtain ⟨_, hpost, hsurj⟩ := hgood a ha
  have he : pointHilbertFunction K a D = N 3 D - upperCritical 3 D := by
    have hh := hpost D
    rw [← N_chart 2 D, min_eq_right hp] at hh
    exact hh
  exact ⟨a, pointEvaluation_surjective_of_hilbert_eq a he, hsurj⟩

/-- Ideal generation for general points of the projective plane in every degree at least two. -/
theorem idealGenerationAt_projectivePlane [CharZero K] (D : ℕ) (hD : 2 ≤ D) :
    ∀ p, IdealGenerationAt K 2 D p := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    let e := D - 1
    have heD : e + 1 = D := by dsimp [e]; omega
    have hres (r : ℕ) (hr : r = D / 2 ∨ r = (D + 1) / 2) :
        ∃ Δ : MvPolynomial (Fin (N 3 e - r) × Fin 2) K,
          (∃ a : PointCoordinates K 2 (N 3 e - r), eval a Δ ≠ 0) ∧
          ∀ a, eval a Δ ≠ 0 → Function.Surjective (pointEvaluation K a e) ∧
            Function.Injective (pointMultiplication a e) ∧
            finrank K (pointDegreePiece K a e) = r := by
      by_cases hbase : D = 2
      · have he : e = 1 := by dsimp [e]; omega
        have hr1 : r = 1 := by rcases hr with hr | hr <;> omega
        rw [he, hr1]
        have hc : N 3 1 - 1 = 2 := by norm_num [N]
        rw [hc]
        exact plane_linear_residual_open
      · have he : 2 ≤ e := by dsimp [e]; omega
        have hlt : e < D := by dsimp [e]; omega
        have hrle : r ≤ N 3 e := by
          have hc := plane_residual_cell D hD
          rcases hr with rfl | rfl <;> dsimp [e] <;> omega
        have hcrit : (r : ℚ) ≤ E 3 e := by
          have hc := plane_residual_below_critical D hD
          rcases hr with rfl | rfl
          · exact hc.1
          · exact hc.2
        exact plane_residual_open e r hrle hcrit (ih e hlt he _)
    have htraceI : ∃ Δ : MvPolynomial (Fin (N 2 (e + 1) - 1) × Fin 1) K,
        (∃ b : PointCoordinates K 1 (N 2 (e + 1) - 1), eval b Δ ≠ 0) ∧
        ∀ b, eval b Δ ≠ 0 → Function.Injective (pointMultiplication b (e + 1)) := by
      have hc : N 2 (e + 1) - 1 = e + 1 := by rw [N_two_variables]; omega
      rw [hc]
      obtain ⟨Δ, hΔ, hgood⟩ := plane_trace_open (K := K) (e + 1)
      exact ⟨Δ, hΔ, fun b hb => (hgood b hb).2.1⟩
    have htraceS : ∃ Δ : MvPolynomial (Fin (N 2 (e + 1) - 1) × Fin 1) K,
        (∃ b : PointCoordinates K 1 (N 2 (e + 1) - 1), eval b Δ ≠ 0) ∧
        ∀ b, eval b Δ ≠ 0 → Function.Surjective (pointEvaluation K b (e + 1)) ∧
          Function.Surjective (pointMultiplication b (e + 1)) := by
      have hc : N 2 (e + 1) - 1 = e + 1 := by rw [N_two_variables]; omega
      rw [hc]
      obtain ⟨Δ, hΔ, hgood⟩ := plane_trace_open (K := K) (e + 1)
      exact ⟨Δ, hΔ, fun b hb => ⟨(hgood b hb).1, (hgood b hb).2.2⟩⟩
    have hcell := plane_residual_cell D hD
    have hrI : D / 2 ≤ N 3 e := by dsimp [e]; omega
    have hrS : (D + 1) / 2 ≤ N 3 e := by dsimp [e]; omega
    have ht : 1 ≤ N 2 (e + 1) := by rw [N_two_variables]; omega
    have hI : IdealGenerationAt K 2 D (N 3 D - lowerCritical 3 D) := by
      have hh := ordinary_hyperplane_injective_cell (K := K) (m := 1) (d := e)
        (D / 2) 1 hrI ht (hres (D / 2) (Or.inl rfl)) htraceI (by
          rw [N_two_variables, heD]
          exact (plane_residual_budgets D).1)
      simpa only [heD, lowerCritical_three_split] using hh
    have hS : IdealGenerationAt K 2 D (N 3 D - upperCritical 3 D) := by
      have hh := ordinary_hyperplane_surjective_cell (K := K) (m := 1) (d := e)
        ((D + 1) / 2) 1 hrS ht (hres ((D + 1) / 2) (Or.inr rfl)) htraceS (by
          rw [N_two_variables, heD]
          exact (plane_residual_budgets D).2)
      simpa only [heD, upperCritical_three_split] using hh
    exact reduction_to_critical_counts (K := K) (n := 2) (d := D) (by omega)
      (plane_lower_critical_witness D (by omega) hI)
      (plane_upper_critical_witness D (by omega) hS)

end IdealGeneration
