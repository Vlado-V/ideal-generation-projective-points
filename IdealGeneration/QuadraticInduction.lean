module

public import IdealGeneration.QuadraticLowDimensionFour
public import IdealGeneration.QuadraticLowDimensionFive
public import IdealGeneration.QuadraticLowDimensionSix
public import IdealGeneration.QuadraticLowDimensionNine
public import IdealGeneration.QuarticRange

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Quadratic induction on the number of variables

The two-normal steps cover residues one and two modulo three. The
three-normal step covers the remaining residue and starts at fifteen
variables. Each step uses the critical trace count in a smaller space.
-/

namespace IdealGeneration

private theorem quadratic_critical_counts_of_mod_three (n : ℕ) (hn : 1 ≤ n)
    (hmod : n % 3 = 0) :
    N n 2 - lowerCritical n 2 = n * (n + 1) / 3 ∧
    N n 2 - upperCritical n 2 = n * (n + 1) / 3 := by
  let t := n / 3
  have ht : n = 3 * t := by dsimp [t]; omega
  have hprod : n * (n + 1) = 3 * (t * (n + 1)) := by
    calc
      n * (n + 1) = (3 * t) * (n + 1) := congrArg (fun x => x * (n + 1)) ht
      _ = _ := Nat.mul_assoc _ _ _
  have hcount : n * (n + 1) / 3 = t * (n + 1) := by rw [hprod]; omega
  have hN := N_degree_recurrence n 1 hn
  change 2 * N n 2 = (n + 1) * N n 1 at hN
  rw [N_one_degree, Nat.mul_comm (n + 1) n, hprod] at hN
  let p := n * (n + 1) / 3
  have hp : p = t * (n + 1) := hcount
  have hr : N n 2 = 3 * (N n 2 - p) := by omega
  have he : E n 2 = ((N n 2 - p : ℕ) : ℚ) := by
    norm_num [E]
    apply (div_eq_iff (by norm_num : (3 : ℚ) ≠ 0)).2
    rw [mul_comm]
    exact_mod_cast hr
  have hle : p ≤ N n 2 := by omega
  constructor <;>
    simp only [lowerCritical, upperCritical, he, Nat.floor_natCast, Nat.ceil_natCast,
      Nat.sub_sub_self hle] <;> rfl

variable {K : Type*} [Field K] [CharZero K]

/-- The exact critical point counts of Appendix A give the quadratic
assertion in every dimension. The three cone steps use their trace counts
in the induction hypothesis. -/
theorem quadratic_induction_of_steps
    (hTwelve : ∀ p, IdealGenerationAt K 11 2 p)
    (hModOne : ∀ ν : ℕ, 2 ≤ ν →
      IdealGenerationAt K (3 * ν - 2) 2 (ν * (3 * ν - 1)) →
      ∀ p, IdealGenerationAt K (3 * ν) 2 p)
    (hModTwo : ∀ ν : ℕ, 2 ≤ ν →
      IdealGenerationAt K (3 * ν - 1) 2 (ν * (3 * ν + 1)) →
      ∀ p, IdealGenerationAt K (3 * ν + 1) 2 p)
    (hModZero : ∀ h : ℕ, 8 ≤ h → h % 3 = 2 →
      IdealGenerationAt K (h + 3) 2 ((h + 4) * (h + 5) / 3) →
      IdealGenerationAt K (h + 6) 2 ((h + 7) * (h + 8) / 3)) :
    ∀ n, 2 ≤ n → ∀ p, IdealGenerationAt K (n - 1) 2 p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : n = 2
    · subst n
      exact idealGenerationAt_projectiveLine_all 2 (by decide)
    by_cases h3 : n = 3
    · subst n
      exact idealGenerationAt_projectivePlane 2 (by decide)
    by_cases h4 : n = 4
    · subst n
      exact QuadraticLowDimension.quadratic_four_all
    by_cases h5 : n = 5
    · subst n
      exact QuadraticLowDimension.quadratic_five_all
    by_cases h6 : n = 6
    · subst n
      exact QuadraticLowDimension.quadratic_six_all
    by_cases h9 : n = 9
    · subst n
      exact QuadraticLowDimension.quadratic_nine_all
    by_cases h12 : n = 12
    · subst n
      exact hTwelve
    by_cases hzero : n % 3 = 0
    · let h := n - 7
      have hlarge : 15 ≤ n := by omega
      have hh : 8 ≤ h := by dsimp [h]; omega
      have hmod : h % 3 = 2 := by dsimp [h]; omega
      have htrace := ih (h + 4) (by dsimp [h]; omega) (by omega)
        ((h + 4) * (h + 5) / 3)
      have htraceDim : h + 4 - 1 = h + 3 := by omega
      have hendpoint := hModZero h hh hmod (by simpa only [htraceDim] using htrace)
      have hcount := quadratic_critical_counts_of_mod_three (h + 7) (by omega) (by omega)
      have hall := idealGenerationAt_all_of_critical (n := h + 6) (d := 2) (by omega) (by decide)
        (hcount.1.symm ▸ hendpoint) (hcount.2.symm ▸ hendpoint)
      have hdim : h + 6 = n - 1 := by dsimp [h]; omega
      simpa only [hdim] using hall
    let ν := n / 3
    by_cases hone : n % 3 = 1
    · have hν : 2 ≤ ν := by dsimp [ν]; omega
      have hnν : n = 3 * ν + 1 := by dsimp [ν]; omega
      have htrace := ih (3 * ν - 1) (by omega) (by omega) (ν * (3 * ν - 1))
      have htraceDim : 3 * ν - 1 - 1 = 3 * ν - 2 := by omega
      have hall := hModOne ν hν (by simpa only [htraceDim] using htrace)
      have hdim : 3 * ν = n - 1 := by omega
      simpa only [hdim] using hall
    · have hν : 2 ≤ ν := by dsimp [ν]; omega
      have hnν : n = 3 * ν + 2 := by dsimp [ν]; omega
      have htrace := ih (3 * ν) (by omega) (by omega) (ν * (3 * ν + 1))
      have hall := hModTwo ν hν htrace
      have hdim : 3 * ν + 1 = n - 1 := by omega
      simpa only [hdim] using hall

end IdealGeneration
