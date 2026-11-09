module

public import IdealGeneration.CubicEvenTransfer
public import IdealGeneration.CubicInductionNumerics
public import IdealGeneration.IntegralHyperplane

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The dimension induction for the cubic case -/

noncomputable section
namespace IdealGeneration
set_option maxHeartbeats 900000

variable {K : Type*} [Field K]

/-- Quadratic maximal rank gives the actual residual injection needed by the
integral cubic hyperplane transfer. -/
theorem cubic_residual_scalarInjection
    (n : ℕ) (hn : 4 ≤ n)
    (hquadratic : ∀ p, IdealGenerationAt K n 2 p) :
    ScalarInjectionAt K n 2 ⌈hyperplaneResidualRatio (n + 1) 3⌉₊ := by
  let r := ⌈hyperplaneResidualRatio (n + 1) 3⌉₊
  have hcrit : (r : ℚ) ≤ E (n + 1) 2 :=
    ceil_cubic_hyperplaneResidualRatio_le_E (n + 1) (by omega)
  have hwidth := E_le_cell_width (n + 1) 2 (by omega) (by decide)
  have hle : (r : ℚ) ≤ N (n + 1) 2 := by
    linarith [show (0 : ℚ) ≤ N (n + 1) (2 - 1) by positivity]
  have hr : r ≤ N (n + 1) 2 := by exact_mod_cast hle
  exact scalarInjectionAt_of_idealGenerationAt (by omega) r hr hcrit (hquadratic _)

variable [CharZero K]

/-- At an integral cubic trace, the preceding cubic dimension and the
quadratic assertion give all point counts in the next dimension. -/
theorem cubic_integral_dimension_step
    (n r : ℕ) (hn : 4 ≤ n) (hintegral : E n 3 = (r : ℚ))
    (hquadratic : ∀ p, IdealGenerationAt K n 2 p)
    (htrace : ∀ p, IdealGenerationAt K (n - 1) 3 p) :
    ∀ p, IdealGenerationAt K n 3 p := by
  have hn₁ : n - 1 + 1 = n := by omega
  have hn₂ : n - 1 + 2 = n + 1 := by omega
  have hintegral' : E (n - 1 + 1) (2 + 1) = (r : ℚ) := by
    simpa only [hn₁] using hintegral
  have htrace' : IdealGenerationAt K (n - 1) (2 + 1) (N (n - 1 + 1) (2 + 1) - r) := htrace _
  have hres : ScalarInjectionAt K (n - 1 + 1) 2 ⌈hyperplaneResidualRatio (n - 1 + 2) (2 + 1)⌉₊ := by
    simpa only [hn₁, hn₂] using cubic_residual_scalarInjection n hn hquadratic
  simpa only [hn₁] using
    integral_hyperplane_transfer (n - 1) 2 r (by omega) hintegral' htrace' hres

/-- The integral hyperplane and even two-variable transfers give the cubic
dimension induction. The remaining inputs are the low-dimensional cubic
cases and actual injective middle-map witnesses. -/
theorem cubic_all_dimensions_of_even_middle
    (hquadratic : ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p)
    (hbase : ∀ n, 1 ≤ n → n ≤ 10 → ∀ p, IdealGenerationAt K n 3 p)
    (heven : ∀ k, CubicEvenMiddleWitness K (10 + 2 * k)) :
    ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn
    by_cases hsmall : n ≤ 10
    · exact hbase n hn hsmall p
    by_cases hint : ∃ r : ℕ, E n 3 = (r : ℚ)
    · obtain ⟨r, hr⟩ := hint
      exact cubic_integral_dimension_step n r (by omega) hr
        (fun q => hquadratic n q hn) (fun q => ih (n - 1) (by omega) q (by omega)) p
    · have hmod : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 := by
        by_contra! hmod
        exact hint ((cubic_E_integral_iff_mod_eight n).mpr hmod)
      have hodd : n % 2 = 1 := by
        rcases hmod with h | h | h <;> omega
      let k := (n - 11) / 2
      have hk : n - 1 = 10 + 2 * k := by
        dsimp [k]
        omega
      have hc : CubicEvenMiddleWitness K (n - 1) := hk.symm ▸ heven k
      have ht (q : ℕ) : IdealGenerationAt K (n - 1 - 1) 3 q :=
        ih (n - 1 - 1) (by omega) q (by omega)
      simpa only [Nat.sub_add_cancel hn] using
        cubic_twoVariable_transfer_of_middle (n - 1) (by omega) hc ht p

end IdealGeneration
