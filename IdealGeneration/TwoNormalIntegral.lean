module

public import IdealGeneration.IntegralTraceNumerics
public import IdealGeneration.ResponseSelection
public import IdealGeneration.DeformationGeneral

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Integral two-normal transfer

The numerical identities identify the residual kernel and the two slice
cokernels. The response lemma turns the two actual coordinate families into
a polynomial motion of maximal rank.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial
set_option maxHeartbeats 800000

/-- The two Pascal decompositions in (4.1). -/
theorem scalar_count_decomposition (m D : ℕ) (hd : 2 ≤ D) :
    N (m + 2) D = N m D + 2 * N (m + 1) (D - 1) + N (m + 2) (D - 2) ∧
    N (m + 2) (D - 1) = N (m + 1) (D - 1) + N (m + 2) (D - 2) := by
  have h₀ := N_pascal (m + 2) D (by omega) (by omega)
  have h₁ := N_pascal (m + 1) D (by omega) (by omega)
  have h₂ := N_pascal (m + 2) (D - 1) (by omega) (by omega)
  simp only [show m + 2 - 1 = m + 1 by omega,
    show m + 1 - 1 = m by omega,
    show D - 1 - 1 = D - 2 by omega] at h₀ h₁ h₂
  omega

/-- The two cross-degree identities in (4.1). -/
theorem cross_degree_counts (m D : ℕ) (hm : 1 ≤ m) (hd : 2 ≤ D) :
    D * N m D = m * N (m + 1) (D - 1) ∧
    (m + 1) * N (m + 2) (D - 2) = (D - 1) * N (m + 1) (D - 1) := by
  constructor
  · simpa only [show m + 1 - 1 = m by omega] using
      (N_cross_hyperplane (m + 1) D (by omega) (by omega)).symm
  · simpa only [show m + 2 - 1 = m + 1 by omega,
      show D - 1 - 1 = D - 2 by omega] using
      N_cross_hyperplane (m + 2) (D - 1) (by omega) (by omega)

/-- The number of points selected on each slice. -/
def sliceCount (m D : ℕ) : ℕ :=
  ⌈(D : ℚ) * N (m + 1) (D - 1) / (D + 1)⌉₊

/-- The rounding error used in (4.2). -/
def sliceRounding (m D : ℕ) : ℚ :=
  (sliceCount m D : ℚ) - (D : ℚ) * N (m + 1) (D - 1) / (D + 1)

/-- Each slice-rounding error lies in the half-open unit interval. -/
theorem sliceRounding_bounds (m D : ℕ) :
    0 ≤ sliceRounding m D ∧ sliceRounding m D < 1 := by
  have hp : (0 : ℚ) ≤ (D : ℚ) * N (m + 1) (D - 1) / (D + 1) := by positivity
  have h₀ := Nat.le_ceil ((D : ℚ) * N (m + 1) (D - 1) / (D + 1))
  have h₁ := Nat.ceil_lt_add_one hp
  change 0 ≤ (⌈(D : ℚ) * N (m + 1) (D - 1) / (D + 1)⌉₊ : ℚ) - _ ∧
    (⌈(D : ℚ) * N (m + 1) (D - 1) / (D + 1)⌉₊ : ℚ) - _ < 1
  constructor <;> linarith

/-- The signed discrepancy from the ambient critical value. -/
def criticalDeviation (m D r : ℕ) : ℚ := (r : ℚ) - E (m + 2) D

/-- Both critical choices have discrepancy strictly between minus one and one. -/
theorem criticalDeviation_bounds (m D r : ℕ)
    (hr : r = lowerCritical (m + 2) D ∨ r = upperCritical (m + 2) D) :
    -1 < criticalDeviation m D r ∧ criticalDeviation m D r < 1 := by
  have he : (0 : ℚ) ≤ E (m + 2) D := by unfold E; positivity
  rcases hr with rfl | rfl
  · have h₀ := Nat.floor_le he
    have h₁ := Nat.lt_floor_add_one (E (m + 2) D)
    change -1 < (⌊E (m + 2) D⌋₊ : ℚ) - E (m + 2) D ∧
      (⌊E (m + 2) D⌋₊ : ℚ) - E (m + 2) D < 1
    constructor <;> linarith
  · have h₀ := Nat.le_ceil (E (m + 2) D)
    have h₁ := Nat.ceil_lt_add_one he
    change -1 < (⌈E (m + 2) D⌉₊ : ℚ) - E (m + 2) D ∧
      (⌈E (m + 2) D⌉₊ : ℚ) - E (m + 2) D < 1
    constructor <;> linarith

/-- The residual ideal dimension expressed before integer point counts are subtracted. -/
def residualDimension (m D r : ℕ) : ℚ :=
  (N (m + 2) (D - 2) : ℚ) / (D + 1) + criticalDeviation m D r +
    2 * sliceRounding m D

/-- The common slice cokernel dimension in (4.6). -/
theorem slice_cokernel_identity (m D : ℕ) (hm : 1 ≤ m) (hd : 2 ≤ D) :
    (D : ℚ) * N m D / (D + 1) -
        m * ((N (m + 1) (D - 1) : ℚ) - sliceCount m D) =
      m * sliceRounding m D := by
  have hc : (D : ℚ) * N m D = (m : ℚ) * N (m + 1) (D - 1) := by
    exact_mod_cast (cross_degree_counts m D hm hd).1
  unfold sliceRounding
  field_simp
  nlinarith

/-- The signed residual kernel dimension is twice the slice cokernel dimension
plus the source-minus-target discrepancy, as in (4.9). -/
theorem residual_kernel_identity (m D r : ℕ) (hm : 1 ≤ m) (hd : 2 ≤ D) :
    (N (m + 1) (D - 1) : ℚ) + (m + 1) * residualDimension m D r -
        2 * sliceCount m D =
      2 * m * sliceRounding m D + (m + 1) * criticalDeviation m D r := by
  have hc : ((m : ℚ) + 1) * N (m + 2) (D - 2) =
      ((D : ℚ) - 1) * N (m + 1) (D - 1) := by
    have h := (cross_degree_counts m D hm hd).2
    have hd' : 1 ≤ D := by omega
    exact_mod_cast (show (m + 1) * N (m + 2) (D - 2) =
      (D - 1) * N (m + 1) (D - 1) from h)
  unfold residualDimension sliceRounding
  field_simp
  nlinarith

section Rank
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The residual kernel count and the source-target discrepancy determine the
entire cokernel, without a separate rank hypothesis. -/
theorem cokernel_dimension_from_residual_kernel (f : V →ₗ[K] W) (c : ℕ) (σ : ℤ)
    (hdiff : (finrank K V : ℤ) - finrank K W = σ)
    (hker : (finrank K f.ker : ℤ) = 2 * c + σ) :
    finrank K (W ⧸ f.range) = 2 * c := by
  have hn := f.finrank_range_add_finrank_ker
  have hq := f.range.finrank_quotient_add_finrank
  omega

/-- The zero-kernel and zero-slice-cokernel cases are already of maximal rank. -/
theorem maximalRank_or_positive_cokernel (f : V →ₗ[K] W) (c : ℕ) (σ : ℤ)
    (hdiff : (finrank K V : ℤ) - finrank K W = σ)
    (hker : (finrank K f.ker : ℤ) = max 0 (2 * c + σ)) :
    HasMaximalRank f ∨
      (0 < finrank K f.ker ∧ 0 < c ∧ finrank K (W ⧸ f.range) = 2 * c) := by
  by_cases hk : finrank K f.ker = 0
  · left
    left
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  · have hpos : 0 < finrank K f.ker := Nat.pos_of_ne_zero hk
    have hlinear : (finrank K f.ker : ℤ) = 2 * c + σ := by
      rw [max_eq_right] at hker
      · exact hker
      · omega
    have hq := cokernel_dimension_from_residual_kernel f c σ hdiff hlinear
    by_cases hc : c = 0
    · left
      right
      have hz : finrank K (W ⧸ f.range) = 0 := by simpa [hc] using hq
      apply LinearMap.range_eq_top.mp
      apply Submodule.eq_top_of_finrank_eq
      have hdim := f.range.finrank_quotient_add_finrank
      simpa only [hz, zero_add] using hdim
    · exact Or.inr ⟨hpos, Nat.pos_of_ne_zero hc, hq⟩
end Rank

section FirstResponse
variable {K V W QA QB ι κ : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup QA] [Module K QA] [FiniteDimensional K QA]
  [AddCommGroup QB] [Module K QB] [FiniteDimensional K QB]
  [Fintype ι] [Fintype κ]

/-- The two normal coordinate families supply a binary motion whose induced
response has maximal rank, and whose nearby polynomial maps have maximal rank. -/
theorem exists_binary_two_normal_maximal_motion
    (A₀ : V →ₗ[K] W)
    (A D : (ι → K) → (κ → K) → (Fin 1 → K) → (V →ₗ[K] W))
    (hA : ∀ u v, IsPolynomialFamily (A u v))
    (hD : ∀ u v, IsPolynomialFamily (D u v))
    (hfactor : ∀ u v a, A u v a = A₀ + a 0 • D u v a)
    (e : (W ⧸ A₀.range) ≃ₗ[K] (QA × QB))
    (α : ι → Module.Dual K A₀.ker) (β : κ → Module.Dual K A₀.ker)
    (eA : ι → QA) (eB : κ → QB)
    (hα : Submodule.span K (Set.range α) = ⊤)
    (hβ : Submodule.span K (Set.range β) = ⊤)
    (heA : ∀ (r : ℕ) (f : Fin r ↪ ι), r ≤ finrank K QA →
      LinearIndependent K (eA ∘ f))
    (heB : ∀ (r : ℕ) (f : Fin r ↪ κ), r ≤ finrank K QB →
      LinearIndependent K (eB ∘ f))
    (hresponse : ∀ u v, e.toLinearMap.comp
        (DeformationGeneral.response A₀ (D u v 0) A₀.range.mkQ) =
      (firstResponse α (fun i => u i • eA i)).prod
        (firstResponse β (fun j => v j • eB j))) :
    ∃ (u : ι → K) (v : κ → K),
      (∀ i, u i = 0 ∨ u i = 1) ∧ (∀ j, v j = 0 ∨ v j = 1) ∧
      ∃ f : MvPolynomial (Fin 1) K, eval 0 f ≠ 0 ∧
        ∀ a : Fin 1 → K, a 0 ≠ 0 → eval a f ≠ 0 → HasMaximalRank (A u v a) := by
  obtain ⟨u, v, hu, hv, hr⟩ := exists_binary_maximal_response α β eA eB hα hβ heA heB
  have hc : HasMaximalRank (e.toLinearMap.comp
      (DeformationGeneral.response A₀ (D u v 0) A₀.range.mkQ)) := by
    apply (maximalRank_iff_rank_eq_min _).mpr
    rw [hresponse u v, hr, Module.finrank_prod]
  have hR : HasMaximalRank (DeformationGeneral.response A₀ (D u v 0) A₀.range.mkQ) := by
    rcases hc with hi | hs
    · left
      intro x y hxy
      exact hi (congrArg e hxy)
    · right
      intro q
      obtain ⟨x, hx⟩ := hs (e q)
      exact ⟨x, e.injective hx⟩
  have hz : A u v 0 = A₀ := by simpa using hfactor u v 0
  have hR' : HasMaximalRank (DeformationGeneral.response
      (A u v 0) (D u v 0) (A u v 0).range.mkQ) := by
    rw [hz]
    exact hR
  have hfactor' : ∀ a, A u v a = A u v 0 + a 0 • D u v a := by
    intro a
    rw [hz]
    exact hfactor u v a
  exact ⟨u, v, hu, hv, DeformationGeneral.maximal_rank_principal_open
    (A u v) (D u v) (hA u v) (hD u v) hfactor' hR'⟩
end FirstResponse

end IdealGeneration.TwoNormalIntegral
