module

public import IdealGeneration.CubicSupportedActual
public import IdealGeneration.QuadraticElimination

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The upper normal coefficient solves in Lemma B.2. -/

noncomputable section
namespace IdealGeneration.CubicUpperSolve

open CubicSupported

section Quartic

variable {K : Type*} [Field K]

/-- Multiplication of two binary cubics by `s,t`, in descending `s` order. -/
def normalQuarticMap : ((Fin 4 → K) × (Fin 4 → K)) →ₗ[K] (Fin 5 → K) where
  toFun C := ![C.1 0, C.1 1 + C.2 0, C.1 2 + C.2 1, C.1 3 + C.2 2, C.2 3]
  map_add' C D := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a C := by funext i; fin_cases i <;> simp <;> ring

theorem normalQuarticMap_surjective : Function.Surjective (normalQuarticMap (K := K)) := by
  intro r
  refine ⟨(![r 0, r 1, r 2, r 3], ![0, 0, 0, r 4]), ?_⟩
  funext i
  fin_cases i <;> simp [normalQuarticMap]

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The top normal equation for the `s,t` multiplier coefficients. -/
def omegaMap (top : E →ₗ[K] (Fin 4 → K)) : (E × E) →ₗ[K] (Fin 5 → K) :=
  normalQuarticMap.comp (top.prodMap top)

abbrev Omega (top : E →ₗ[K] (Fin 4 → K)) := (omegaMap top).ker

theorem omegaMap_surjective (top : E →ₗ[K] (Fin 4 → K)) (htop : Function.Surjective top) :
    Function.Surjective (omegaMap top) := by
  intro r
  obtain ⟨C, hC⟩ := normalQuarticMap_surjective r
  obtain ⟨x, hx⟩ := htop C.1
  obtain ⟨y, hy⟩ := htop C.2
  refine ⟨(x, y), ?_⟩
  simpa only [omegaMap, LinearMap.comp_apply, LinearMap.prodMap_apply, hx, hy] using hC

/-- The pure normal quartic equations remove five dimensions. -/
theorem finrank_omega [FiniteDimensional K E] (top : E →ₗ[K] (Fin 4 → K))
    (htop : Function.Surjective top) : Module.finrank K (Omega top) = 2 * Module.finrank K E - 5 := by
  have h := (omegaMap top).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (omegaMap_surjective top htop), finrank_top,
    Module.finrank_pi, Fintype.card_fin, Module.finrank_prod] at h
  change 5 + Module.finrank K (Omega top) = Module.finrank K E + Module.finrank K E at h
  omega

/-- Each trace multiplier has its normal cubic forced by the two mixed quadratics. -/
def cubicCorrection (Qs Qt : Fin 3 → K) : Fin 4 → K :=
  -(QuadraticElimination.normalCubicMap (Qs, Qt))

theorem cubicCorrection_cancel (Qs Qt : Fin 3 → K) (s t : K) :
    normalCubic (cubicCorrection Qs Qt) s t + s * normalQuadratic Qs s t +
      t * normalQuadratic Qt s t = 0 := by
  simp [cubicCorrection, QuadraticElimination.normalCubicMap, normalCubic, normalQuadratic]
  ring

end Quartic

section SymmetricSolve

variable {K : Type*} [Field K] {m : ℕ}

/-- A free mixed coefficient on every increasing pair determines an antisymmetric matrix. -/
def antisymmetric (z : Edge m → Fin 3 → K) (i j : Fin m) (a : Fin 3) : K :=
  if h : i < j then z ⟨(i, j), h⟩ a
  else if h : j < i then -z ⟨(j, i), h⟩ a
  else 0

theorem antisymmetric_swap (z : Edge m → Fin 3 → K) (i j : Fin m) (a : Fin 3) :
    antisymmetric z j i a = -antisymmetric z i j a := by
  by_cases h : i < j
  · simp [antisymmetric, h, not_lt_of_ge h.le]
  · by_cases h' : j < i <;> simp [antisymmetric, h, h']

private def quadraticAt {R : Type*} [CommRing R] (y : Fin m → R) :
    (Fin m → Fin m → R) →ₗ[R] R where
  toFun A := traceQuadratic A y
  map_add' A B := by
    simp [traceQuadratic, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r A := by
    change traceQuadratic (fun i j => r * A i j) y = r * traceQuadratic A y
    simp only [traceQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem quadraticAt_transpose {R : Type*} [CommRing R]
    (y : Fin m → R) (A : Fin m → Fin m → R) :
    quadraticAt y (fun i j => A j i) = quadraticAt y A := by
  change (∑ i, ∑ j, A j i * y i * y j) = ∑ i, ∑ j, A i j * y i * y j
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The free antisymmetric coefficients do not affect the symmetric trace quadratic. -/
theorem antisymmetric_traceQuadratic_zero (h₂ : (2 : K) ≠ 0)
    (z : Edge m → Fin 3 → K) (a : Fin 3) (y : Fin m → K) :
    traceQuadratic (fun i j => antisymmetric z i j a) y = 0 := by
  let A := fun i j => antisymmetric z i j a
  have hswap : (fun i j => A j i) = -A := by
    funext i j
    exact antisymmetric_swap z i j a
  have h := quadraticAt_transpose y A
  rw [hswap, map_neg] at h
  have hprod : (2 : K) * quadraticAt y A = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hprod).resolve_left h₂

/-- The symmetric correction, with independent antisymmetric parameters. -/
def symmetricCompletion (A : Fin m → Fin m → Fin 3 → K)
    (z : Edge m → Fin 3 → K) (i j : Fin m) (a : Fin 3) : K :=
  antisymmetric z i j a - (A i j a + A j i a) / 2

/-- The completion cancels the required upper normal-quadratic coefficients. -/
theorem symmetricCompletion_cancel (h₂ : (2 : K) ≠ 0)
    (A : Fin m → Fin m → Fin 3 → K) (z : Edge m → Fin 3 → K)
    (a : Fin 3) (y : Fin m → K) :
    traceQuadratic (fun i j => symmetricCompletion A z i j a) y +
      traceQuadratic (fun i j => A i j a) y = 0 := by
  let M := fun i j => A i j a
  let Z := fun i j => antisymmetric z i j a
  have hcomp : (fun i j => symmetricCompletion A z i j a) =
      Z - (2 : K)⁻¹ • (M + fun i j => M j i) := by
    funext i j
    simp [symmetricCompletion, M, Z, div_eq_mul_inv, mul_comm, add_mul]
  change quadraticAt y (fun i j => symmetricCompletion A z i j a) + quadraticAt y M = 0
  rw [hcomp, map_sub, map_smul, map_add, quadraticAt_transpose y M]
  have hz : quadraticAt y Z = 0 := antisymmetric_traceQuadratic_zero h₂ z a y
  rw [hz, smul_eq_mul]
  field_simp
  ring

/-- The completed matrix plus the prescribed matrix is antisymmetric. -/
theorem symmetricCompletion_add_swap (h₂ : (2 : K) ≠ 0)
    (A : Fin m → Fin m → Fin 3 → K) (z : Edge m → Fin 3 → K)
    (i j : Fin m) (a : Fin 3) :
    symmetricCompletion A z j i a + A j i a =
      -(symmetricCompletion A z i j a + A i j a) := by
  unfold symmetricCompletion
  rw [antisymmetric_swap z i j a]
  field_simp
  ring

private theorem traceQuadratic_zero_of_swap {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h₂ : (2 : R) ≠ 0) (A : Fin m → Fin m → R) (y : Fin m → R)
    (hswap : ∀ i j, A j i = -A i j) : traceQuadratic A y = 0 := by
  have hswap' : (fun i j => A j i) = -A := by
    funext i j
    exact hswap i j
  have h := quadraticAt_transpose y A
  rw [hswap', map_neg] at h
  have hprod : (2 : R) * quadraticAt y A = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hprod).resolve_left h₂

/-- The cancellation is a literal polynomial identity, also over finite fields. -/
theorem symmetricCompletion_polynomial_cancel (h₂ : (2 : K) ≠ 0)
    (A : Fin m → Fin m → Fin 3 → K) (z : Edge m → Fin 3 → K) (a : Fin 3) :
    traceQuadratic (fun i j => MvPolynomial.C (symmetricCompletion A z i j a)) MvPolynomial.X +
      traceQuadratic (fun i j => MvPolynomial.C (A i j a)) MvPolynomial.X = 0 := by
  let f : Fin m → Fin m → Poly K m := fun i j => MvPolynomial.C (symmetricCompletion A z i j a)
  let g : Fin m → Fin m → Poly K m := fun i j => MvPolynomial.C (A i j a)
  change quadraticAt MvPolynomial.X f + quadraticAt MvPolynomial.X g = 0
  rw [← map_add]
  change traceQuadratic (f + g) MvPolynomial.X = 0
  have h₂' : (2 : Poly K m) ≠ 0 := by
    intro h
    have hc : (MvPolynomial.C (2 : K) : Poly K m) = MvPolynomial.C (0 : K) := by
      simpa only [map_ofNat, map_zero] using h
    exact h₂ (MvPolynomial.C_injective (Fin m) K hc)
  apply traceQuadratic_zero_of_swap h₂'
  intro i j
  change MvPolynomial.C (symmetricCompletion A z j i a) + MvPolynomial.C (A j i a) =
    -(MvPolynomial.C (symmetricCompletion A z i j a) + MvPolynomial.C (A i j a))
  simpa only [map_add, map_neg] using
    congrArg (MvPolynomial.C : K →+* Poly K m) (symmetricCompletion_add_swap h₂ A z i j a)

/-- Every solution of the symmetric trace-quadratic equation arises by the stated completion. -/
theorem symmetricCompletion_complete (h₂ : (2 : K) ≠ 0)
    (A B : Fin m → Fin m → Fin 3 → K)
    (h : ∀ (a : Fin 3) (y : Fin m → K),
      traceQuadratic (fun i j => B i j a) y + traceQuadratic (fun i j => A i j a) y = 0) :
    ∃ z : Edge m → Fin 3 → K, B = symmetricCompletion A z := by
  let Z := fun i j a => B i j a + (A i j a + A j i a) / 2
  have hZ (a : Fin 3) (y : Fin m → K) : traceQuadratic (fun i j => Z i j a) y = 0 := by
    let M := fun i j => A i j a
    let N := fun i j => B i j a
    have hsum : (fun i j => Z i j a) = N + (2 : K)⁻¹ • (M + fun i j => M j i) := by
      funext i j
      simp [Z, M, N, div_eq_mul_inv, mul_comm, add_mul]
    change quadraticAt y (fun i j => Z i j a) = 0
    rw [hsum, map_add, map_smul, map_add, quadraticAt_transpose y M, smul_eq_mul]
    have hB : quadraticAt y N + quadraticAt y M = 0 := h a y
    field_simp
    linear_combination 2 * hB
  have hdiag (i : Fin m) (a : Fin 3) : Z i i a = 0 := by
    simpa using hZ a (vertexSupport i 1)
  have hpair (i j : Fin m) (a : Fin 3) : Z i j a + Z j i a = 0 := by
    have hz := hZ a (fun k => vertexSupport i 1 k + vertexSupport j 1 k)
    rw [traceQuadratic_pair] at hz
    simpa [hdiag] using hz
  let z : Edge m → Fin 3 → K := fun e a => Z e.val.1 e.val.2 a
  have hrecover (i j : Fin m) (a : Fin 3) : antisymmetric z i j a = Z i j a := by
    by_cases hij : i < j
    · simp [antisymmetric, hij, z]
    · by_cases hji : j < i
      · simpa [antisymmetric, hij, hji, z] using (eq_neg_of_add_eq_zero_left (hpair i j a)).symm
      · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        simp [antisymmetric, hdiag]
  refine ⟨z, ?_⟩
  funext i j a
  rw [symmetricCompletion, hrecover]
  dsimp [Z]
  ring

end SymmetricSolve
end IdealGeneration.CubicUpperSolve
