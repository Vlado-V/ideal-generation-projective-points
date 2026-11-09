module

public import IdealGeneration.GenericMatrixDescent
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Descent of the algebraic finite witness in the three-normal quadratic construction. -/

namespace IdealGeneration
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Vanishing at a primitive root in characteristic zero forces vanishing
after any specialization of the corresponding cyclotomic polynomial. -/
theorem cyclotomic_polynomial_nonvanishing {K S : Type*}
    [Field K] [CharZero K] [CommRing S] {n : ℕ} (hn : 0 < n)
    (ω : K) (hω : IsPrimitiveRoot ω n) (r : S)
    (hr : (cyclotomic n ℤ).eval₂ (Int.castRingHom S) r = 0)
    (f : Polynomial ℤ) (hf : f.eval₂ (Int.castRingHom S) r ≠ 0) :
    f.eval₂ (Int.castRingHom K) ω ≠ 0 := by
  intro hz
  have hzero : Polynomial.aeval ω f = 0 := by
    have hmap : algebraMap ℤ K = Int.castRingHom K := Subsingleton.elim _ _
    simpa only [Polynomial.aeval_def, hmap] using hz
  have hdiv : cyclotomic n ℤ ∣ f := by
    rw [Polynomial.cyclotomic_eq_minpoly hω hn]
    exact minpoly.isIntegrallyClosed_dvd (hω.isIntegral hn) hzero
  obtain ⟨g, rfl⟩ := hdiv
  apply hf
  rw [Polynomial.eval₂_mul, hr, zero_mul]

/-- The algebraic parameter used in Appendix A.4 satisfies the required
cyclotomic equation modulo 1009. -/
theorem primitive_cube_parameter_mod1009 :
    (cyclotomic 3 ℤ).eval₂ (Int.castRingHom (ZMod 1009)) (374 : ZMod 1009) = 0 := by
  norm_num [Polynomial.cyclotomic_three]
  decide +kernel

/-- An integer-polynomial matrix minor certified at the modular cube root
stays nonsingular at every primitive cube root in characteristic zero. -/
theorem cubic_root_matrix_det_ne_zero {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι (Polynomial ℤ)) (ω : K) (hω : IsPrimitiveRoot ω 3)
    (h : (A.map (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 1009)) 374)).det ≠ 0) :
    (A.map (Polynomial.eval₂RingHom (Int.castRingHom K) ω)).det ≠ 0 := by
  have hmod : A.det.eval₂ (Int.castRingHom (ZMod 1009)) 374 ≠ 0 := by
    change (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 1009)) 374) A.det ≠ 0
    rwa [(Polynomial.eval₂RingHom (Int.castRingHom (ZMod 1009)) 374).map_det]
  have hzero := cyclotomic_polynomial_nonvanishing (by decide : 0 < 3)
    ω hω (374 : ZMod 1009) primitive_cube_parameter_mod1009 A.det hmod
  change (Polynomial.eval₂RingHom (Int.castRingHom K) ω) A.det ≠ 0 at hzero
  rwa [(Polynomial.eval₂RingHom (Int.castRingHom K) ω).map_det] at hzero

/-- The same certificate gives injectivity of the actual characteristic-zero matrix. -/
theorem cubic_root_matrix_mulVec_injective {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι (Polynomial ℤ)) (ω : K) (hω : IsPrimitiveRoot ω 3)
    (h : (A.map (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 1009)) 374)).det ≠ 0) :
    Function.Injective (A.map (Polynomial.eval₂RingHom (Int.castRingHom K) ω)).mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero (cubic_root_matrix_det_ne_zero A ω hω h)

end IdealGeneration
