module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Descent of exact modular determinant certificates to characteristic zero. -/

namespace IdealGeneration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero determinant after modular reduction certifies the integer determinant. -/
theorem integer_matrix_det_ne_zero_of_mod (A : Matrix ι ι ℤ) (p : ℕ)
    (h : (A.map (Int.castRingHom (ZMod p))).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  apply h
  change (A.map (fun z : ℤ => (z : ZMod p))).det = 0
  rw [← Int.cast_det, hz, Int.cast_zero]

/-- The certified integer determinant stays nonzero over every characteristic-zero field. -/
theorem integer_matrix_det_ne_zero_over {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι ℤ) (p : ℕ)
    (h : (A.map (Int.castRingHom (ZMod p))).det ≠ 0) :
    (A.map (Int.castRingHom K)).det ≠ 0 := by
  have hz := integer_matrix_det_ne_zero_of_mod A p h
  change (A.map (fun z : ℤ => (z : K))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast hz

/-- A modular certificate for a row-cleared matrix certifies the original rational matrix. -/
theorem rational_matrix_det_ne_zero_of_mod_row_clear
    (A : Matrix ι ι ℚ) (B : Matrix ι ι ℤ) (scale : ι → ℤ) (p : ℕ)
    (hclear : Matrix.diagonal (fun i => (scale i : ℚ)) * A = B.map (Int.castRingHom ℚ))
    (hmod : (B.map (Int.castRingHom (ZMod p))).det ≠ 0) : A.det ≠ 0 := by
  have hB := integer_matrix_det_ne_zero_over (K := ℚ) B p hmod
  intro hA
  apply hB
  rw [← hclear, Matrix.det_mul, hA, mul_zero]

/-- A nonzero rational determinant stays nonzero over every characteristic-zero field. -/
theorem rational_matrix_det_ne_zero_over {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι ℚ) (hA : A.det ≠ 0) :
    (A.map (Rat.castHom K)).det ≠ 0 := by
  intro hz
  apply hA
  apply (Rat.castHom K).injective
  rw [map_zero, (Rat.castHom K).map_det]
  exact hz

/-- The modular integer certificate provides an actual bijective linear map. -/
theorem integer_matrix_mulVec_bijective_of_mod {K : Type*} [Field K] [CharZero K]
    (A : Matrix ι ι ℤ) (p : ℕ)
    (h : (A.map (Int.castRingHom (ZMod p))).det ≠ 0) :
    Function.Bijective (A.map (Int.castRingHom K)).mulVec := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero
    (integer_matrix_det_ne_zero_over (K := K) A p h)
  refine ⟨hi, ?_⟩
  exact LinearMap.surjective_of_injective (f := Matrix.mulVecLin (A.map (Int.castRingHom K))) hi

/-- A nonzero evaluation of an integer polynomial over any coefficient ring
gives a nonzero evaluation over every characteristic-zero field. -/
theorem integer_polynomial_nonvanishing_descends {σ S K : Type*}
    [CommRing S] [Field K] [CharZero K]
    (p : MvPolynomial σ ℤ) (x : σ → S)
    (h : MvPolynomial.eval₂ (Int.castRingHom S) x p ≠ 0) :
    ∃ y : σ → K, MvPolynomial.eval₂ (Int.castRingHom K) y p ≠ 0 := by
  have hp : p ≠ 0 := by
    intro hz
    simp only [hz, MvPolynomial.eval₂_zero] at h
    exact h rfl
  have hmap : MvPolynomial.map (Int.castRingHom K) p ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.map_injective (Int.castRingHom K)
      (show Function.Injective (Int.castRingHom K) from fun a b hab => Int.cast_injective hab)
    simpa using hz
  have hex : ∃ y : σ → K, MvPolynomial.eval y (MvPolynomial.map (Int.castRingHom K) p) ≠ 0 := by
    by_contra! hn
    exact hmap (MvPolynomial.funext (fun y => by simpa using hn y))
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, by simpa only [MvPolynomial.eval_map] using hy⟩

/-- An explicitly selected polynomial minor detected in finite characteristic
is also nonzero at some characteristic-zero parameter configuration. -/
theorem integer_polynomial_matrix_det_nonvanishing_descends {σ S K : Type*}
    [CommRing S] [Field K] [CharZero K]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (x : σ → S)
    (h : (A.map (MvPolynomial.eval₂Hom (Int.castRingHom S) x)).det ≠ 0) :
    ∃ y : σ → K, (A.map (MvPolynomial.eval₂Hom (Int.castRingHom K) y)).det ≠ 0 := by
  have hp : MvPolynomial.eval₂ (Int.castRingHom S) x A.det ≠ 0 := by
    change (MvPolynomial.eval₂Hom (Int.castRingHom S) x) A.det ≠ 0
    rwa [(MvPolynomial.eval₂Hom (Int.castRingHom S) x).map_det]
  obtain ⟨y, hy⟩ := integer_polynomial_nonvanishing_descends (K := K) A.det x hp
  refine ⟨y, ?_⟩
  change (MvPolynomial.eval₂Hom (Int.castRingHom K) y) A.det ≠ 0 at hy
  rwa [(MvPolynomial.eval₂Hom (Int.castRingHom K) y).map_det] at hy

end IdealGeneration
