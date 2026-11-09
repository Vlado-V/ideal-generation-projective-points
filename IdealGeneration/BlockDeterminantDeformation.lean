module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Leading determinant of a polynomial matrix after extracting a common row factor. -/

namespace IdealGeneration
open Matrix Polynomial

variable {K : Type*} [CommRing K] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Multiply the first block of rows by the deformation parameter. -/
noncomputable def scaleFirstBlockRows (B : Matrix (ι ⊕ κ) (ι ⊕ κ) K[X]) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) K[X] :=
  fun i j => Sum.elim (fun r => X * B (.inl r) j) (fun r => B (.inr r) j) i

/-- Each divided row contributes one factor of the parameter to the determinant. -/
theorem det_scaleFirstBlockRows (B : Matrix (ι ⊕ κ) (ι ⊕ κ) K[X]) :
    (scaleFirstBlockRows B).det = X ^ Fintype.card ι * B.det := by
  let d : ι ⊕ κ → K[X] := Sum.elim (fun _ => X) (fun _ => 1)
  have h : scaleFirstBlockRows B = diagonal d * B := by
    ext i j
    rw [Matrix.diagonal_mul]
    cases i <;> simp [scaleFirstBlockRows, d]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [d]

/-- If the divided matrix is block triangular at zero, the first possible
coefficient of the original determinant is the product of its two diagonal determinants. -/
theorem coeff_det_scaleFirstBlockRows
    (B : Matrix (ι ⊕ κ) (ι ⊕ κ) K[X])
    (B₁₁ : Matrix ι ι K) (B₂₁ : Matrix κ ι K) (B₂₂ : Matrix κ κ K)
    (hB : B.map (Polynomial.evalRingHom (0 : K)) = fromBlocks B₁₁ 0 B₂₁ B₂₂) :
    (scaleFirstBlockRows B).det.coeff (Fintype.card ι) = B₁₁.det * B₂₂.det := by
  rw [det_scaleFirstBlockRows]
  calc
    _ = B.det.coeff 0 := by
      simpa only [Nat.zero_add] using Polynomial.coeff_X_pow_mul B.det (Fintype.card ι) 0
    _ = (B.map (Polynomial.evalRingHom (0 : K))).det := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact (Polynomial.evalRingHom (0 : K)).map_det B
    _ = _ := by rw [hB, Matrix.det_fromBlocks_zero₁₂]

/-- The same extraction shows that all preceding coefficients vanish. -/
theorem coeff_det_scaleFirstBlockRows_of_lt
    (B : Matrix (ι ⊕ κ) (ι ⊕ κ) K[X]) {j : ℕ} (hj : j < Fintype.card ι) :
    (scaleFirstBlockRows B).det.coeff j = 0 := by
  rw [det_scaleFirstBlockRows, Polynomial.coeff_X_pow_mul', ite_eq_right (Nat.not_le.mpr hj)]

/-- Nonsingular diagonal blocks give a nonsingular specialization of the
undivided matrix over any infinite field. The parameter can be taken nonzero. -/
theorem exists_det_scaleFirstBlockRows_eval_ne_zero {F : Type*} [Field F] [Infinite F]
    (B : Matrix (ι ⊕ κ) (ι ⊕ κ) F[X])
    (B₁₁ : Matrix ι ι F) (B₂₁ : Matrix κ ι F) (B₂₂ : Matrix κ κ F)
    (hB : B.map (Polynomial.evalRingHom (0 : F)) = fromBlocks B₁₁ 0 B₂₁ B₂₂)
    (h₁₁ : B₁₁.det ≠ 0) (h₂₂ : B₂₂.det ≠ 0) :
    ∃ t : F, t ≠ 0 ∧ ((scaleFirstBlockRows B).map (Polynomial.evalRingHom t)).det ≠ 0 := by
  let p := (scaleFirstBlockRows B).det
  have hp : p ≠ 0 := by
    intro hz
    have h := coeff_det_scaleFirstBlockRows B B₁₁ B₂₁ B₂₂ hB
    change p.coeff (Fintype.card ι) = _ at h
    rw [hz, Polynomial.coeff_zero] at h
    exact mul_ne_zero h₁₁ h₂₂ h.symm
  have hXp : X * p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hp
  obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (X * p) hXp
    (Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk F))
  rw [Polynomial.eval_mul, Polynomial.eval_X, mul_ne_zero_iff] at ht
  refine ⟨t, ht.1, ?_⟩
  have hm : ((scaleFirstBlockRows B).map (Polynomial.evalRingHom t)).det = p.eval t :=
    ((Polynomial.evalRingHom t).map_det (scaleFirstBlockRows B)).symm
  rw [hm]
  exact ht.2

/-- The block expansion can be stated directly with vanishing coefficients,
without choosing divided entries separately. -/
theorem exists_block_det_eval_ne_zero {F : Type*} [Field F] [Infinite F]
    (A₁₁ : Matrix ι ι F[X]) (A₁₂ : Matrix ι κ F[X])
    (A₂₁ : Matrix κ ι F[X]) (A₂₂ : Matrix κ κ F[X])
    (h₁₁₀ : ∀ i j, (A₁₁ i j).coeff 0 = 0)
    (h₁₂₀ : ∀ i j, (A₁₂ i j).coeff 0 = 0)
    (h₁₂₁ : ∀ i j, (A₁₂ i j).coeff 1 = 0)
    (h₁₁ : (A₁₁.map fun p => p.coeff 1).det ≠ 0)
    (h₂₂ : (A₂₂.map (Polynomial.evalRingHom (0 : F))).det ≠ 0) :
    ∃ t : F, t ≠ 0 ∧
      ((fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).map (Polynomial.evalRingHom t)).det ≠ 0 := by
  let B := fromBlocks (A₁₁.map Polynomial.divX) (A₁₂.map Polynomial.divX) A₂₁ A₂₂
  have hdiv (p : F[X]) (h : p.coeff 0 = 0) : X * p.divX = p := by
    simpa only [h, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add p
  have hscale : scaleFirstBlockRows B = fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ := by
    ext i j
    cases i <;> cases j <;> simp [scaleFirstBlockRows, B, hdiv, h₁₁₀, h₁₂₀]
  have hconst : B.map (Polynomial.evalRingHom (0 : F)) =
      fromBlocks (A₁₁.map fun p => p.coeff 1) 0
        (A₂₁.map (Polynomial.evalRingHom 0)) (A₂₂.map (Polynomial.evalRingHom 0)) := by
    have heval (p : F[X]) : (p.divX).eval 0 = p.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, zero_add]
    ext i j
    cases i <;> cases j <;> simp [B, heval, h₁₂₁]
  simpa only [hscale] using exists_det_scaleFirstBlockRows_eval_ne_zero
    B _ _ _ hconst h₁₁ h₂₂

end IdealGeneration
