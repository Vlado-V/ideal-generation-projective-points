module

public import IdealGeneration.IntegerKernelChart
public import IdealGeneration.MatrixKernelFree
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Normalized free-coordinate charts formed from selected pivot rows and columns. -/

noncomputable section
namespace IdealGeneration.SelectedKernelChart
open Matrix Module IntegerKernelChart

variable {m ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The columns are ordered as pivot columns followed by free columns.
The rows may be selected from a larger list of equations. -/
def kernelMatrix {R : Type*} [CommRing R] (A : Matrix m (ι ⊕ κ) R) (rows : ι → m) :
    Matrix (ι ⊕ κ) κ R :=
  normalizedKernelMatrix (A.submatrix rows Sum.inl)⁻¹ (A.submatrix rows Sum.inr)

private theorem inverse_map_of_unit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Matrix ι ι R) (hP : IsUnit P.det) :
    P⁻¹.map f = (P.map f)⁻¹ := by
  have h : P⁻¹.map f * P.map f = 1 := by
    rw [← Matrix.map_mul, P.nonsing_inv_mul hP]
    exact f.mapMatrix.map_one
  exact (Matrix.inv_eq_left_inv h).symm

/-- Inverting a unit pivot commutes with any coefficient map. -/
theorem kernelMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix m (ι ⊕ κ) R) (rows : ι → m)
    (hP : IsUnit (A.submatrix rows Sum.inl).det) :
    (kernelMatrix A rows).map f = kernelMatrix (A.map f) rows := by
  let P := A.submatrix rows Sum.inl
  let Q := A.submatrix rows Sum.inr
  have hPmap : P⁻¹.map f = (P.map f)⁻¹ := inverse_map_of_unit f P hP
  have hprod : (P⁻¹ * Q).map f = (P.map f)⁻¹ * Q.map f := by
    rw [Matrix.map_mul, hPmap]
  have hmul : (-(P⁻¹ * Q)).map f = -((P.map f)⁻¹ * Q.map f) := by
    ext i j
    change f (-((P⁻¹ * Q) i j)) = -(((P.map f)⁻¹ * Q.map f) i j)
    rw [map_neg]
    exact congrArg Neg.neg (congrArg (fun M : Matrix ι κ S => M i j) hprod)
  ext i j
  rcases i with i | i
  · exact congrArg (fun M : Matrix ι κ S => M i j) hmul
  · change f ((1 : Matrix κ κ R) i j) = (1 : Matrix κ κ S) i j
    exact congrArg (fun M : Matrix κ κ S => M i j) f.mapMatrix.map_one

variable {K : Type*} [Field K] [Fintype m]

omit [DecidableEq κ] [Fintype m] in
/-- When the full rank is bounded by the pivot size, the selected rows
impose every equation of the original matrix. -/
theorem selected_rows_ker_eq (A : Matrix m (ι ⊕ κ) K) (rows : ι → m)
    (hP : (A.submatrix rows Sum.inl).det ≠ 0)
    (hr : A.rank ≤ Fintype.card ι) :
    (A.submatrix rows id).mulVecLin.ker = A.mulVecLin.ker := by
  let B := A.submatrix rows id
  have hle : A.mulVecLin.ker ≤ B.mulVecLin.ker := by
    intro u hu
    change A *ᵥ u = 0 at hu
    change B *ᵥ u = 0
    have hB := Matrix.submatrix_mulVec_equiv A u rows (Equiv.refl (ι ⊕ κ))
    change B *ᵥ u = (A *ᵥ (u ∘ (Equiv.refl (ι ⊕ κ)).symm)) ∘ rows at hB
    rw [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, hu] at hB
    exact hB
  have hp : (B.submatrix id Sum.inl).rank = Fintype.card ι :=
    Matrix.rank_of_det_ne_zero hP
  have hrB : B.rank = Fintype.card ι := by
    refine le_antisymm (Matrix.rank_le_card_height B) ?_
    simpa only [hp] using B.rank_submatrix_le id (Sum.inl : ι → ι ⊕ κ)
  have hrA : A.rank = Fintype.card ι := by
    refine le_antisymm hr ?_
    have h : B.rank ≤ A.rank := A.rank_submatrix_le rows id
    rwa [hrB] at h
  have ha := A.mulVecLin.finrank_range_add_finrank_ker
  have hb := B.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + _ = _ at ha
  change B.rank + _ = _ at hb
  rw [hrA] at ha
  rw [hrB] at hb
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

omit [Fintype m] in
/-- The normalized chart spans the kernel of the full matrix at the same
rank bound, with no additional equations on the free coordinates. -/
theorem kernelMatrix_range_eq_ker (A : Matrix m (ι ⊕ κ) K) (rows : ι → m)
    (hP : (A.submatrix rows Sum.inl).det ≠ 0)
    (hr : A.rank ≤ Fintype.card ι) :
    (kernelMatrix A rows).mulVecLin.range = A.mulVecLin.ker := by
  let P := A.submatrix rows Sum.inl
  let Q := A.submatrix rows Sum.inr
  let B := A.submatrix rows id
  let D := kernelMatrix A rows
  have hsplit : B = Matrix.fromCols P Q := by
    ext i j
    cases j <;> rfl
  have hmul : B * D = 0 := by
    change B * normalizedKernelMatrix P⁻¹ Q = 0
    rw [hsplit, normalizedKernelMatrix, Matrix.fromCols_mul_fromRows, Matrix.mul_neg,
      ← Matrix.mul_assoc, P.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have hfree : D.submatrix Sum.inr id = 1 := by
    ext i j
    rfl
  change D.mulVecLin.range = A.mulVecLin.ker
  rw [← selected_rows_ker_eq A rows hP hr]
  change D.mulVecLin.range = B.mulVecLin.ker
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    change B *ᵥ (D *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, hmul, Matrix.zero_mulVec]
  · intro hu
    change B *ᵥ u = 0 at hu
    exact MatrixKernelFree.exists_mulVec_eq_of_kernel B D (Equiv.refl _)
      (Matrix.mulVec_injective_of_det_ne_zero hP) hmul hfree u hu

end IdealGeneration.SelectedKernelChart
