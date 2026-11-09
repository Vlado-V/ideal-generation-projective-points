module

public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A pivot and free-coordinate block parametrizes the actual matrix kernel. -/

namespace IdealGeneration.MatrixKernelFree
open Matrix

variable {F κ ν r : Type*} [Ring F]
  [Fintype κ] [Fintype ν] [Fintype r] [DecidableEq r]

/-- A vector in the kernel is reconstructed from its free coordinates. -/
theorem mulVec_free_eq_of_kernel
    (E : Matrix κ ν F) (B : Matrix ν r F) (e : κ ⊕ r ≃ ν)
    (hE : Function.Injective (E.submatrix id (fun i : κ => e (Sum.inl i))).mulVec)
    (hB : E * B = 0)
    (hfree : B.submatrix (fun j : r => e (Sum.inr j)) id = 1)
    (u : ν → F) (hu : E *ᵥ u = 0) :
    B *ᵥ (u ∘ (fun j : r => e (Sum.inr j))) = u := by
  let v : r → F := u ∘ (fun j : r => e (Sum.inr j))
  let w : ν → F := u - B *ᵥ v
  have hBfree : (B *ᵥ v) ∘ (fun j : r => e (Sum.inr j)) = v := by
    have h := Matrix.submatrix_mulVec_equiv B v (fun j : r => e (Sum.inr j)) (Equiv.refl r)
    change (B.submatrix (fun j : r => e (Sum.inr j)) id) *ᵥ v =
      (B *ᵥ v) ∘ (fun j : r => e (Sum.inr j)) at h
    rw [hfree, Matrix.one_mulVec] at h
    exact h.symm
  have hwfree : w ∘ (fun j : r => e (Sum.inr j)) = 0 := by
    funext j
    change u (e (Sum.inr j)) - (B *ᵥ v) (e (Sum.inr j)) = 0
    have hj : (B *ᵥ v) (e (Sum.inr j)) = u (e (Sum.inr j)) := congrFun hBfree j
    rw [hj, sub_self]
  have hEw : E *ᵥ w = 0 := by
    change E *ᵥ (u - B *ᵥ v) = 0
    rw [Matrix.mulVec_sub, hu, Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec, sub_zero]
  have hwcomp : (w ∘ e) ∘ e.symm = w := by
    funext i
    simp [Function.comp_def]
  have hreindex : E.submatrix id e *ᵥ (w ∘ e) = 0 := by
    have h := Matrix.submatrix_mulVec_equiv E (w ∘ e) id e
    rw [hwcomp, hEw] at h
    exact h
  have hsplit : E.submatrix id e = Matrix.fromCols
      (E.submatrix id (fun i : κ => e (Sum.inl i)))
      (E.submatrix id (fun j : r => e (Sum.inr j))) := by
    ext i j
    cases j <;> rfl
  rw [hsplit, Matrix.fromCols_mulVec] at hreindex
  have hwfree' : (w ∘ e) ∘ Sum.inr = 0 := hwfree
  rw [hwfree', Matrix.mulVec_zero, add_zero] at hreindex
  have hwpivot : (w ∘ e) ∘ Sum.inl = 0 := hE (by
    rw [Matrix.mulVec_zero]
    exact hreindex)
  have hw : w = 0 := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j => exact congrFun hwpivot j
    | inr j => exact congrFun hwfree j
  have hd : u - B *ᵥ v = 0 := hw
  exact (sub_eq_zero.mp hd).symm

/-- The columns with identity free-coordinate block span the whole kernel. -/
theorem exists_mulVec_eq_of_kernel
    (E : Matrix κ ν F) (B : Matrix ν r F) (e : κ ⊕ r ≃ ν)
    (hE : Function.Injective (E.submatrix id (fun i : κ => e (Sum.inl i))).mulVec)
    (hB : E * B = 0)
    (hfree : B.submatrix (fun j : r => e (Sum.inr j)) id = 1)
    (u : ν → F) (hu : E *ᵥ u = 0) : ∃ v : r → F, B *ᵥ v = u :=
  ⟨_, mulVec_free_eq_of_kernel E B e hE hB hfree u hu⟩

end IdealGeneration.MatrixKernelFree
