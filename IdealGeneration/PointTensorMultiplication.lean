module

public import IdealGeneration.MainStatement
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Tensor-product multiplication for the homogeneous pieces of a point ideal. -/

noncomputable section
namespace IdealGeneration

open Module MvPolynomial
open scoped TensorProduct

variable {K : Type*} [Field K] {n p : ℕ}

/-- The degree-one monomial basis indexed by the coordinate variables. -/
def coordinateLinearBasis (K : Type*) [Field K] (n : ℕ) : Basis (Fin n) K (Forms K n 1) :=
  (formsBasis K n 1).reindex Sym.oneEquiv.symm

@[simp] theorem coordinateLinearBasis_val (i : Fin n) :
    (coordinateLinearBasis K n i).val = (X i : Poly K n) := by
  rw [coordinateLinearBasis, Basis.reindex_apply, Equiv.symm_symm, formsBasis_val_monomial]
  have h : (exponentEquiv n 1 (Sym.oneEquiv i)).val = Finsupp.single i 1 := by
    change Multiset.toFinsupp ({i} : Multiset (Fin n)) = Finsupp.single i 1
    exact Multiset.toFinsupp_singleton i
  rw [h]
  rfl

/-- A tuple of ideal equations represents their tensor with the coordinate basis of linear forms. -/
def pointMultiplicationTensorEquiv (a : PointCoordinates K n p) (d : ℕ) :
    (Fin (n + 1) → pointDegreePiece K a d) ≃ₗ[K]
      (pointDegreePiece K a d ⊗[K] Forms K (n + 1) 1) :=
  ((TensorProduct.equivFinsuppOfBasisRight (M := pointDegreePiece K a d)
    (coordinateLinearBasis K (n + 1))).trans
      (Finsupp.linearEquivFunOnFinite K (pointDegreePiece K a d) (Fin (n + 1)))).symm

theorem pointMultiplicationTensorEquiv_apply (a : PointCoordinates K n p) (d : ℕ)
    (f : Fin (n + 1) → pointDegreePiece K a d) :
    pointMultiplicationTensorEquiv a d f =
      ∑ j, f j ⊗ₜ[K] coordinateLinearBasis K (n + 1) j := by
  rw [pointMultiplicationTensorEquiv, LinearEquiv.symm_trans_apply,
    TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
  · simp only [Finsupp.linearEquivFunOnFinite_symm_apply]
  · intro j
    exact TensorProduct.zero_tmul _ _

private def pointMultiplicationBilinear (a : PointCoordinates K n p) (d : ℕ) :
    pointDegreePiece K a d →ₗ[K] Forms K (n + 1) 1 →ₗ[K] pointDegreePiece K a (d + 1) where
  toFun f := (mulForm f.val).codRestrict _ fun g => by
    apply (mem_pointDegreePiece a _).mpr
    intro i
    rw [mulForm_val, map_mul, (mem_pointDegreePiece a _).mp f.property i, zero_mul]
  map_add' f g := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    apply Subtype.ext
    exact add_mul f.val.val g.val.val u.val
  map_smul' c f := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    apply Subtype.ext
    exact smul_mul_assoc c f.val.val u.val

/-- Multiplication from the degree-`d` ideal piece tensored with the linear forms. -/
def pointTensorMultiplication (a : PointCoordinates K n p) (d : ℕ) :
    (pointDegreePiece K a d ⊗[K] Forms K (n + 1) 1) →ₗ[K] pointDegreePiece K a (d + 1) :=
  TensorProduct.lift (pointMultiplicationBilinear a d)

@[simp] theorem pointTensorMultiplication_tmul {d : ℕ} (a : PointCoordinates K n p)
    (f : pointDegreePiece K a d) (g : Forms K (n + 1) 1) :
    (pointTensorMultiplication a d (f ⊗ₜ[K] g)).val.val = f.val.val * g.val := by
  rw [pointTensorMultiplication, TensorProduct.lift.tmul]
  rfl

/-- The tensor multiplication agrees with multiplication of coordinate tuples. -/
theorem pointTensorMultiplication_comp_tensorEquiv (a : PointCoordinates K n p) (d : ℕ) :
    (pointTensorMultiplication a d).comp (pointMultiplicationTensorEquiv a d).toLinearMap =
      pointMultiplication a d := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  change (pointTensorMultiplication a d (pointMultiplicationTensorEquiv a d f)).val.val = _
  simp only [pointMultiplicationTensorEquiv_apply, map_sum, Submodule.coe_sum,
    pointTensorMultiplication_tmul, coordinateLinearBasis_val, pointMultiplication_val]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Passing from coordinates to tensors preserves maximal rank. -/
theorem pointTensorMultiplication_maximalRank_iff (a : PointCoordinates K n p) (d : ℕ) :
    HasMaximalRank (pointTensorMultiplication a d) ↔ HasMaximalRank (pointMultiplication a d) := by
  let f := pointTensorMultiplication a d
  let e := (pointMultiplicationTensorEquiv a d).toEquiv
  unfold HasMaximalRank
  rw [← pointTensorMultiplication_comp_tensorEquiv a d]
  change (Function.Injective f ∨ Function.Surjective f) ↔
    (Function.Injective (f ∘ e) ∨ Function.Surjective (f ∘ e))
  rw [e.injective_comp, e.surjective_comp]

/-- The same principal open proves the tensor formulation of point-ideal generation. -/
theorem idealGenerationAt_tensor_iff (n d p : ℕ) :
    IdealGenerationAt K n d p ↔
      ∃ Δ : MvPolynomial (Fin p × Fin n) K,
        (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
        ∀ a : PointCoordinates K n p, eval a Δ ≠ 0 →
          DistinctPoints K a ∧
          (∀ j, pointHilbertFunction K a j = min ((n + j).choose j) p) ∧
          HasMaximalRank (pointTensorMultiplication a d) := by
  simp only [IdealGenerationAt, pointTensorMultiplication_maximalRank_iff]

end IdealGeneration
