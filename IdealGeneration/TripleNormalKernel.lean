module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Eliminating a correction term in a kernel

When the correction term is an arbitrary element of the kernel of an
evaluation map, the corrected equation is equivalent to the evaluation of
the uncorrected equation. The equivalence preserves the first coordinate.
-/

noncomputable section
namespace IdealGeneration

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- Add an arbitrary correction from the kernel of `e` to the image of `f`. -/
def kernelAugmentation (f : A →ₗ[K] B) (e : B →ₗ[K] C) :
    (A × ↥e.ker) →ₗ[K] B :=
  f.coprod e.ker.subtype

@[simp] theorem kernelAugmentation_apply (f : A →ₗ[K] B) (e : B →ₗ[K] C)
    (a : A) (w : e.ker) :
    kernelAugmentation f e (a, w) = f a + w.val := rfl

/-- A corrected equation is zero exactly when its first coordinate solves
the evaluated equation, with the correction then uniquely determined. -/
def kernelAugmentationKerEquiv (f : A →ₗ[K] B) (e : B →ₗ[K] C) :
    (kernelAugmentation f e).ker ≃ₗ[K] (e.comp f).ker where
  toFun x := ⟨x.val.1, by
    have hx : f x.val.1 + x.val.2.val = 0 := x.property
    have he : e (f x.val.1) + e x.val.2.val = 0 := by
      simpa only [map_add, map_zero] using congrArg e hx
    have hw : e x.val.2.val = 0 := x.val.2.property
    change e (f x.val.1) = 0
    simpa only [hw, add_zero] using he⟩
  invFun a := ⟨(a.val, ⟨-f a.val, by
    change e (-f a.val) = 0
    rw [map_neg]
    exact neg_eq_zero.mpr a.property⟩), by
      change f a.val + -f a.val = 0
      exact add_neg_cancel _⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change -f x.val.1 = x.val.2.val
      have hx : f x.val.1 + x.val.2.val = 0 := x.property
      calc
        -f x.val.1 = -f x.val.1 + (f x.val.1 + x.val.2.val) := by rw [hx]; simp
        _ = x.val.2.val := by abel
  right_inv a := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' k x := by
    apply Subtype.ext
    rfl

@[simp] theorem kernelAugmentationKerEquiv_apply_val
    (f : A →ₗ[K] B) (e : B →ₗ[K] C) (x : (kernelAugmentation f e).ker) :
    (kernelAugmentationKerEquiv f e x).val = x.val.1 := rfl

@[simp] theorem kernelAugmentationKerEquiv_symm_fst
    (f : A →ₗ[K] B) (e : B →ₗ[K] C) (a : (e.comp f).ker) :
    ((kernelAugmentationKerEquiv f e).symm a).val.1 = a.val := rfl

@[simp] theorem kernelAugmentationKerEquiv_symm_snd
    (f : A →ₗ[K] B) (e : B →ₗ[K] C) (a : (e.comp f).ker) :
    ((kernelAugmentationKerEquiv f e).symm a).val.2.val = -f a.val := rfl

/-- Eliminating the correction term preserves the kernel dimension. -/
theorem finrank_kernelAugmentation (f : A →ₗ[K] B) (e : B →ₗ[K] C) :
    Module.finrank K (kernelAugmentation f e).ker =
      Module.finrank K (e.comp f).ker :=
  (kernelAugmentationKerEquiv f e).finrank_eq

end IdealGeneration
