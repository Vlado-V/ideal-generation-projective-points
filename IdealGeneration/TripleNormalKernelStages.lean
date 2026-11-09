module

public import IdealGeneration.TripleNormalKernel
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact linear kernel reductions used by normal-degree elimination. -/
noncomputable section
namespace IdealGeneration
variable {K A B V Y Z : Type*} [Field K]
  [AddCommMonoid A] [Module K A] [AddCommMonoid B] [Module K B]
  [AddCommMonoid V] [Module K V] [AddCommMonoid Y] [Module K Y]
  [AddCommMonoid Z] [Module K Z]

/-- Restrict the first source component to the kernel of its leading constraint. -/
def firstKernelRestricted (r : A →ₗ[K] Z) (F : (A × B) →ₗ[K] Y) :
    (r.ker × B) →ₗ[K] Y :=
  F.comp ((r.ker.subtype).prodMap (LinearMap.id : B →ₗ[K] B))

/-- If a leading output component detects only the first source component,
vanishing of the full output forces that first component into its kernel. -/
def firstKernelReduction (r : A →ₗ[K] Z) (F : (A × B) →ₗ[K] Y)
    (g : Y →ₗ[K] Z) (h : ∀ a b, g (F (a, b)) = r a) :
    F.ker ≃ₗ[K] (firstKernelRestricted r F).ker where
  toFun x := ⟨(⟨x.val.1, by
    change r x.val.1 = 0
    have hx : F (x.val.1, x.val.2) = 0 := x.property
    rw [← h x.val.1 x.val.2, hx, map_zero]⟩, x.val.2), x.property⟩
  invFun x := ⟨(x.val.1.val, x.val.2), x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

private theorem add_neg_one_smul_cancel (x y : B) : x + y + (-1 : K) • y = x := by
  calc
    _ = x + ((1 : K) • y + (-1 : K) • y) := by simp [add_assoc]
    _ = x := by rw [← add_smul]; simp

/-- Solve a triangular constraint using a specified section of its second block. -/
def triangularSource (r : A →ₗ[K] Z) (q : B →ₗ[K] Z) (L : Z →ₗ[K] B) :
    (A × (q.ker × V)) →ₗ[K] (A × (B × V)) where
  toFun x := (x.1, (x.2.1.val + (-1 : K) • L (r x.1), x.2.2))
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (x.2.1.val + y.2.1.val) + (-1 : K) • L (r (x.1 + y.1)) =
          (x.2.1.val + (-1 : K) • L (r x.1)) + (y.2.1.val + (-1 : K) • L (r y.1))
        simp only [map_add, smul_add]
        ac_rfl
      · rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change a • x.2.1.val + (-1 : K) • L (r (a • x.1)) =
          a • (x.2.1.val + (-1 : K) • L (r x.1))
        simp [smul_add, smul_smul, mul_comm]
      · rfl

/-- A second leading component `r a+q b` determines the lifted part of `b`
uniquely and leaves its kernel component free. -/
def triangularKernelReduction (r : A →ₗ[K] Z) (q : B →ₗ[K] Z)
    (L : Z →ₗ[K] B) (hL : ∀ z, q (L z) = z)
    (F : (A × (B × V)) →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (h : ∀ a b v, g (F (a, (b, v))) = r a + q b) :
    F.ker ≃ₗ[K] (F.comp (triangularSource r q L)).ker where
  toFun x := ⟨(x.val.1, (⟨x.val.2.1 + L (r x.val.1), by
      change q (x.val.2.1 + L (r x.val.1)) = 0
      have hx : F (x.val.1, (x.val.2.1, x.val.2.2)) = 0 := x.property
      rw [map_add, hL, add_comm, ← h x.val.1 x.val.2.1 x.val.2.2, hx, map_zero]⟩, x.val.2.2)), by
      change F (x.val.1, (x.val.2.1 + L (r x.val.1) + (-1 : K) • L (r x.val.1), x.val.2.2)) = 0
      rw [add_neg_one_smul_cancel]
      exact x.property⟩
  invFun x := ⟨triangularSource r q L x.val, x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact add_neg_one_smul_cancel (K := K) _ _
      · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        change x.val.2.1.val + (-1 : K) • L (r x.val.1) + L (r x.val.1) = x.val.2.1.val
        calc
          _ = x.val.2.1.val + L (r x.val.1) + (-1 : K) • L (r x.val.1) := by ac_rfl
          _ = _ := add_neg_one_smul_cancel (K := K) _ _
      · rfl
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        change x.val.2.1 + y.val.2.1 + L (r (x.val.1 + y.val.1)) =
          (x.val.2.1 + L (r x.val.1)) + (y.val.2.1 + L (r y.val.1))
        simp only [map_add]
        ac_rfl
      · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        change a • x.val.2.1 + L (r (a • x.val.1)) =
          a • (x.val.2.1 + L (r x.val.1))
        simp only [map_smul, smul_add]
      · rfl

/-- A source-coordinate equivalence transports the actual kernel. -/
def kernelSourceEquiv (e : A ≃ₗ[K] B) (F : A →ₗ[K] Y) (G : B →ₗ[K] Y)
    (h : ∀ a, G (e a) = F a) : F.ker ≃ₗ[K] G.ker where
  toFun x := ⟨e x.val, (h x.val).trans x.property⟩
  invFun x := ⟨e.symm x.val, by
    change F (e.symm x.val) = 0
    rw [← h, LinearEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' a x := Subtype.ext (map_smul e a x.val)

/-- Injectivity depends only on the additive-monoid presentation of the kernel. -/
theorem linearMap_injective_iff_kernel_subsingleton (F : A →ₗ[K] Y) :
    Function.Injective F ↔ Subsingleton F.ker := by
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup Y := Module.addCommMonoidToAddCommGroup K
  rw [Submodule.subsingleton_iff_eq_bot]
  exact (LinearMap.ker_eq_bot (f := F)).symm

end IdealGeneration
