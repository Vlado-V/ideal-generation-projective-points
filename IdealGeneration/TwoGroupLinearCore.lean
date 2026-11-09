module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The linear algebra of two successive groups of scalar conditions

The combined kernel is the kernel of the second map on the first kernel.
Its dimension is obtained by two applications of rank-nullity. The final
count in Lemma 4.1 follows when the first projection's kernel has dimension
at most the number of rows in either group.
-/

noncomputable section
namespace IdealGeneration.TwoGroup
open Module

variable {K U A B C D : Type*} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
  [AddCommGroup D] [Module K D]

/-- Restrict the second family of conditions to the first kernel. -/
def secondStage (f : U →ₗ[K] C) (g : U →ₗ[K] D) : f.ker →ₗ[K] D :=
  g.comp f.ker.subtype

/-- Imposing both groups at once agrees with imposing them successively. -/
def combinedKernelEquiv (f : U →ₗ[K] C) (g : U →ₗ[K] D) :
    (f.prod g).ker ≃ₗ[K] (secondStage f g).ker where
  toFun x := ⟨⟨x.val, by
    have h := congrArg Prod.fst x.property
    exact h⟩, by
    have h := congrArg Prod.snd x.property
    exact h⟩
  invFun x := ⟨x.val.val, by
    change (f x.val.val, g x.val.val) = (0, 0)
    exact Prod.ext x.val.property x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The dimension left after the second group is a second rank-nullity subtraction. -/
theorem combinedKernel_finrank [FiniteDimensional K U]
    (f : U →ₗ[K] C) (g : U →ₗ[K] D) :
    finrank K (f.prod g).ker =
      finrank K f.ker - finrank K (secondStage f g).range := by
  have heq := (combinedKernelEquiv f g).finrank_eq
  have hr := (secondStage f g).finrank_range_add_finrank_ker
  omega

/-- A second projection is injective on the first kernel precisely when the
first conditions are injective on the second projection's kernel. -/
theorem secondStage_injective_symm (f : U →ₗ[K] C) (g : U →ₗ[K] D) :
    Function.Injective (secondStage f g) ↔ Function.Injective (secondStage g f) := by
  constructor
  · intro h x y hxy
    let z : f.ker := ⟨x.val - y.val, by
      change f (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy⟩
    have hz : secondStage f g z = secondStage f g 0 := by
      change g (x.val - y.val) = g 0
      rw [map_sub, x.property, y.property, map_zero, sub_self]
    have hz0 : z = 0 := h hz
    apply Subtype.ext
    exact sub_eq_zero.mp (congrArg Subtype.val hz0)
  · intro h x y hxy
    let z : g.ker := ⟨x.val - y.val, by
      change g (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy⟩
    have hz : secondStage g f z = secondStage g f 0 := by
      change f (x.val - y.val) = f 0
      rw [map_sub, x.property, y.property, map_zero, sub_self]
    have hz0 : z = 0 := h hz
    apply Subtype.ext
    exact sub_eq_zero.mp (congrArg Subtype.val hz0)

/-- Passing through the range of a map does not change the image of its composite. -/
theorem range_comp_eq_range_on_image (f : U →ₗ[K] A) (e : A →ₗ[K] B) :
    (e.comp f).range = (e.comp f.range.subtype).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨f x, ⟨x, rfl⟩⟩, rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu⟩ := x.property
    refine ⟨u, ?_⟩
    change e (f u) = y
    rw [hu]
    exact hx

/-- The numerical conclusion of the two-group interpolation argument.
The first group has maximal rank on the first projection. The second has
maximal rank on the first kernel. -/
theorem two_group_kernel_finrank [FiniteDimensional K U]
    (pa : U →ₗ[K] A) (f : U →ₗ[K] C) (g : U →ₗ[K] D) (b : ℕ)
    (hsmall : finrank K pa.ker ≤ b)
    (hfirst : finrank K f.range = min (finrank K pa.range) b)
    (hsecond : finrank K (secondStage f g).range = min (finrank K f.ker) b) :
    finrank K (f.prod g).ker = finrank K U - 2 * b := by
  have hp := pa.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hboth := combinedKernel_finrank f g
  rw [hfirst] at hf
  rw [hsecond] at hboth
  omega

/-- The first-stage dimension in the notation of Lemma 4.1. -/
theorem first_kernel_finrank [FiniteDimensional K U]
    (pa : U →ₗ[K] A) (f : U →ₗ[K] C) (b : ℕ)
    (hfirst : finrank K f.range = min (finrank K pa.range) b) :
    finrank K f.ker = max (finrank K U - b) (finrank K pa.ker) := by
  have hp := pa.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  rw [hfirst] at hf
  omega


section AddCommMonoid

variable {K U A C D : Type*} [Field K]
  [AddCommMonoid U] [Module K U]
  [AddCommMonoid A] [Module K A]
  [AddCommMonoid C] [Module K C]
  [AddCommMonoid D] [Module K D]

/-- Rank-nullity with the original additive-monoid instances retained.
The canonical additive-group structure is induced by scalar multiplication. -/
theorem rank_nullity_monoid [Module.Finite K U] (f : U →ₗ[K] C) :
    finrank K f.range + finrank K f.ker = finrank K U := by
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  exact f.finrank_range_add_finrank_ker

/-- The symmetry of the restricted-kernel injectivity criterion, retaining the
additive instances supplied by the caller. -/
theorem secondStage_injective_symm_monoid (f : U →ₗ[K] C) (g : U →ₗ[K] D) :
    Function.Injective (g.comp f.ker.subtype) ↔
      Function.Injective (f.comp g.ker.subtype) := by
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup D := Module.addCommMonoidToAddCommGroup K
  exact secondStage_injective_symm f g

/-- The two-group dimension formula with additive-monoid-compatible signatures. -/
theorem two_group_kernel_finrank_monoid [Module.Finite K U]
    (pa : U →ₗ[K] A) (f : U →ₗ[K] C) (g : U →ₗ[K] D) (b : ℕ)
    (hsmall : finrank K pa.ker ≤ b)
    (hfirst : finrank K f.range = min (finrank K pa.range) b)
    (hsecond : finrank K (g.comp f.ker.subtype).range = min (finrank K f.ker) b) :
    finrank K (f.prod g).ker = finrank K U - 2 * b := by
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup D := Module.addCommMonoidToAddCommGroup K
  exact two_group_kernel_finrank pa f g b hsmall hfirst hsecond

end AddCommMonoid

end IdealGeneration.TwoGroup
