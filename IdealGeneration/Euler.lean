module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The linear algebra of Euler evaluation

A commutative square induces a map on the kernels of its vertical arrows and
another map on the kernels of its horizontal arrows. Their kernels agree.
If the top and left arrows are surjective, surjectivity of either induced map
is equivalent to surjectivity of the other. This is the diagram chase used in
Lemma 2.2 of the supplied paper.
-/

namespace IdealGeneration

variable {k A B C D : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]

/-- The four linear maps in a commutative square. -/
structure LinearSquare (k A B C D : Type*) [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D] where
  top : A →ₗ[k] B
  left : A →ₗ[k] C
  right : B →ₗ[k] D
  bottom : C →ₗ[k] D
  commutes : ∀ a, right (top a) = bottom (left a)

namespace LinearSquare

variable (s : LinearSquare k A B C D)

/-- The top arrow restricted to the kernels of the vertical arrows. -/
def topOnKernel : LinearMap.ker s.left →ₗ[k] LinearMap.ker s.right where
  toFun a := ⟨s.top a, by
    rw [LinearMap.mem_ker, s.commutes, LinearMap.mem_ker.mp a.property, map_zero]⟩
  map_add' a b := Subtype.ext (s.top.map_add a b)
  map_smul' c a := Subtype.ext (s.top.map_smul c a)

/-- The left arrow restricted to the kernels of the horizontal arrows. -/
def leftOnKernel : LinearMap.ker s.top →ₗ[k] LinearMap.ker s.bottom where
  toFun a := ⟨s.left a, by
    rw [LinearMap.mem_ker, ← s.commutes, LinearMap.mem_ker.mp a.property, map_zero]⟩
  map_add' a b := Subtype.ext (s.left.map_add a b)
  map_smul' c a := Subtype.ext (s.left.map_smul c a)

@[simp] theorem topOnKernel_coe (a : LinearMap.ker s.left) :
    (s.topOnKernel a : B) = s.top a := rfl

@[simp] theorem leftOnKernel_coe (a : LinearMap.ker s.top) :
    (s.leftOnKernel a : C) = s.left a := rfl

/-- Both induced kernels describe the intersection of the two kernels in `A`. -/
def kernelEquiv : LinearMap.ker s.topOnKernel ≃ₗ[k] LinearMap.ker s.leftOnKernel where
  toFun a := ⟨⟨a.val.val, by
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp a.property)
    exact h⟩, by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact LinearMap.mem_ker.mp a.val.property⟩
  invFun a := ⟨⟨a.val.val, by
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp a.property)
    exact h⟩, by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact LinearMap.mem_ker.mp a.val.property⟩
  left_inv a := rfl
  right_inv a := rfl
  map_add' a b := rfl
  map_smul' c a := rfl

/-- Injectivity transfers across the square without any surjectivity hypotheses. -/
theorem injective_iff : Function.Injective s.topOnKernel ↔
    Function.Injective s.leftOnKernel := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot]
  constructor
  · intro h
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have ht : s.top a = 0 := LinearMap.mem_ker.mp a.property
    have hl : s.left a = 0 := congrArg Subtype.val ha
    have hb : (⟨a.val, hl⟩ : LinearMap.ker s.left) = 0 :=
      LinearMap.ker_eq_bot'.mp h _ (Subtype.ext ht)
    apply Subtype.ext
    exact congrArg (fun x : LinearMap.ker s.left => x.val) hb
  · intro h
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have hl : s.left a = 0 := LinearMap.mem_ker.mp a.property
    have ht : s.top a = 0 := congrArg Subtype.val ha
    have hb : (⟨a.val, ht⟩ : LinearMap.ker s.top) = 0 :=
      LinearMap.ker_eq_bot'.mp h _ (Subtype.ext hl)
    apply Subtype.ext
    exact congrArg (fun x : LinearMap.ker s.top => x.val) hb

/-- Surjectivity of multiplication implies surjectivity of Euler evaluation. -/
theorem leftOnKernel_surjective (hleft : Function.Surjective s.left)
    (htop : Function.Surjective s.topOnKernel) : Function.Surjective s.leftOnKernel := by
  intro c
  obtain ⟨a, ha⟩ := hleft c.val
  have hb : s.top a ∈ LinearMap.ker s.right := by
    rw [LinearMap.mem_ker, s.commutes, ha]
    exact c.property
  obtain ⟨a', ha'⟩ := htop ⟨s.top a, hb⟩
  have ht : s.top (a - a'.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val ha').symm
  refine ⟨⟨a - a'.val, ht⟩, ?_⟩
  apply Subtype.ext
  change s.left (a - a'.val) = c.val
  rw [map_sub, ha, LinearMap.mem_ker.mp a'.property, sub_zero]

/-- Surjectivity of Euler evaluation implies surjectivity of multiplication. -/
theorem topOnKernel_surjective (htop : Function.Surjective s.top)
    (hleft : Function.Surjective s.leftOnKernel) : Function.Surjective s.topOnKernel := by
  intro b
  obtain ⟨a, ha⟩ := htop b.val
  have hc : s.left a ∈ LinearMap.ker s.bottom := by
    rw [LinearMap.mem_ker, ← s.commutes, ha]
    exact b.property
  obtain ⟨a', ha'⟩ := hleft ⟨s.left a, hc⟩
  have hl : s.left (a - a'.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val ha').symm
  refine ⟨⟨a - a'.val, hl⟩, ?_⟩
  apply Subtype.ext
  change s.top (a - a'.val) = b.val
  rw [map_sub, ha, LinearMap.mem_ker.mp a'.property, sub_zero]

/-- The surjectivity conclusion in the Euler comparison. -/
theorem surjective_iff (htop : Function.Surjective s.top)
    (hleft : Function.Surjective s.left) :
    Function.Surjective s.topOnKernel ↔ Function.Surjective s.leftOnKernel :=
  ⟨s.leftOnKernel_surjective hleft, s.topOnKernel_surjective htop⟩

/-- The maximal-rank conclusion in the Euler comparison. -/
theorem maximalRank_iff (htop : Function.Surjective s.top)
    (hleft : Function.Surjective s.left) :
    (Function.Injective s.topOnKernel ∨ Function.Surjective s.topOnKernel) ↔
    (Function.Injective s.leftOnKernel ∨ Function.Surjective s.leftOnKernel) := by
  rw [s.injective_iff, s.surjective_iff htop hleft]

end LinearSquare
end IdealGeneration
