module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Linear splittings with a specified section

The equivalence here records both components of a split restriction map.
The second component remains a subspace of the original ambient space.
-/

noncomputable section
namespace IdealGeneration

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A restriction map with a section splits every compatible subspace into its
trace and its intersection with the restriction kernel. -/
def submoduleSectionKernelEquiv (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W)
    (hρ : ∀ v ∈ I, ρ v ∈ J) (hL : ∀ w ∈ J, L w ∈ I) :
    I ≃ₗ[K] J × ↥(I ⊓ LinearMap.ker ρ) where
  toFun v := (⟨ρ v, hρ v v.property⟩,
    ⟨v.val - L (ρ v),
      I.sub_mem v.property (hL _ (hρ v v.property)), by simp [hsection]⟩)
  invFun w := ⟨L w.1.val + w.2.val, I.add_mem (hL _ w.1.property) w.2.property.1⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Prod.ext
    · apply Subtype.ext
      change ρ (L w.1.val + w.2.val) = w.1.val
      rw [map_add, hsection, LinearMap.mem_ker.mp w.2.property.2, add_zero]
    · apply Subtype.ext
      change L w.1.val + w.2.val - L (ρ (L w.1.val + w.2.val)) = w.2.val
      rw [map_add, hsection, LinearMap.mem_ker.mp w.2.property.2, add_zero]
      abel
  map_add' v v' := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add ρ v.val v'.val
    · apply Subtype.ext
      change (v.val + v'.val) - L (ρ (v.val + v'.val)) =
        (v.val - L (ρ v.val)) + (v'.val - L (ρ v'.val))
      simp only [map_add]
      abel
  map_smul' a v := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_smul ρ a v.val
    · apply Subtype.ext
      change a • v.val - L (ρ (a • v.val)) = a • (v.val - L (ρ v.val))
      simp only [map_smul, smul_sub]

@[simp] theorem submoduleSectionKernelEquiv_fst
    (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W)
    (hρ : ∀ v ∈ I, ρ v ∈ J) (hL : ∀ w ∈ J, L w ∈ I) (v : I) :
    (submoduleSectionKernelEquiv ρ L hsection I J hρ hL v).1.val = ρ v := rfl

@[simp] theorem submoduleSectionKernelEquiv_snd
    (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W)
    (hρ : ∀ v ∈ I, ρ v ∈ J) (hL : ∀ w ∈ J, L w ∈ I) (v : I) :
    (submoduleSectionKernelEquiv ρ L hsection I J hρ hL v).2.val =
      v.val - L (ρ v) := rfl

@[simp] theorem submoduleSectionKernelEquiv_symm
    (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W)
    (hρ : ∀ v ∈ I, ρ v ∈ J) (hL : ∀ w ∈ J, L w ∈ I)
    (w : J × ↥(I ⊓ LinearMap.ker ρ)) :
    ((submoduleSectionKernelEquiv ρ L hsection I J hρ hL).symm w).val =
      L w.1.val + w.2.val := rfl

/-- The splitting is an internal direct sum in the original ambient space. -/
theorem submodule_eq_map_sup_inf_ker
    (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W)
    (hρ : ∀ v ∈ I, ρ v ∈ J) (hL : ∀ w ∈ J, L w ∈ I) :
    I = J.map L ⊔ (I ⊓ LinearMap.ker ρ) := by
  apply le_antisymm
  · intro v hv
    have hfirst : L (ρ v) ∈ J.map L := ⟨ρ v, hρ v hv, rfl⟩
    have hsecond : v - L (ρ v) ∈ I ⊓ LinearMap.ker ρ :=
      ⟨I.sub_mem hv (hL _ (hρ v hv)), by simp [hsection]⟩
    convert Submodule.add_mem_sup hfirst hsecond using 1
    abel
  · apply sup_le
    · rintro _ ⟨w, hw, rfl⟩
      exact hL w hw
    · exact inf_le_left

/-- The lifted trace has zero intersection with the restriction kernel. -/
theorem disjoint_map_inf_ker_of_section
    (ρ : V →ₗ[K] W) (L : W →ₗ[K] V)
    (hsection : ∀ w, ρ (L w) = w) (I : Submodule K V) (J : Submodule K W) :
    Disjoint (J.map L) (I ⊓ LinearMap.ker ρ) := by
  rw [Submodule.disjoint_def]
  rintro v ⟨w, hw, rfl⟩ hv
  have hwzero : w = 0 := by
    rw [← hsection w]
    exact LinearMap.mem_ker.mp hv.2
  simp [hwzero]

section Coordinates

variable {A B C : Type*} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

/-- Regroup a tuple of split vectors by putting the trace coefficients of the
last coordinates first, followed by all residual coefficients and the trace
coefficients of the first coordinates. -/
def coordinateSplitEquiv (e : A ≃ₗ[K] B × C) (c m : ℕ) :
    (Fin (c + m) → A) ≃ₗ[K]
      ((Fin m → B) × ((Fin (c + m) → C) × (Fin c → B))) where
  toFun f := ((fun j => (e (f (Fin.natAdd c j))).1),
    (fun i => (e (f i)).2), fun i => (e (f (Fin.castAdd m i))).1)
  invFun z := fun i => e.symm (Fin.addCases z.2.2 z.1 i, z.2.1 i)
  left_inv f := by
    funext i
    apply e.injective
    simp only [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · exact Fin.addCases_castAdd_natAdd (fun j => (e (f j)).1) i
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp
  map_add' f g := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp
  map_smul' a f := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp

@[simp] theorem coordinateSplitEquiv_trace_apply (e : A ≃ₗ[K] B × C)
    (c m : ℕ) (f : Fin (c + m) → A) (i : Fin m) :
    (coordinateSplitEquiv e c m f).1 i = (e (f (Fin.natAdd c i))).1 := rfl

@[simp] theorem coordinateSplitEquiv_residual_apply (e : A ≃ₗ[K] B × C)
    (c m : ℕ) (f : Fin (c + m) → A) (i : Fin (c + m)) :
    (coordinateSplitEquiv e c m f).2.1 i = (e (f i)).2 := rfl

@[simp] theorem coordinateSplitEquiv_normal_apply (e : A ≃ₗ[K] B × C)
    (c m : ℕ) (f : Fin (c + m) → A) (i : Fin c) :
    (coordinateSplitEquiv e c m f).2.2 i = (e (f (Fin.castAdd m i))).1 := rfl

@[simp] theorem coordinateSplitEquiv_symm_apply (e : A ≃ₗ[K] B × C)
    (c m : ℕ) (z : (Fin m → B) × ((Fin (c + m) → C) × (Fin c → B)))
    (i : Fin (c + m)) :
    (coordinateSplitEquiv e c m).symm z i =
      e.symm (Fin.addCases z.2.2 z.1 i, z.2.1 i) := rfl

end Coordinates

section BlockMaps

variable {U Z : Type*} [AddCommGroup U] [Module K U]
  [AddCommGroup Z] [Module K Z]

/-- The dimension of a split vector space is the sum of its two factors. -/
theorem finrank_eq_add_of_linearEquiv [Module.Finite K W] [Module.Finite K U]
    (e : V ≃ₗ[K] W × U) :
    Module.finrank K V = Module.finrank K W + Module.finrank K U := by
  rw [e.finrank_eq, Module.finrank_prod]

/-- Injectivity of a block diagonal linear map is equivalent to injectivity
of its two blocks. -/
theorem linearMap_prodMap_injective_iff (f : V →ₗ[K] W) (g : U →ₗ[K] Z) :
    Function.Injective (f.prodMap g) ↔ Function.Injective f ∧ Function.Injective g := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      have heq : f.prodMap g (x, 0) = f.prodMap g (y, 0) := by simp [hxy]
      exact congrArg Prod.fst (h heq)
    · intro x y hxy
      have heq : f.prodMap g (0, x) = f.prodMap g (0, y) := by simp [hxy]
      exact congrArg Prod.snd (h heq)
  · rintro ⟨hf, hg⟩ x y hxy
    exact Prod.ext (hf (congrArg Prod.fst hxy)) (hg (congrArg Prod.snd hxy))

/-- Surjectivity of a block diagonal linear map is equivalent to
surjectivity of its two blocks. -/
theorem linearMap_prodMap_surjective_iff (f : V →ₗ[K] W) (g : U →ₗ[K] Z) :
    Function.Surjective (f.prodMap g) ↔ Function.Surjective f ∧ Function.Surjective g := by
  constructor
  · intro h
    constructor
    · intro y
      obtain ⟨x, hx⟩ := h (y, 0)
      exact ⟨x.1, congrArg Prod.fst hx⟩
    · intro y
      obtain ⟨x, hx⟩ := h (0, y)
      exact ⟨x.2, congrArg Prod.snd hx⟩
  · rintro ⟨hf, hg⟩ y
    obtain ⟨x₁, hx₁⟩ := hf y.1
    obtain ⟨x₂, hx₂⟩ := hg y.2
    exact ⟨(x₁, x₂), Prod.ext hx₁ hx₂⟩

end BlockMaps

end IdealGeneration
