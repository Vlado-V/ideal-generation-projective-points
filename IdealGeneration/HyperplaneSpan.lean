module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Lifting a spanning statement from a hyperplane

A sum of subspaces covers an ambient subspace when it covers the image under
restriction and one summand contains the kernel of restriction there.
-/

namespace IdealGeneration

variable {K S R : Type*} [Field K]
  [AddCommGroup S] [Module K S] [AddCommGroup R] [Module K R]

/-- Lift image spanning when the restriction kernel is already in the first summand. -/
theorem submodule_le_sup_of_restriction
    (ρ : S →ₗ[K] R) (A P G : Submodule K S)
    (hPA : P ≤ A) (hGA : G ≤ A)
    (hker : A ⊓ ρ.ker ≤ P)
    (himage : A.map ρ ≤ P.map ρ ⊔ G.map ρ) : A ≤ P ⊔ G := by
  intro a ha
  have hρa : ρ a ∈ P.map ρ ⊔ G.map ρ := himage ⟨a, ha, rfl⟩
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hρa
  obtain ⟨p, hp, hpρ⟩ := hu
  obtain ⟨g, hg, hgρ⟩ := hv
  have hrem : a - (p + g) ∈ P := by
    apply hker
    constructor
    · exact A.sub_mem ha (A.add_mem (hPA hp) (hGA hg))
    · change ρ (a - (p + g)) = 0
      rw [map_sub, map_add, hpρ, hgρ, huv, sub_self]
  have hrem' : a - (p + g) ∈ P ⊔ G := (show P ≤ P ⊔ G from le_sup_left) hrem
  have hpg : p + g ∈ P ⊔ G := (P ⊔ G).add_mem ((show P ≤ P ⊔ G from le_sup_left) hp) ((show G ≤ P ⊔ G from le_sup_right) hg)
  simpa only [sub_add_cancel] using (P ⊔ G).add_mem hrem' hpg

/-- The corresponding exact equality of the ambient subspace and the two summands. -/
theorem submodule_eq_sup_of_restriction
    (ρ : S →ₗ[K] R) (A P G : Submodule K S)
    (hPA : P ≤ A) (hGA : G ≤ A)
    (hker : A ⊓ ρ.ker ≤ P)
    (himage : A.map ρ ≤ P.map ρ ⊔ G.map ρ) : A = P ⊔ G := by
  exact le_antisymm (submodule_le_sup_of_restriction ρ A P G hPA hGA hker himage)
    (sup_le hPA hGA)

/-- Restricting the range of a section gives exactly the subspace being lifted. -/
theorem map_range_eq_of_section (ρ : S →ₗ[K] R) (T : Submodule K R)
    (L : T →ₗ[K] S) (hL : ∀ t : T, ρ (L t) = t.val) : L.range.map ρ = T := by
  apply le_antisymm
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    rw [hL]
    exact t.property
  · intro y hy
    refine ⟨L ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    exact hL ⟨y, hy⟩

/-- The spanning criterion expressed using a linear lift of the trace subspace. -/
theorem submodule_le_product_sup_section
    (ρ : S →ₗ[K] R) (A P : Submodule K S) (T : Submodule K R)
    (L : T →ₗ[K] S) (hL : ∀ t : T, ρ (L t) = t.val)
    (hPA : P ≤ A) (hLA : L.range ≤ A)
    (hker : A ⊓ ρ.ker ≤ P)
    (himage : A.map ρ ≤ P.map ρ ⊔ T) : A ≤ P ⊔ L.range := by
  apply submodule_le_sup_of_restriction ρ A P L.range hPA hLA hker
  rwa [map_range_eq_of_section ρ T L hL]

end IdealGeneration
