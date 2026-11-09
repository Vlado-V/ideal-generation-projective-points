module

public import IdealGeneration.ScalarTransversality
public import IdealGeneration.HyperplaneAlgebra

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Transfer scalar transversality to homogeneous subspaces of the polynomial ring. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n d p : ℕ}

/-- Regard a homogeneous polynomial subspace as a subspace of the space of forms. -/
def homogeneousCore (U : Submodule K (Poly K (n + 1))) :
    Submodule K (Forms K (n + 1) d) := U.comap (Forms K (n + 1) d).subtype

/-- Passing to the homogeneous ambient space preserves the actual vectors. -/
def homogeneousCoreEquiv (U : Submodule K (Poly K (n + 1)))
    (hU : U ≤ Forms K (n + 1) d) : homogeneousCore (d := d) U ≃ₗ[K] U where
  toFun f := ⟨f.val.val, f.property⟩
  invFun f := ⟨⟨f.val, hU f.property⟩, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_homogeneousCore (U : Submodule K (Poly K (n + 1)))
    (hU : U ≤ Forms K (n + 1) d) :
    finrank K (homogeneousCore (d := d) U) = finrank K U :=
  (homogeneousCoreEquiv U hU).finrank_eq

/-- Disjointness in the space of forms is the desired polynomial disjointness. -/
theorem polynomial_disjoint_of_core_disjoint
    (U : Submodule K (Poly K (n + 1))) (hU : U ≤ Forms K (n + 1) d)
    (a : PointCoordinates K n p)
    (h : Disjoint (homogeneousCore (d := d) U) (pointDegreePiece K a d)) :
    Disjoint U (pointPolynomialPiece a d) := by
  rw [Submodule.disjoint_def] at h ⊢
  intro f hfU hfI
  have hfForms : f ∈ Forms K (n + 1) d := hU hfU
  have hfCore : (⟨f, hfForms⟩ : Forms K (n + 1) d) ∈ homogeneousCore U := hfU
  have hfPiece : (⟨f, hfForms⟩ : Forms K (n + 1) d) ∈ pointDegreePiece K a d := by
    apply (mem_pointDegreePiece a _).mpr
    exact ((mem_pointPolynomialPiece_iff a f).mp hfI).2
  have he := h _ hfCore hfPiece
  exact congrArg Subtype.val he

/-- Spanning in the space of forms is the desired polynomial equality. -/
theorem polynomial_sup_of_core_sup
    (U : Submodule K (Poly K (n + 1))) (hU : U ≤ Forms K (n + 1) d)
    (a : PointCoordinates K n p)
    (h : homogeneousCore (d := d) U ⊔ pointDegreePiece K a d = ⊤) :
    U ⊔ pointPolynomialPiece a d = Forms K (n + 1) d := by
  apply le_antisymm
  · apply sup_le hU
    intro f hf
    exact ((mem_pointPolynomialPiece_iff a f).mp hf).1
  · intro f hf
    have hm : (⟨f, hf⟩ : Forms K (n + 1) d) ∈
        homogeneousCore (d := d) U ⊔ pointDegreePiece K a d := by rw [h]; trivial
    obtain ⟨u, hu, v, hv, he⟩ := Submodule.mem_sup.mp hm
    apply Submodule.mem_sup.mpr
    exact ⟨u.val, hu, v.val, ⟨v, hv, rfl⟩, congrArg Subtype.val he⟩

/-- The scalar disjointness condition in the polynomial model holds generically. -/
theorem generic_polynomial_disjoint [Infinite K]
    (U : Submodule K (Poly K (n + 1))) (hU : U ≤ Forms K (n + 1) d)
    (p : ℕ) (hp : finrank K U ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Disjoint U (pointPolynomialPiece a d) := by
  obtain ⟨D, hD, hgood⟩ := generic_disjoint_pointDegreePiece
    (homogeneousCore (d := d) U) (by simpa only [finrank_homogeneousCore U hU] using hp)
  exact ⟨D, hD, fun a ha => polynomial_disjoint_of_core_disjoint U hU a (hgood a ha)⟩

/-- The scalar spanning condition in the polynomial model holds generically. -/
theorem generic_polynomial_sup [Infinite K]
    (U : Submodule K (Poly K (n + 1))) (hU : U ≤ Forms K (n + 1) d)
    (p : ℕ) (hp : p ≤ finrank K U) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → U ⊔ pointPolynomialPiece a d = Forms K (n + 1) d := by
  obtain ⟨D, hD, hgood⟩ := generic_sup_pointDegreePiece
    (homogeneousCore (d := d) U) (by simpa only [finrank_homogeneousCore U hU] using hp)
  exact ⟨D, hD, fun a ha => polynomial_sup_of_core_sup U hU a (hgood a ha)⟩

end IdealGeneration
