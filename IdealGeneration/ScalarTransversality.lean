module

public import IdealGeneration.SubspaceInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Scalar interpolation gives the disjointness and spanning conditions in hyperplane specialization. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n d p : ℕ}

/-- Injective scalar evaluation makes the fixed space disjoint from the point ideal. -/
theorem disjoint_pointDegreePiece_of_subspaceEvaluation_injective
    (U : Submodule K (Forms K (n + 1) d)) (a : PointCoordinates K n p)
    (h : Function.Injective (subspaceEvaluation U a)) :
    Disjoint U (pointDegreePiece K a d) := by
  rw [Submodule.disjoint_def]
  intro f hfU hfI
  have he : subspaceEvaluation U a ⟨f, hfU⟩ = subspaceEvaluation U a 0 := by
    change pointEvaluation K a d f = 0
    exact hfI
  exact congrArg (fun u : U => u.val) (h he)

/-- Surjective scalar evaluation makes the fixed space and the point ideal span all forms. -/
theorem sup_pointDegreePiece_of_subspaceEvaluation_surjective
    (U : Submodule K (Forms K (n + 1) d)) (a : PointCoordinates K n p)
    (h : Function.Surjective (subspaceEvaluation U a)) :
    U ⊔ pointDegreePiece K a d = ⊤ := by
  apply le_antisymm le_top
  intro f _
  obtain ⟨g, hg⟩ := h (pointEvaluation K a d f)
  have hdiff : f - g.val ∈ pointDegreePiece K a d := by
    apply (mem_pointDegreePiece a _).mpr
    intro i
    have he := congrFun hg i
    change eval (chartPoint K a i) (f.val - g.val.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he.symm
  apply Submodule.mem_sup.mpr
  exact ⟨g.val, g.property, f - g.val, hdiff, by abel⟩

/-- The disjointness half of the scalar transversality condition. -/
theorem generic_disjoint_pointDegreePiece [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (hp : finrank K U ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Disjoint U (pointDegreePiece K a d) := by
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation_injective U p hp
  exact ⟨D, hD, fun a ha => disjoint_pointDegreePiece_of_subspaceEvaluation_injective
    U a (hgood a ha)⟩

/-- The spanning half of the scalar transversality condition. -/
theorem generic_sup_pointDegreePiece [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (hp : p ≤ finrank K U) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → U ⊔ pointDegreePiece K a d = ⊤ := by
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation_surjective U p hp
  exact ⟨D, hD, fun a ha => sup_pointDegreePiece_of_subspaceEvaluation_surjective
    U a (hgood a ha)⟩

end IdealGeneration
