module

public import IdealGeneration.QuadraticElimination
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Projecting the eliminated quadratic image

Projection along the mixed subspace identifies the intersection of the
mixed subspace plus an image with the target summand as the projected
image. Applied to the normal-cubic kernel, this gives the `2h+2` bound
for the space denoted by `W'` in Appendix A.2.
-/

noncomputable section
namespace IdealGeneration.QuadraticProjection

variable {K M E : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup E] [Module K E]

/-- Projection along `U` onto `W` converts the intersection with `W`
into the projected image, for every linear map `φ`. -/
theorem projection_range_intersection
    (U W : Submodule K M) (π : M →ₗ[K] M) (φ : E →ₗ[K] M)
    (hU : ∀ u ∈ U, π u = 0)
    (hW : ∀ w ∈ W, π w = w)
    (hπW : ∀ m, π m ∈ W)
    (hsub : ∀ m, m - π m ∈ U) :
    (U ⊔ φ.range) ⊓ W = (π.comp φ).range := by
  ext x
  constructor
  · rintro ⟨hx, hxW⟩
    obtain ⟨u, hu, v, hv, hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨e, rfl⟩ := hv
    refine ⟨e, ?_⟩
    change π (φ e) = x
    calc
      π (φ e) = π (u + φ e) := by rw [map_add, hU u hu, zero_add]
      _ = π x := congrArg π hsum
      _ = x := hW x hxW
  · rintro ⟨e, rfl⟩
    refine ⟨?_, hπW (φ e)⟩
    apply Submodule.mem_sup.mpr
    refine ⟨-(φ e - π (φ e)), U.neg_mem (hsub (φ e)),
      φ e, ⟨e, rfl⟩, ?_⟩
    change -(φ e - π (φ e)) + φ e = π (φ e)
    abel

/-- The projected intersection has dimension at most that of the source. -/
theorem finrank_projection_range_intersection_le [FiniteDimensional K E]
    (U W : Submodule K M) (π : M →ₗ[K] M) (φ : E →ₗ[K] M)
    (hU : ∀ u ∈ U, π u = 0)
    (hW : ∀ w ∈ W, π w = w)
    (hπW : ∀ m, π m ∈ W)
    (hsub : ∀ m, m - π m ∈ U) :
    Module.finrank K ↥((U ⊔ φ.range) ⊓ W) ≤ Module.finrank K E := by
  rw [projection_range_intersection U W π φ hU hW hπW hsub]
  exact LinearMap.finrank_range_le (π.comp φ)

section ExplicitPhi

variable {H R : Type*} [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] [CommRing R] [Algebra K R]

/-- Applying the projection identity to the actual eliminated map gives
the claimed upper bound for `W'`. -/
theorem finrank_projected_phi_intersection_le
    (U W : Submodule K (R × R)) (π : (R × R) →ₗ[K] (R × R))
    (N₁ N₂ : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (hU : ∀ u ∈ U, π u = 0)
    (hW : ∀ w ∈ W, π w = w)
    (hπW : ∀ m, π m ∈ W)
    (hsub : ∀ m, m - π m ∈ U) :
    Module.finrank K ↥((U ⊔ (QuadraticElimination.phi N₁ N₂ g₁ g₂).range) ⊓ W) ≤
      2 * Module.finrank K H + 2 := by
  rw [projection_range_intersection U W π (QuadraticElimination.phi N₁ N₂ g₁ g₂)
    hU hW hπW hsub]
  exact QuadraticElimination.finrank_projected_phi_range_le N₁ N₂ g₁ g₂ π

end ExplicitPhi
end IdealGeneration.QuadraticProjection
