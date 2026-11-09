module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Selected first-response directions

The linear-algebra step of Lemma 4.4 in
*Ideal generation for general reduced projective points*.

Independent source functionals and independent target vectors determine a sum
of rank-one maps whose rank is the number of selected directions. The selection
of directions from the two spanning families is a separate combinatorial step.
-/

namespace IdealGeneration

open Module

variable {𝕜 V W ι : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] [Fintype ι]

/-- Evaluation against a finite linearly independent family of functionals is onto. -/
theorem independent_functionals_surjective
    (α : ι → Module.Dual 𝕜 V) (hα : LinearIndependent 𝕜 α) :
    Function.Surjective (LinearMap.pi α) := by
  have hfun : LinearIndependent 𝕜 (fun i x => α i x) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    apply (Fintype.linearIndependent_iff.mp hα) c ?_ i
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, LinearMap.zero_apply] using congrFun hc x
  have hspan : Submodule.span 𝕜 (Set.range (fun x i => α i x)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hfun
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- The sum of the rank-one maps `x ↦ α i x • v i`. -/
noncomputable def firstResponse
    (α : ι → Module.Dual 𝕜 V) (v : ι → W) : V →ₗ[𝕜] W :=
  (Fintype.linearCombination 𝕜 v).comp (LinearMap.pi α)

@[simp] theorem firstResponse_apply
    (α : ι → Module.Dual 𝕜 V) (v : ι → W) (x : V) :
    firstResponse α v x = ∑ i, α i x • v i := by
  simp [firstResponse, Fintype.linearCombination_apply]

/-- The image of the response equals the span of the selected target vectors. -/
theorem firstResponse_range
    (α : ι → Module.Dual 𝕜 V) (v : ι → W)
    (hα : LinearIndependent 𝕜 α) :
    LinearMap.range (firstResponse α v) = Submodule.span 𝕜 (Set.range v) := by
  unfold firstResponse
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (independent_functionals_surjective α hα))]
  exact Fintype.range_linearCombination 𝕜 v

/-- Independent source functionals and target vectors give exactly one rank per
selected direction, as used in the response construction of Lemma 4.4. -/
theorem firstResponse_finrank
    (α : ι → Module.Dual 𝕜 V) (v : ι → W)
    (hα : LinearIndependent 𝕜 α) (hv : LinearIndependent 𝕜 v) :
    Module.finrank 𝕜 (LinearMap.range (firstResponse α v)) = Fintype.card ι := by
  unfold firstResponse
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (independent_functionals_surjective α hα))]
  rw [LinearMap.finrank_range_of_inj hv.fintypeLinearCombination_injective]
  exact Module.finrank_pi 𝕜

/-- The selected directions in two independent target summands give additive ranks.
This is the two-target version used for the normal motions in Lemma 4.4. -/
theorem firstResponse_two_summands_finrank
    {κ A B : Type*} [Fintype κ]
    [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B] [Module 𝕜 B]
    (α : ι ⊕ κ → Module.Dual 𝕜 V) (a : ι → A) (b : κ → B)
    (hα : LinearIndependent 𝕜 α)
    (ha : LinearIndependent 𝕜 a) (hb : LinearIndependent 𝕜 b) :
    Module.finrank 𝕜 (LinearMap.range (firstResponse α
      (Sum.elim (LinearMap.inl 𝕜 A B ∘ a) (LinearMap.inr 𝕜 A B ∘ b)))) =
        Fintype.card ι + Fintype.card κ := by
  simpa only [Fintype.card_sum] using firstResponse_finrank α
    (Sum.elim (LinearMap.inl 𝕜 A B ∘ a) (LinearMap.inr 𝕜 A B ∘ b))
    hα (linearIndependent_inl_union_inr' ha hb)

end IdealGeneration
