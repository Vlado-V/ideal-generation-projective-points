module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Elimination of a surjective evaluation block

For a pair of linear maps `(f,g)` with `f` surjective, the cokernel is
canonically the second target modulo the values of `g` on `ker f`.
The construction uses the inclusion of the second target into the pair
target and does not choose a linear splitting.
-/

noncomputable section
namespace IdealGeneration.TwoNormalCokernelLinear

variable {K V A B : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

/-- The remaining scalar target maps into the cokernel of the pair map. -/
def scalarClassMap (f : V →ₗ[K] A) (g : V →ₗ[K] B) :
    B →ₗ[K] ((A × B) ⧸ (f.prod g).range) :=
  (f.prod g).range.mkQ.comp (LinearMap.inr K A B)

@[simp] theorem scalarClassMap_apply (f : V →ₗ[K] A) (g : V →ₗ[K] B) (b : B) :
    scalarClassMap f g b = Submodule.Quotient.mk (0, b) := rfl

/-- Scalar classes vanish exactly on the second-map values of the first kernel. -/
theorem scalarClassMap_ker (f : V →ₗ[K] A) (g : V →ₗ[K] B) :
    (scalarClassMap f g).ker = (g.comp f.ker.subtype).range := by
  ext b
  change (Submodule.Quotient.mk (0, b) : (A × B) ⧸ (f.prod g).range) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v, hv⟩
    have hf : f v = 0 := congrArg Prod.fst hv
    have hg : g v = b := congrArg Prod.snd hv
    exact ⟨⟨v, hf⟩, hg⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.val, Prod.ext v.property hv⟩

/-- Surjectivity of the first map makes every cokernel class a scalar class. -/
theorem scalarClassMap_surjective (f : V →ₗ[K] A) (g : V →ₗ[K] B)
    (hf : Function.Surjective f) : Function.Surjective (scalarClassMap f g) := by
  intro c
  obtain ⟨⟨a, b⟩, rfl⟩ := (f.prod g).range.mkQ_surjective c
  obtain ⟨v, hv⟩ := hf a
  refine ⟨b - g v, ?_⟩
  change (Submodule.Quotient.mk (0, b - g v) : (A × B) ⧸ (f.prod g).range) =
    Submodule.Quotient.mk (a, b)
  symm
  apply (Submodule.Quotient.eq (f.prod g).range).mpr
  refine ⟨v, ?_⟩
  apply Prod.ext
  · simpa using hv
  · simp

/-- The cokernel after a surjective first block is the scalar quotient by
the second block restricted to its kernel. -/
def cokernelEquiv (f : V →ₗ[K] A) (g : V →ₗ[K] B)
    (hf : Function.Surjective f) :
    ((A × B) ⧸ (f.prod g).range) ≃ₗ[K] B ⧸ (g.comp f.ker.subtype).range :=
  ((scalarClassMap f g).quotKerEquivOfSurjective
    (scalarClassMap_surjective f g hf)).symm.trans
      (Submodule.quotEquivOfEq _ _ (scalarClassMap_ker f g))

/-- The quotient equivalence retains the class of a pure scalar representative. -/
@[simp] theorem cokernelEquiv_scalarClass (f : V →ₗ[K] A) (g : V →ₗ[K] B)
    (hf : Function.Surjective f) (b : B) :
    cokernelEquiv f g hf (Submodule.Quotient.mk (0, b)) =
      Submodule.Quotient.mk b := by
  let e := (scalarClassMap f g).quotKerEquivOfSurjective
    (scalarClassMap_surjective f g hf)
  change Submodule.quotEquivOfEq _ _ (scalarClassMap_ker f g)
    (e.symm (e (Submodule.Quotient.mk b))) = Submodule.Quotient.mk b
  rw [e.symm_apply_apply]
  rfl

/-- The cokernel dimension is the dimension left in the scalar quotient. -/
theorem cokernel_finrank [FiniteDimensional K B]
    (f : V →ₗ[K] A) (g : V →ₗ[K] B) (hf : Function.Surjective f) :
    Module.finrank K ((A × B) ⧸ (f.prod g).range) =
      Module.finrank K B - Module.finrank K (g.comp f.ker.subtype).range := by
  rw [(cokernelEquiv f g hf).finrank_eq]
  have h := (g.comp f.ker.subtype).range.finrank_quotient_add_finrank
  omega

section AddCommMonoid

variable {K V A B : Type*} [Field K]
  [AddCommMonoid V] [Module K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

/-- The same equivalence retains the source's declared additive-monoid
instance, as needed for homogeneous subspaces and their linear maps. -/
def cokernelEquiv_monoid (f : V →ₗ[K] A) (g : V →ₗ[K] B)
    (hf : Function.Surjective f) :
    ((A × B) ⧸ (f.prod g).range) ≃ₗ[K] B ⧸ (g.comp f.ker.subtype).range := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  exact cokernelEquiv f g hf

end AddCommMonoid

end IdealGeneration.TwoNormalCokernelLinear
