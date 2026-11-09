module

public import IdealGeneration.Multiplication
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimension of the three-normal residual constraint

A surjection onto the six ternary quadrics induces a surjection from three
copies of its source onto the ten ternary cubics. Rank-nullity gives the
dimension of the kernel used in the three-normal elimination.
-/

noncomputable section
namespace IdealGeneration
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Apply the quadratic restriction to each of three coefficients, then
multiply by the corresponding normal coordinate. -/
def tripleNormalConstraint (q : V →ₗ[K] Forms K 3 2) :
    (Fin 3 → V) →ₗ[K] Forms K 3 3 :=
  (formMultiplication K 3 2).comp
    (LinearMap.pi (fun i => q.comp (LinearMap.proj i)))

@[simp] theorem tripleNormalConstraint_apply (q : V →ₗ[K] Forms K 3 2)
    (v : Fin 3 → V) :
    tripleNormalConstraint q v = formMultiplication K 3 2 (fun i => q (v i)) := rfl

/-- The coefficient tuples satisfying the cubic compatibility constraint. -/
def tripleNormalOmega (q : V →ₗ[K] Forms K 3 2) : Submodule K (Fin 3 → V) :=
  LinearMap.ker (tripleNormalConstraint q)

@[simp] theorem mem_tripleNormalOmega (q : V →ₗ[K] Forms K 3 2)
    (v : Fin 3 → V) :
    v ∈ tripleNormalOmega q ↔ formMultiplication K 3 2 (fun i => q (v i)) = 0 := Iff.rfl

/-- Onto quadratic restriction makes the cubic constraint onto. -/
theorem tripleNormalConstraint_surjective [CharZero K]
    (q : V →ₗ[K] Forms K 3 2) (hq : Function.Surjective q) :
    Function.Surjective (tripleNormalConstraint q) := by
  intro f
  obtain ⟨g, hg⟩ := formMultiplication_surjective (K := K) 3 2 f
  choose v hv using fun i => hq (g i)
  refine ⟨v, ?_⟩
  rw [tripleNormalConstraint_apply]
  have heq : (fun i => q (v i)) = g := funext hv
  rw [heq]
  exact hg

/-- If the kernel of quadratic restriction has dimension `h`, the space of
compatible triples has dimension `3h + 8`. -/
theorem finrank_tripleNormalOmega [CharZero K] [Module.Finite K V]
    (q : V →ₗ[K] Forms K 3 2) (hq : Function.Surjective q)
    (h : ℕ) (hker : finrank K q.ker = h) :
    finrank K (tripleNormalOmega q) = 3 * h + 8 := by
  have hquadrics : finrank K (Forms K 3 2) = 6 := by
    rw [finrank_forms]
    decide
  have hcubics : finrank K (Forms K 3 3) = 10 := by
    rw [finrank_forms]
    decide
  have hsource := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, hquadrics, hker] at hsource
  have hconstraint := (tripleNormalConstraint q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tripleNormalConstraint_surjective q hq),
    finrank_top, hcubics] at hconstraint
  have htriples : finrank K (Fin 3 → V) = 3 * finrank K V := by
    simp [Module.finrank_pi_fintype]
  rw [htriples] at hconstraint
  change finrank K (LinearMap.ker (tripleNormalConstraint q)) = 3 * h + 8
  omega

end IdealGeneration
