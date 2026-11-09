module

public import IdealGeneration.HyperplanePolynomial
public import IdealGeneration.Multiplication

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The scalar trace exact sequence for Euler relations

This file proves sequence (3.2). The normal coordinate is `0`; the trace
coordinates are its successors. The source consists of `n` ambient forms
of degree `d`, and its scalar trace has degree `d+1` on the hyperplane.
-/

noncomputable section
namespace IdealGeneration.HyperplaneEulerScalar
open MvPolynomial

variable (K : Type*) [Field K] (n d : ℕ)

/-- Restrict each component to the hyperplane and multiply by its trace coordinate. -/
def scalarTrace :
    (Fin n → Forms K (n + 1) d) →ₗ[K] Forms K n (d + 1) :=
  (formMultiplication K n d).comp
    (LinearMap.pi (fun i => (restrictForm K n d).comp (LinearMap.proj i)))

/-- The ambient sum using only tangential coordinates. -/
def tangentForm :
    (Fin n → Forms K (n + 1) d) →ₗ[K] Forms K (n + 1) (d + 1) where
  toFun g := ⟨∑ i, X i.succ * (g i).val, by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_comm] using
      (isHomogeneous_X (R := K) i.succ).mul (g i).property⟩
  map_add' g h := by
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    apply Subtype.ext
    simp [Finset.smul_sum]

@[simp] theorem tangentForm_val (g : Fin n → Forms K (n + 1) d) :
    (tangentForm K n d g).val = ∑ i, X i.succ * (g i).val := rfl

@[simp] theorem scalarTrace_val (g : Fin n → Forms K (n + 1) d) :
    (scalarTrace K n d g).val = ∑ i, X i * hyperplaneRestrict K n (g i).val := rfl

/-- The scalar trace is the restriction of the ambient tangential sum. -/
theorem restrict_tangentForm (g : Fin n → Forms K (n + 1) d) :
    restrictForm K n (d + 1) (tangentForm K n d g) = scalarTrace K n d g := by
  apply Subtype.ext
  simp

/-- Drop the normal component of an ambient Euler relation. -/
def forgetNormal :
    (formMultiplication K (n + 1) d).ker →ₗ[K] (Fin n → Forms K (n + 1) d) :=
  LinearMap.pi (fun i => (LinearMap.proj i.succ).comp
    (formMultiplication K (n + 1) d).ker.subtype)

@[simp] theorem forgetNormal_apply (f : (formMultiplication K (n + 1) d).ker)
    (i : Fin n) : forgetNormal K n d f i = f.val i.succ := rfl

/-- The scalar trace of an ambient Euler relation vanishes. -/
theorem scalarTrace_forgetNormal (f : (formMultiplication K (n + 1) d).ker) :
    scalarTrace K n d (forgetNormal K n d f) = 0 := by
  apply Subtype.ext
  have h := congrArg (hyperplaneRestrict K n)
    (congrArg Subtype.val f.property)
  change hyperplaneRestrict K n (∑ j, X j * (f.val j).val) = hyperplaneRestrict K n 0 at h
  rw [Fin.sum_univ_succ] at h
  simp only [map_add, map_mul, map_sum, map_zero, hyperplaneRestrict_X_zero,
    zero_mul, zero_add, hyperplaneRestrict_X_succ] at h
  exact h

/-- The omitted normal component is determined by the tangential components. -/
theorem forgetNormal_injective : Function.Injective (forgetNormal K n d) := by
  intro f g hfg
  have hsucc (i : Fin n) : f.val i.succ = g.val i.succ := congrFun hfg i
  have hf := congrArg Subtype.val f.property
  have hg := congrArg Subtype.val g.property
  simp only [formMultiplication_val, Fin.sum_univ_succ, Submodule.coe_zero] at hf hg
  have hsum : (∑ i : Fin n, X i.succ * (f.val i.succ).val) =
      ∑ i : Fin n, X i.succ * (g.val i.succ).val := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hsucc i]
  rw [hsum] at hf
  have hnormal : (f.val 0).val = (g.val 0).val :=
    mul_left_cancel₀ (X_ne_zero (0 : Fin (n + 1))) (add_right_cancel (hf.trans hg.symm))
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => hsucc j) i
  exact Subtype.ext hnormal

/-- Every tuple with zero scalar trace extends to an ambient Euler relation. -/
theorem mem_range_forgetNormal_of_scalarTrace_eq_zero
    (g : Fin n → Forms K (n + 1) d) (hg : scalarTrace K n d g = 0) :
    g ∈ (forgetNormal K n d).range := by
  have ht : restrictForm K n (d + 1) (tangentForm K n d g) = 0 := by
    rw [restrict_tangentForm, hg]
  obtain ⟨q, hq⟩ := (restrictForm_eq_zero_iff K n (tangentForm K n d g)).mp ht
  refine ⟨⟨Fin.cons (-q) g, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp only [formMultiplication_val, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Submodule.coe_neg, Submodule.coe_zero]
    change X 0 * -q.val + (tangentForm K n d g).val = 0
    rw [mul_neg, ← hq]
    exact neg_add_cancel _
  · funext i
    simp

/-- Exactness in the middle of sequence (3.2). -/
theorem scalarTrace_ker_eq_range :
    (scalarTrace K n d).ker = (forgetNormal K n d).range := by
  ext g
  constructor
  · exact mem_range_forgetNormal_of_scalarTrace_eq_zero K n d g
  · rintro ⟨f, rfl⟩
    exact scalarTrace_forgetNormal K n d f

/-- Forgetting the normal component as a map into the scalar-trace kernel. -/
def forgetNormalToKernel :
    (formMultiplication K (n + 1) d).ker →ₗ[K] (scalarTrace K n d).ker where
  toFun f := ⟨forgetNormal K n d f, scalarTrace_forgetNormal K n d f⟩
  map_add' f g := Subtype.ext ((forgetNormal K n d).map_add f g)
  map_smul' c f := Subtype.ext ((forgetNormal K n d).map_smul c f)

/-- The kernel in sequence (3.2) is naturally the ambient Euler relation space. -/
def forgetNormalKernelEquiv :
    (formMultiplication K (n + 1) d).ker ≃ₗ[K] (scalarTrace K n d).ker :=
  LinearEquiv.ofBijective (forgetNormalToKernel K n d) (by
    constructor
    · intro f g h
      apply forgetNormal_injective K n d
      exact congrArg Subtype.val h
    · intro g
      obtain ⟨f, hf⟩ := mem_range_forgetNormal_of_scalarTrace_eq_zero K n d g.val g.property
      exact ⟨f, Subtype.ext hf⟩)

/-- The scalar trace map is onto in characteristic zero. -/
theorem scalarTrace_surjective [CharZero K] :
    Function.Surjective (scalarTrace K n d) := by
  intro f
  obtain ⟨g, hg⟩ := formMultiplication_surjective (K := K) n d f
  refine ⟨fun i => extendForm K n d (g i), ?_⟩
  change formMultiplication K n d
    (fun i => restrictForm K n d (extendForm K n d (g i))) = f
  simpa only [restrictForm_extendForm] using hg

end IdealGeneration.HyperplaneEulerScalar
