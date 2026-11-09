module

public import IdealGeneration.HyperplanePolynomial
public import IdealGeneration.Multiplication

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The hyperplane exact sequence for Euler relations

The normal coordinate is `0` and the trace coordinates are its successors.
This file constructs the maps of (3.1) with genuine homogeneous polynomials.
-/

noncomputable section
namespace IdealGeneration.HyperplaneEuler
open MvPolynomial
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (n : ℕ)

/-- Polynomial Euler relations in `n` variables and degree `d`. -/
abbrev Relations (d : ℕ) := (formMultiplication K n d).ker

/-- The tangential dot product, before restriction to the hyperplane. -/
def tangentProduct (d : ℕ) :
    (Fin n → Forms K (n + 1) d) →ₗ[K] Forms K (n + 1) (d + 1) where
  toFun g := ⟨∑ i, X i.succ * (g i).val, by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) i.succ).mul (g i).property⟩
  map_add' g h := by
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    apply Subtype.ext
    simp [Finset.smul_sum]

@[simp] theorem tangentProduct_val {d : ℕ} (g : Fin n → Forms K (n + 1) d) :
    (tangentProduct K n d g).val = ∑ i, X i.succ * (g i).val := rfl

/-- The tuple `(-Σ xᵢgᵢ, x₀g₁, ..., x₀gₙ)`. -/
def normalTuple (d : ℕ) :
    (Fin n → Forms K (n + 1) d) →ₗ[K]
      (Fin (n + 1) → Forms K (n + 1) (d + 1)) where
  toFun g := Fin.cons (-(tangentProduct K n d g)) (fun i => normalFormMul K n d (g i))
  map_add' g h := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [add_comm]
    · simp
  map_smul' c g := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp

/-- The normal tuple satisfies the Euler equation identically. -/
theorem normalTuple_relation (d : ℕ) (g : Fin n → Forms K (n + 1) d) :
    formMultiplication K (n + 1) (d + 1) (normalTuple K n d g) = 0 := by
  apply Subtype.ext
  change (∑ j, X j * (normalTuple K n d g j).val) = 0
  rw [Fin.sum_univ_succ]
  change X 0 * (-(∑ i, X i.succ * (g i).val)) +
    (∑ i, X i.succ * (X 0 * (g i).val)) = 0
  have hs : (∑ i, X i.succ * (X 0 * (g i).val)) =
      X 0 * (∑ i, X i.succ * (g i).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The left map of the hyperplane Euler exact sequence. -/
def normalInjection (d : ℕ) :
    (Fin n → Forms K (n + 1) d) →ₗ[K] Relations K (n + 1) (d + 1) :=
  (normalTuple K n d).codRestrict _ (normalTuple_relation K n d)

@[simp] theorem normalInjection_zero {d : ℕ} (g : Fin n → Forms K (n + 1) d) :
    (normalInjection K n d g).val 0 = -(tangentProduct K n d g) := rfl

@[simp] theorem normalInjection_succ {d : ℕ} (g : Fin n → Forms K (n + 1) d)
    (i : Fin n) :
    (normalInjection K n d g).val i.succ = normalFormMul K n d (g i) := rfl

/-- Restrict all tangential components of an Euler relation to the hyperplane. -/
def trace (d : ℕ) : Relations K (n + 1) d →ₗ[K] Relations K n d where
  toFun f := ⟨fun i => restrictForm K n d (f.val i.succ), by
    apply Subtype.ext
    have hf : (∑ j, X j * (f.val j).val) = 0 := congrArg Subtype.val f.property
    have hr := congrArg (hyperplaneRestrict K n) hf
    change (∑ i, X i * hyperplaneRestrict K n (f.val i.succ).val) = 0
    simpa only [map_add, map_sum, map_mul, Fin.sum_univ_succ, hyperplaneRestrict_X_zero,
      zero_mul, hyperplaneRestrict_X_succ, zero_add, map_zero] using hr⟩
  map_add' f g := by
    apply Subtype.ext
    funext i
    exact (restrictForm K n d).map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    funext i
    exact (restrictForm K n d).map_smul c _

@[simp] theorem trace_apply {d : ℕ} (f : Relations K (n + 1) d) (i : Fin n) :
    (trace K n d f).val i = restrictForm K n d (f.val i.succ) := rfl

/-- Extend a trace relation with zero normal component. -/
def extend (d : ℕ) : Relations K n d →ₗ[K] Relations K (n + 1) d where
  toFun f := ⟨Fin.cons 0 (fun i => extendForm K n d (f.val i)), by
    apply Subtype.ext
    have hf : (∑ i, X i * (f.val i).val) = 0 := congrArg Subtype.val f.property
    have he := congrArg (hyperplaneExtend K n) hf
    simpa only [formMultiplication_val, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Submodule.coe_zero, mul_zero, zero_add, map_sum, map_mul,
      hyperplaneExtend_X, extendForm_val, map_zero] using he⟩
  map_add' f g := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · exact (extendForm K n d).map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · exact (extendForm K n d).map_smul c _

@[simp] theorem trace_extend (d : ℕ) (f : Relations K n d) :
    trace K n d (extend K n d f) = f := by
  apply Subtype.ext
  funext i
  exact restrictForm_extendForm K n (f.val i)

/-- The trace map in (3.1) is split surjective. -/
theorem trace_surjective (d : ℕ) : Function.Surjective (trace K n d) :=
  fun f => ⟨extend K n d f, trace_extend K n d f⟩

/-- The normal map in (3.1) is injective. -/
theorem normalInjection_injective (d : ℕ) : Function.Injective (normalInjection K n d) := by
  intro g h hgh
  funext i
  apply normalFormMul_injective K n d
  exact congrArg (fun f : Relations K (n + 1) (d + 1) => f.val i.succ) hgh

@[simp] theorem trace_normalInjection (d : ℕ) (g : Fin n → Forms K (n + 1) d) :
    trace K n (d + 1) (normalInjection K n d g) = 0 := by
  apply Subtype.ext
  funext i
  exact restrictForm_normalFormMul K n (g i)

/-- Every Euler relation with zero trace comes from its unique normal tuple. -/
theorem exists_normal_of_trace_eq_zero (d : ℕ) (f : Relations K (n + 1) (d + 1))
    (hf : trace K n (d + 1) f = 0) :
    ∃ g : Fin n → Forms K (n + 1) d, normalInjection K n d g = f := by
  have hfi (i : Fin n) : restrictForm K n (d + 1) (f.val i.succ) = 0 :=
    congrArg (fun t : Relations K n (d + 1) => t.val i) hf
  have hgi (i : Fin n) : ∃ g : Forms K (n + 1) d,
      (f.val i.succ).val = X 0 * g.val :=
    (restrictForm_eq_zero_iff K n (f.val i.succ)).mp (hfi i)
  choose g hg using hgi
  have hrel : X 0 * (f.val 0).val +
      (∑ i : Fin n, X i.succ * (f.val i.succ).val) = 0 := by
    have hh := congrArg Subtype.val f.property
    simpa only [formMultiplication_val, Fin.sum_univ_succ, Submodule.coe_zero] using hh
  simp_rw [hg] at hrel
  have hprod : X 0 * ((f.val 0).val + (tangentProduct K n d g).val) = 0 := by
    calc
      _ = X 0 * (f.val 0).val + ∑ i : Fin n, X i.succ * (X 0 * (g i).val) := by
        rw [mul_add, tangentProduct_val, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hrel
  have hzero : (f.val 0).val + (tangentProduct K n d g).val = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (X_ne_zero 0)
  have hfirst : (f.val 0).val = -(tangentProduct K n d g).val :=
    eq_neg_iff_add_eq_zero.mpr hzero
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext j
  apply Subtype.ext
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hfirst.symm
  · exact (hg i).symm

/-- Exactness in the middle of the hyperplane Euler sequence (3.1). -/
theorem trace_ker_eq_range (d : ℕ) :
    (trace K n (d + 1)).ker = (normalInjection K n d).range := by
  ext f
  constructor
  · intro hf
    exact exists_normal_of_trace_eq_zero K n d f hf
  · rintro ⟨g, rfl⟩
    exact trace_normalInjection K n d g

end IdealGeneration.HyperplaneEuler
