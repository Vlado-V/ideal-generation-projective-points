module

public import IdealGeneration.ConeMiddleFamily
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Monomial coordinates for the trace and normal parts of the cone middle map. -/

noncomputable section
namespace IdealGeneration.ConeMonomialChart
open MvPolynomial Module

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] {n c m d : ℕ}

local instance (priority := 2000) canonicalSubmoduleGroup
    {A : Type*} [AddCommMonoid A] [Module K A] (S : Submodule K A) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup K

/-- Synthesis in an explicitly ordered list of monomials. -/
def synth (e : ι → Fin n →₀ ℕ) : (ι → K) →ₗ[K] Poly K n :=
  ∑ i, (monomial (e i)).comp (LinearMap.proj i)

@[simp] theorem synth_apply (e : ι → Fin n →₀ ℕ) (u : ι → K) :
    synth e u = ∑ i, monomial (e i) (u i) := by
  simp [synth]

theorem synth_injective (e : ι → Fin n →₀ ℕ) (he : Function.Injective e) :
    Function.Injective (synth (K := K) e) := by
  classical
  intro u v h
  funext i
  have hc := congrArg (fun f : Poly K n => f.coeff (e i)) h
  simpa only [synth_apply, coeff_sum, coeff_monomial, he.eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hc

/-- Coefficient synthesis with its degree certificate. -/
def formSynth (e : ι → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = d) :
    (ι → K) →ₗ[K] Forms K n d :=
  (synth e).codRestrict _ fun u => by
    rw [synth_apply]
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_monomial _ (he i)

theorem coneRestrict_monomial_eq_zero (e : Fin (c + m) →₀ ℕ)
    (he : ∃ i : Fin c, e (i.castAdd m) ≠ 0) (a : K) :
    coneRestrict K c m (monomial e a) = 0 := by
  obtain ⟨i, hi⟩ := he
  rw [monomial_eq, map_mul, Finsupp.prod_fintype, map_prod]
  · have hz : (∏ j : Fin (c + m), coneRestrict K c m (X j ^ e j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (i.castAdd m))
      simp [hi]
    rw [hz, mul_zero]
  · simp

/-- Synthesis of monomials that vanish after normal restriction. -/
def normalSynth (e : ι → Fin (c + m) →₀ ℕ)
    (hd : ∀ i, (e i).degree = d) (hn : ∀ i, ∃ j : Fin c, e i (j.castAdd m) ≠ 0) :
    (ι → K) →ₗ[K] ConeMiddleFamily.normalForms K c m d :=
  (formSynth e hd).codRestrict _ fun u => by
    change coneRestrictForm K c m d (formSynth e hd u) = 0
    apply Subtype.ext
    change coneRestrict K c m (synth e u) = 0
    simp [map_sum, coneRestrict_monomial_eq_zero _ (hn _)]

private theorem surjective_of_injective_of_finrank_eq {V W : Type*}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (hi : Function.Injective f) (hr : finrank K V = finrank K W) :
    Function.Surjective f := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj hi, hr]

theorem formSynth_surjective (e : ι → Fin n →₀ ℕ) (hd : ∀ i, (e i).degree = d)
    (he : Function.Injective e) (hcard : Fintype.card ι = (n + d - 1).choose d) :
    Function.Surjective (formSynth (K := K) e hd) := by
  refine surjective_of_injective_of_finrank_eq (K := K) (V := ι → K)
    (W := Forms K n d) (formSynth e hd) ?_ ?_
  · intro u v h
    exact synth_injective e he (congrArg Subtype.val h)
  · simpa only [Module.finrank_fintype_fun_eq_card, finrank_forms] using hcard

theorem normalForms_finrank (K : Type*) [Field K] (c m d : ℕ) :
    finrank K (ConeMiddleFamily.normalForms K c m d) =
      (c + m + d - 1).choose d - (m + d - 1).choose d := by
  let f := coneRestrictForm K c m d
  have hs : Function.Surjective f := fun g => ⟨coneExtendForm K c m d g,
    coneRestrictForm_extendForm K c m g⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_forms, finrank_forms] at h
  change _ + finrank K (ConeMiddleFamily.normalForms K c m d) = _ at h
  omega

theorem normalSynth_surjective (e : ι → Fin (c + m) →₀ ℕ)
    (hd : ∀ i, (e i).degree = d) (hn : ∀ i, ∃ j : Fin c, e i (j.castAdd m) ≠ 0)
    (he : Function.Injective e)
    (hcard : Fintype.card ι = (c + m + d - 1).choose d - (m + d - 1).choose d) :
    Function.Surjective (normalSynth (K := K) e hd hn) := by
  refine surjective_of_injective_of_finrank_eq (K := K) (V := ι → K)
    (W := ConeMiddleFamily.normalForms K c m d) (normalSynth e hd hn) ?_ ?_
  · intro u v h
    exact synth_injective e he (congrArg (fun f => f.val.val) h)
  · simpa only [Module.finrank_fintype_fun_eq_card, normalForms_finrank] using hcard

/-- Evaluation at actual representatives in the selected monomial ordering. -/
def evaluationMatrix {R : Type*} [CommSemiring R] {κ : Type*}
    (z : κ → Fin n → R) (e : ι → Fin n →₀ ℕ) : Matrix κ ι R :=
  fun i j => ∏ k, z i k ^ e j k

theorem evaluationMatrix_mulVec (z : Fin n → K) (e : ι → Fin n →₀ ℕ) (u : ι → K) :
    eval z (synth e u) = ∑ i, (∏ k, z k ^ e i k) * u i := by
  simp [eval_monomial, Finsupp.prod_fintype, mul_comm]

omit [Fintype ι] in
theorem evaluationMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (k : R →+* S) {κ : Type*} (z : κ → Fin n → R) (e : ι → Fin n →₀ ℕ) :
    (evaluationMatrix z e).map k = evaluationMatrix (fun i j => k (z i j)) e := by
  ext i j
  simp [evaluationMatrix, map_prod]

end IdealGeneration.ConeMonomialChart
