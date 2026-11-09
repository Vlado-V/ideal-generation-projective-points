module

public import IdealGeneration.CubicPrimitiveSplit
public import IdealGeneration.CubicParameterCompatibility

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Distinct single-edge slopes on every admissible old-parameter fiber. -/

noncomputable section
namespace IdealGeneration.CubicSupported.RationalChart

open MvPolynomial CubicParameterCompatibility

variable (K : Type*) [Field K] {m : ℕ}

private abbrev GuardEdge (single : Edge m → Bool) := {e : Edge m // single e = true}

/-- The product of all differences between distinct graph-single slopes. -/
def singleSlopeGuard (single : Edge m → Bool) : MvPolynomial (PrimitiveIndex m) K :=
  ∏ e : GuardEdge single, ∏ f ∈ Finset.univ.erase e,
    (X (.edgeSlope e.val 0) - X (.edgeSlope f.val 0))

variable {K}

theorem eval_singleSlopeGuard (x : PrimitiveIndex m → K) (single : Edge m → Bool) :
    eval x (singleSlopeGuard K single) =
      ∏ e : GuardEdge single, ∏ f ∈ Finset.univ.erase e,
        (x (.edgeSlope e.val 0) - x (.edgeSlope f.val 0)) := by
  simp only [singleSlopeGuard, map_prod, map_sub, eval_X]

/-- Guard evaluation is nonzero exactly when all single slopes are distinct. -/
theorem eval_singleSlopeGuard_ne_zero_iff (x : PrimitiveIndex m → K) (single : Edge m → Bool) :
    eval x (singleSlopeGuard K single) ≠ 0 ↔
      Set.InjOn (fun e : Edge m => x (.edgeSlope e 0)) {e | single e = true} := by
  rw [eval_singleSlopeGuard]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, Finset.mem_erase, and_true, true_implies,
    sub_ne_zero]
  constructor
  · intro h e he f hf hEq
    by_contra hne
    exact h ⟨e, he⟩ ⟨f, hf⟩ (fun hEF => hne (congrArg Subtype.val hEF).symm) hEq
  · intro h e f hfe hEq
    exact hfe (Subtype.ext (h e.property f.property hEq).symm)

/-- The initial guard itself is a nonzero polynomial in the primitive variables. -/
theorem singleSlopeGuard_ne_zero (single : Edge m → Bool) : singleSlopeGuard K single ≠ 0 := by
  rw [singleSlopeGuard]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  apply Finset.prod_ne_zero_iff.mpr
  intro f hf
  apply sub_ne_zero.mpr
  intro hX
  have heq := (PrimitiveIndex.edgeSlope.inj (X_injective hX)).1
  exact (Finset.mem_erase.mp hf).1 (Subtype.ext heq.symm)

/-- The guard with old labels in the coefficient ring and new labels as variables. -/
def singleSlopeGuardFiber (K : Type*) [Field K] (single : Edge (m + 2) → Bool) :
    MvPolynomial (NewPrimitiveIndex m) (MvPolynomial (PrimitiveIndex m) K) :=
  MvPolynomial.sumAlgEquiv K (NewPrimitiveIndex m) (PrimitiveIndex m)
    (rename (primitiveOldNewEquiv m).symm (singleSlopeGuard K single))

/-- Evaluate an old fiber at the joint assignment of new and old primitive values. -/
theorem eval_specialize_singleSlopeGuardFiber (x : PrimitiveIndex m → K)
    (y : NewPrimitiveIndex m → K) (single : Edge (m + 2) → Bool) :
    eval y (specialize x (singleSlopeGuardFiber K single)) =
      eval (fun i => Sum.elim y x ((primitiveOldNewEquiv m).symm i)) (singleSlopeGuard K single) := by
  rw [singleSlopeGuardFiber, eval_specialize_sumPolynomial, MvPolynomial.eval_rename]
  rfl

/-- A fiber guard checks distinctness at precisely the combined assignment. -/
theorem eval_specialize_singleSlopeGuardFiber_ne_zero_iff (x : PrimitiveIndex m → K)
    (y : NewPrimitiveIndex m → K) (single : Edge (m + 2) → Bool) :
    eval y (specialize x (singleSlopeGuardFiber K single)) ≠ 0 ↔
      Set.InjOn (fun e : Edge (m + 2) =>
        Sum.elim y x ((primitiveOldNewEquiv m).symm (.edgeSlope e 0))) {e | single e = true} := by
  rw [eval_specialize_singleSlopeGuardFiber, eval_singleSlopeGuard_ne_zero_iff]

private def specializePrimitive (x : PrimitiveIndex m → K) :
    MvPolynomial (PrimitiveIndex (m + 2)) K →+* MvPolynomial (NewPrimitiveIndex m) K :=
  (MvPolynomial.map (eval x)).comp
    ((MvPolynomial.sumAlgEquiv K (NewPrimitiveIndex m) (PrimitiveIndex m)).toRingHom.comp
      (rename (primitiveOldNewEquiv m).symm).toRingHom)

private theorem specializePrimitive_X (x : PrimitiveIndex m → K) (i : PrimitiveIndex (m + 2)) :
    specializePrimitive x (X i) = Sum.elim X (fun j => C (x j)) ((primitiveOldNewEquiv m).symm i) := by
  change specialize x (MvPolynomial.sumAlgEquiv K (NewPrimitiveIndex m) (PrimitiveIndex m)
    (rename (primitiveOldNewEquiv m).symm (X i))) = _
  rw [rename_X]
  rcases (primitiveOldNewEquiv m).symm i with j | j
  · simp [specialize, MvPolynomial.sumAlgEquiv_X_inl]
  · simp [specialize, MvPolynomial.sumAlgEquiv_X_inr]

private theorem variable_ne_constant {ι : Type*} (i : ι) (a : K) :
    (X i : MvPolynomial ι K) ≠ C a := by
  intro h
  have h₀ : (0 : K) = a := by simpa using congrArg (eval (fun _ : ι => (0 : K))) h
  have h₁ : (1 : K) = a := by simpa using congrArg (eval (fun _ : ι => (1 : K))) h
  exact zero_ne_one (h₀.trans h₁.symm)

private theorem old_edgeSlope_label {i : PrimitiveIndex m} {e : Edge (m + 2)}
    (h : oldPrimitiveIndex m i = .edgeSlope e 0) :
    ∃ a : Edge m, i = .edgeSlope a 0 ∧ oldEdge m a = e := by
  cases i with
  | vertexSlope j d => cases h
  | vertexHeight j d => cases h
  | edgeHeight a d => cases h
  | edgeLambda a => cases h
  | edgeSlope a d =>
    change PrimitiveIndex.edgeSlope (oldEdge m a) d = .edgeSlope e 0 at h
    obtain ⟨he, hd⟩ := PrimitiveIndex.edgeSlope.inj h
    exact ⟨a, congrArg (PrimitiveIndex.edgeSlope a) hd, he⟩

private theorem specializePrimitive_slope_injOn (x : PrimitiveIndex m → K)
    (single : Edge (m + 2) → Bool)
    (hold : Set.InjOn (fun e : Edge m => x (.edgeSlope e 0)) {e | single (oldEdge m e) = true}) :
    Set.InjOn (fun e : Edge (m + 2) => specializePrimitive x (X (.edgeSlope e 0)))
      {e | single e = true} := by
  intro e he f hf hEq
  change specializePrimitive x (X (.edgeSlope e 0)) = specializePrimitive x (X (.edgeSlope f 0)) at hEq
  rw [specializePrimitive_X, specializePrimitive_X] at hEq
  cases he' : (primitiveOldNewEquiv m).symm (.edgeSlope e 0) with
  | inl a =>
    cases hf' : (primitiveOldNewEquiv m).symm (.edgeSlope f 0) with
    | inl b =>
      rw [he', hf'] at hEq
      change (X a : MvPolynomial (NewPrimitiveIndex m) K) = X b at hEq
      have hab := X_injective hEq
      have hlabels : PrimitiveIndex.edgeSlope e 0 = .edgeSlope f 0 :=
        (primitiveOldNewEquiv m).symm.injective (he'.trans ((congrArg Sum.inl hab).trans hf'.symm))
      exact (PrimitiveIndex.edgeSlope.inj hlabels).1
    | inr j =>
      rw [he', hf'] at hEq
      exact (variable_ne_constant a (x j) hEq).elim
  | inr i =>
    cases hf' : (primitiveOldNewEquiv m).symm (.edgeSlope f 0) with
    | inl b =>
      rw [he', hf'] at hEq
      exact (variable_ne_constant b (x i) hEq.symm).elim
    | inr j =>
      rw [he', hf'] at hEq
      have heL := congrArg (primitiveOldNewEquiv m) he'
      have hfL := congrArg (primitiveOldNewEquiv m) hf'
      simp only [Equiv.apply_symm_apply, primitiveOldNewEquiv_inr] at heL hfL
      obtain ⟨a, haI, haE⟩ := old_edgeSlope_label heL.symm
      obtain ⟨b, hbI, hbE⟩ := old_edgeSlope_label hfL.symm
      change (C (x i) : MvPolynomial (NewPrimitiveIndex m) K) = C (x j) at hEq
      have hab := MvPolynomial.C_injective (NewPrimitiveIndex m) K hEq
      rw [haI, hbI] at hab
      have ha : a ∈ {e | single (oldEdge m e) = true} := by
        change single (oldEdge m a) = true
        rwa [haE]
      have hb : b ∈ {e | single (oldEdge m e) = true} := by
        change single (oldEdge m b) = true
        rwa [hbE]
      exact haE.symm.trans ((congrArg (oldEdge m) (hold ha hb hab)).trans hbE)

/-- Distinct old single slopes leave a nonzero guard polynomial in the new variables. -/
theorem specialize_singleSlopeGuardFiber_ne_zero (x : PrimitiveIndex m → K)
    (single : Edge (m + 2) → Bool)
    (hold : Set.InjOn (fun e : Edge m => x (.edgeSlope e 0)) {e | single (oldEdge m e) = true}) :
    specialize x (singleSlopeGuardFiber K single) ≠ 0 := by
  change specializePrimitive x (singleSlopeGuard K single) ≠ 0
  rw [singleSlopeGuard, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun f hf => ?_
  rw [map_sub, sub_ne_zero]
  intro hEq
  have h := specializePrimitive_slope_injOn x single hold e.property f.property hEq
  exact (Finset.mem_erase.mp hf).1 (Subtype.ext h.symm)

/-- Compatibility transfers the old actual slope condition to the new-parameter fiber. -/
theorem specialize_singleSlopeGuardFiber_ne_zero_of_compatible
    {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)
    (hold : Set.InjOn (fun e : Edge m => P.edgeSlope e 0) {e | P.single e = true}) :
    specialize (primitiveValue P) (singleSlopeGuardFiber K Q.single) ≠ 0 := by
  apply specialize_singleSlopeGuardFiber_ne_zero
  simpa only [primitiveValue, h.single_eq] using hold

end IdealGeneration.CubicSupported.RationalChart
