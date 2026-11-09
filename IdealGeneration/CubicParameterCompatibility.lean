module

public import IdealGeneration.PointAvoidance
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Nonzero coefficient conditions for the shared old and new cubic parameters. -/

noncomputable section
namespace IdealGeneration.CubicParameterCompatibility
open MvPolynomial

variable {K : Type*} [Field K] {Old New Label : Type*}

/-- A polynomial in the new parameters whose coefficients vary with the old
parameters, specialized at a fixed old configuration. -/
def specialize (x : Old → K) (P : MvPolynomial New (MvPolynomial Old K)) :
    MvPolynomial New K :=
  MvPolynomial.map (eval x) P

@[simp] theorem coeff_specialize (x : Old → K)
    (P : MvPolynomial New (MvPolynomial Old K)) (e : New →₀ ℕ) :
    (specialize x P).coeff e = eval x (P.coeff e) :=
  MvPolynomial.coeff_map _ _ _

/-- A nonzero coefficient gives a principal open of old parameters on which
the new-parameter polynomial is nonzero. -/
theorem exists_fiber_coefficient (P : MvPolynomial New (MvPolynomial Old K)) (hP : P ≠ 0) :
    ∃ D : MvPolynomial Old K, D ≠ 0 ∧
      ∀ x : Old → K, eval x D ≠ 0 → specialize x P ≠ 0 := by
  have he : ∃ e, P.coeff e ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.ext
    intro e
    simpa using h e
  obtain ⟨e, he⟩ := he
  refine ⟨P.coeff e, he, fun x hx hz => hx ?_⟩
  rw [← coeff_specialize x P e, hz]
  simp

/-- All prescribed new-parameter determinants can retain a nonzero
coefficient on one old-parameter principal open. -/
theorem joint_fiber_open [Fintype Label]
    (G : MvPolynomial Old K) (hG : G ≠ 0)
    (P : Label → MvPolynomial New (MvPolynomial Old K)) (hP : ∀ l, P l ≠ 0) :
    ∃ D : MvPolynomial Old K, D ≠ 0 ∧ ∀ x : Old → K, eval x D ≠ 0 →
      eval x G ≠ 0 ∧ ∀ l, specialize x (P l) ≠ 0 := by
  classical
  choose Q hQ hgood using fun l => exists_fiber_coefficient (P l) (hP l)
  refine ⟨G * ∏ l, Q l, mul_ne_zero hG (Finset.prod_ne_zero_iff.mpr fun l _ => hQ l), ?_⟩
  intro x hx
  have hx' : eval x G ≠ 0 ∧ ∀ l, eval x (Q l) ≠ 0 := by
    simpa only [map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, true_implies] using hx
  exact ⟨hx'.1, fun l => hgood l x (hx'.2 l)⟩

/-- At a fixed good old parameter, finitely many block determinants and any
extra future coefficient-open condition can be imposed on the same new data. -/
theorem exists_shared_extension [Infinite K] [Fintype Label]
    (P : Label → MvPolynomial New K) (hP : ∀ l, P l ≠ 0)
    (F : MvPolynomial New K) (hF : F ≠ 0) :
    ∃ y : New → K, eval y F ≠ 0 ∧ ∀ l, eval y (P l) ≠ 0 := by
  classical
  have hprod : F * ∏ l, P l ≠ 0 :=
    mul_ne_zero hF (Finset.prod_ne_zero_iff.mpr fun l _ => hP l)
  have hex : ∃ y : New → K, eval y (F * ∏ l, P l) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, by simpa only [map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, true_implies] using hy⟩

/-- Initial middle rank and future block conditions meet in the shared old
parameters, and the retained conditions give a simultaneous extension. -/
theorem exists_compatible_old_new [Infinite K] [Fintype Label]
    (G : MvPolynomial Old K) (hG : G ≠ 0)
    (P : Label → MvPolynomial New (MvPolynomial Old K)) (hP : ∀ l, P l ≠ 0)
    (F : MvPolynomial New K) (hF : F ≠ 0) :
    ∃ (x : Old → K) (y : New → K), eval x G ≠ 0 ∧ eval y F ≠ 0 ∧
      ∀ l, eval y (specialize x (P l)) ≠ 0 := by
  obtain ⟨D, hD, hgood⟩ := joint_fiber_open G hG P hP
  have hx : ∃ x : Old → K, eval x D ≠ 0 := by
    by_contra! h
    exact hD (MvPolynomial.funext h)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨hxG, hxP⟩ := hgood x hx
  obtain ⟨y, hyF, hyP⟩ := exists_shared_extension (fun l => specialize x (P l)) hxP F hF
  exact ⟨x, y, hxG, hyF, hyP⟩

/-- Converting disjoint old and new variables into an iterated polynomial
ring preserves the nonvanishing of the determinant polynomial. -/
theorem sumPolynomial_ne_zero (P : MvPolynomial (New ⊕ Old) K) (hP : P ≠ 0) :
    MvPolynomial.sumAlgEquiv K New Old P ≠ 0 := by
  intro hz
  apply hP
  apply (MvPolynomial.sumAlgEquiv K New Old).injective
  simpa only [map_zero] using hz

/-- Evaluating the specialized polynomial gives evaluation at the joint
new and old parameter values. -/
theorem eval_specialize_sumPolynomial (x : Old → K) (y : New → K)
    (P : MvPolynomial (New ⊕ Old) K) :
    eval y (specialize x (MvPolynomial.sumAlgEquiv K New Old P)) =
      eval (Sum.elim y x) P := by
  let f := (eval y).comp ((MvPolynomial.map (eval x)).comp
    (MvPolynomial.sumAlgEquiv K New Old).toRingHom)
  have hf : f = eval (Sum.elim y x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change eval y (specialize x (MvPolynomial.sumAlgEquiv K New Old (C r))) = _
      simp [specialize, MvPolynomial.sumAlgEquiv_C_inl]
    · rintro (i | j)
      · change eval y (specialize x (MvPolynomial.sumAlgEquiv K New Old
          (X (.inl i)))) = _
        simp [specialize, MvPolynomial.sumAlgEquiv_X_inl]
      · change eval y (specialize x (MvPolynomial.sumAlgEquiv K New Old
          (X (.inr j)))) = _
        simp [specialize, MvPolynomial.sumAlgEquiv_X_inr]
  exact congrArg (fun F : MvPolynomial (New ⊕ Old) K →+* K => F P) hf

end IdealGeneration.CubicParameterCompatibility
