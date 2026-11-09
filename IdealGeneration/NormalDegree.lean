module

public import IdealGeneration.ConeSplitting
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Normal-degree components of actual homogeneous polynomials. -/

noncomputable section
namespace IdealGeneration.NormalDegree
open MvPolynomial

variable (K : Type*) [Field K] (c m : ℕ)

/-- The degree counts only the first, normal coordinates. -/
def normalWeight : Fin (c + m) → ℕ :=
  Fin.addCases (fun _ : Fin c => 1) (fun _ : Fin m => 0)

/-- The complementary degree counts the trace coordinates. -/
def traceWeight : Fin (c + m) → ℕ :=
  Fin.addCases (fun _ : Fin c => 0) (fun _ : Fin m => 1)

@[simp] theorem normalWeight_normal (i : Fin c) : normalWeight c m (i.castAdd m) = 1 := by
  simp [normalWeight]
@[simp] theorem normalWeight_trace (i : Fin m) : normalWeight c m (i.natAdd c) = 0 := by
  simp [normalWeight]
@[simp] theorem traceWeight_normal (i : Fin c) : traceWeight c m (i.castAdd m) = 0 := by
  simp [traceWeight]
@[simp] theorem traceWeight_trace (i : Fin m) : traceWeight c m (i.natAdd c) = 1 := by
  simp [traceWeight]

/-- The pure-normal restriction sets the trace variables to zero. -/
def pureRestrict : Poly K (c + m) →ₐ[K] Poly K c :=
  aeval (Fin.addCases (fun i : Fin c => X i) (fun _ : Fin m => 0))

/-- Include a polynomial involving only normal coordinates. -/
def pureExtend : Poly K c →ₐ[K] Poly K (c + m) := rename (Fin.castAdd m)

@[simp] theorem pureRestrict_X_normal (i : Fin c) :
    pureRestrict K c m (X (i.castAdd m)) = X i := by simp [pureRestrict]
@[simp] theorem pureRestrict_X_trace (i : Fin m) :
    pureRestrict K c m (X (i.natAdd c)) = 0 := by simp [pureRestrict]
@[simp] theorem pureExtend_X (i : Fin c) :
    pureExtend K c m (X i) = X (i.castAdd m) := by simp [pureExtend]

@[simp] theorem pureRestrict_extend (f : Poly K c) :
    pureRestrict K c m (pureExtend K c m f) = f := by
  have hh : (pureRestrict K c m).comp (pureExtend K c m) = AlgHom.id K _ := by
    ext i
    simp
  exact congrArg (fun F : Poly K c →ₐ[K] Poly K c => F f) hh

theorem pureRestrict_homogeneous {d : ℕ} {f : Poly K (c + m)}
    (hf : f.IsHomogeneous d) : (pureRestrict K c m f).IsHomogeneous d := by
  simpa only [one_mul, pureRestrict] using hf.aeval (n := 1)
    (Fin.addCases (fun i : Fin c => X i) (fun _ : Fin m => 0))
    (by intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.addCases_left] using (isHomogeneous_X K j)
        · simpa only [Fin.addCases_right] using (isHomogeneous_zero (σ := Fin c) (R := K) 1))

def pureRestrictForm (d : ℕ) : Forms K (c + m) d →ₗ[K] Forms K c d where
  toFun f := ⟨pureRestrict K c m f.val, pureRestrict_homogeneous K c m f.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def pureExtendForm (d : ℕ) : Forms K c d →ₗ[K] Forms K (c + m) d where
  toFun f := ⟨pureExtend K c m f.val, f.property.rename_isHomogeneous⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem pureRestrictForm_extendForm {d : ℕ} (f : Forms K c d) :
    pureRestrictForm K c m d (pureExtendForm K c m d f) = f := by
  apply Subtype.ext
  exact pureRestrict_extend K c m f.val

/-- Normal-degree projection is the actual weighted homogeneous component. -/
def component (r : ℕ) : Poly K (c + m) →ₗ[K] Poly K (c + m) :=
  weightedHomogeneousComponent (normalWeight c m) r

theorem component_homogeneous {d r : ℕ} {f : Poly K (c + m)}
    (hf : f.IsHomogeneous d) : (component K c m r f).IsHomogeneous d := by
  intro e he
  have hcoeff : f.coeff e ≠ 0 := by
    intro hz
    simp [component, coeff_weightedHomogeneousComponent, hz] at he
  exact hf hcoeff

/-- The two component degrees add to the ordinary total degree. -/
theorem weight_add (e : Fin (c + m) →₀ ℕ) :
    Finsupp.weight (normalWeight c m) e + Finsupp.weight (traceWeight c m) e = e.degree := by
  simp only [Finsupp.weight_eq_sum, Finsupp.degree_eq_weight_one]
  simp [Fin.sum_univ_add, normalWeight, traceWeight]

/-- The homogeneous total degree determines the complementary trace degree. -/
theorem trace_homogeneous {d r : ℕ} {f : Poly K (c + m)}
    (hf : f.IsHomogeneous d) (hr : f.IsWeightedHomogeneous (normalWeight c m) r)
    (hrd : r ≤ d) : f.IsWeightedHomogeneous (traceWeight c m) (d - r) := by
  intro e he
  have hd := hf he
  have hn := hr he
  have hadd := weight_add c m e
  have hd' : e.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  omega

/-- A polynomial of weighted degree zero is unchanged by every substitution
that fixes the variables of weight zero. -/
theorem weighted_zero_substitution {σ : Type*} (w : σ → ℕ)
    (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w 0)
    (v : σ → MvPolynomial σ K) (hv : ∀ i, w i = 0 → v i = X i) :
    eval₂ C v f = f := by
  classical
  have hmono (e : σ →₀ ℕ) (he : Finsupp.weight w e = 0) (a : K) :
      eval₂ C v (monomial e a) = monomial e a := by
    rw [eval₂_monomial, monomial_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hterm : e i * w i = 0 := by
      have hh : ∑ j ∈ e.support, e j * w j = 0 := by
        simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using he
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hh i hi
    have hi' : e i ≠ 0 := Finsupp.mem_support_iff.mp hi
    change v i ^ e i = X i ^ e i
    rw [hv i ((mul_eq_zero.mp hterm).resolve_left hi')]
  calc
    eval₂ C v f = eval₂ C v (∑ e ∈ f.support, monomial e (f.coeff e)) :=
      congrArg (eval₂ C v) f.as_sum
    _ = ∑ e ∈ f.support, eval₂ C v (monomial e (f.coeff e)) := by simp only [eval₂_sum]
    _ = ∑ e ∈ f.support, monomial e (f.coeff e) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hmono e (hf (mem_support_iff.mp he)) _
    _ = f := f.as_sum.symm

/-- Weighted degree zero in the normal variables means a pure trace polynomial. -/
theorem extend_restrict_of_normal_zero {f : Poly K (c + m)}
    (hf : f.IsWeightedHomogeneous (normalWeight c m) 0) :
    coneExtend K c m (coneRestrict K c m f) = f := by
  have hh : (coneExtend K c m).toRingHom.comp (coneRestrict K c m).toRingHom =
      eval₂Hom C (Fin.addCases (fun _ : Fin c => 0) (fun j : Fin m => X (j.natAdd c))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [coneExtend, coneRestrict]
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  change ((coneExtend K c m).toRingHom.comp (coneRestrict K c m).toRingHom) f = f
  rw [hh]
  apply weighted_zero_substitution K (normalWeight c m) f hf
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; simp at hi
  · intro hi; simp

/-- Weighted degree zero in the trace variables means a pure normal polynomial. -/
theorem extend_restrict_of_trace_zero {f : Poly K (c + m)}
    (hf : f.IsWeightedHomogeneous (traceWeight c m) 0) :
    pureExtend K c m (pureRestrict K c m f) = f := by
  have hh : (pureExtend K c m).toRingHom.comp (pureRestrict K c m).toRingHom =
      eval₂Hom C (Fin.addCases (fun i : Fin c => X (i.castAdd m)) (fun _ : Fin m => 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [pureExtend, pureRestrict]
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  change ((pureExtend K c m).toRingHom.comp (pureRestrict K c m).toRingHom) f = f
  rw [hh]
  apply weighted_zero_substitution K (traceWeight c m) f hf
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; simp
  · intro hi; simp at hi

/-- The canonical vector of trace coefficients of the normal-linear part. -/
def linearCoefficient (d : ℕ) (f : Forms K (c + m) (d + 1)) (i : Fin c) : Forms K m d :=
  ⟨coneRestrict K c m (pderiv (i.castAdd m) f.val),
    coneRestrict_homogeneous K c m (by simpa using f.property.pderiv (i := i.castAdd m))⟩

/-- Normal-weight-one forms are exactly the sums of their normal variables
multiplied by these canonical trace coefficients. -/
theorem linear_reconstruct {d : ℕ} (f : Forms K (c + m) (d + 1))
    (hf : f.val.IsWeightedHomogeneous (normalWeight c m) 1) :
    f.val = ∑ i : Fin c, X (i.castAdd m) *
      coneExtend K c m (linearCoefficient K c m d f i).val := by
  have heuler := hf.sum_weight_X_mul_pderiv
  simp only [Fin.sum_univ_add, normalWeight_normal, normalWeight_trace,
    one_nsmul, zero_nsmul, Finset.sum_const_zero, add_zero] at heuler
  rw [← heuler]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply (extend_restrict_of_normal_zero K c m
    (hf.pderiv (i := i.castAdd m) (by simp))).symm

/-- Killing every variable of positive weight kills every homogeneous form of
strictly positive weighted degree. -/
theorem weighted_positive_eval₂ {σ R : Type*} [CommSemiring R]
    (w : σ → ℕ) (f : MvPolynomial σ K) {r : ℕ}
    (hf : f.IsWeightedHomogeneous w r) (hr : 0 < r)
    (k : K →+* R) (v : σ → R) (hv : ∀ i, w i ≠ 0 → v i = 0) :
    eval₂ k v f = 0 := by
  classical
  have hmono (e : σ →₀ ℕ) (he : Finsupp.weight w e = r) (a : K) :
      eval₂ k v (monomial e a) = 0 := by
    have hex : ∃ i ∈ e.support, w i ≠ 0 := by
      by_contra! hall
      have hz : Finsupp.weight w e = 0 := by
        simp only [Finsupp.weight_apply, Finsupp.sum]
        apply Finset.sum_eq_zero
        intro i hi
        rw [hall i hi, smul_zero]
      omega
    obtain ⟨i, hi, hwi⟩ := hex
    rw [eval₂_monomial]
    have hp : e.prod (fun j n => v j ^ n) = 0 := by
      apply Finset.prod_eq_zero hi
      change v i ^ e i = 0
      rw [hv i hwi, zero_pow (Finsupp.mem_support_iff.mp hi)]
    rw [hp, mul_zero]
  calc
    eval₂ k v f = eval₂ k v (∑ e ∈ f.support, monomial e (f.coeff e)) :=
      congrArg (eval₂ k v) f.as_sum
    _ = ∑ e ∈ f.support, eval₂ k v (monomial e (f.coeff e)) := by simp only [eval₂_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact hmono e (hf (mem_support_iff.mp he)) _

theorem component_weighted (r : ℕ) (f : Poly K (c + m)) :
    (component K c m r f).IsWeightedHomogeneous (normalWeight c m) r :=
  weightedHomogeneousComponent_isWeightedHomogeneous r f

/-- Every degree-d polynomial is the sum of its normal-degree components 0,...,d. -/
theorem sum_components {d : ℕ} (f : Forms K (c + m) d) :
    f.val = ∑ r ∈ Finset.range (d + 1), component K c m r f.val := by
  classical
  ext e
  simp only [coeff_sum, component, coeff_weightedHomogeneousComponent]
  by_cases he : f.val.coeff e = 0
  · simp [he]
  · have hd := f.property he
    have hb := weight_add c m e
    have hn : Finsupp.weight (normalWeight c m) e < d + 1 := by
      have hd' : e.degree = d := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      omega
    rw [Finset.sum_eq_single (Finsupp.weight (normalWeight c m) e)]
    · simp
    · intro b hb hbn
      simp [Ne.symm hbn]
    · intro hn'
      exact False.elim (hn' (Finset.mem_range.mpr hn))

/-- Restriction to the trace kills every positive normal-degree component. -/
theorem restrict_component_eq_zero {r : ℕ} (hr : 0 < r) (f : Poly K (c + m)) :
    coneRestrict K c m (component K c m r f) = 0 := by
  apply weighted_positive_eval₂ K (normalWeight c m) _ (component_weighted K c m r f) hr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; simp
  · intro hi; simp at hi

/-- A component below the total degree vanishes after all trace variables are zeroed. -/
theorem pureRestrict_component_eq_zero {d r : ℕ} (f : Forms K (c + m) d)
    (hr : r < d) : pureRestrict K c m (component K c m r f.val) = 0 := by
  apply weighted_positive_eval₂ K (traceWeight c m) _
    (trace_homogeneous K c m (component_homogeneous K c m f.property)
      (component_weighted K c m r f.val) (Nat.le_of_lt hr)) (by omega)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; simp at hi
  · intro hi; simp

/-- The top normal-degree component is the extension of the pure-normal part. -/
theorem top_component {d : ℕ} (f : Forms K (c + m) d) :
    component K c m d f.val = pureExtend K c m (pureRestrict K c m f.val) := by
  have htrace := trace_homogeneous K c m (component_homogeneous K c m f.property)
    (component_weighted K c m d f.val) le_rfl
  have hcomp : pureExtend K c m (pureRestrict K c m (component K c m d f.val)) =
      component K c m d f.val := extend_restrict_of_trace_zero K c m (by simpa using htrace)
  have hp := congrArg (pureRestrict K c m) (sum_components K c m f)
  rw [map_sum] at hp
  have hs : (∑ r ∈ Finset.range (d + 1), pureRestrict K c m (component K c m r f.val)) =
      pureRestrict K c m (component K c m d f.val) := by
    apply Finset.sum_eq_single d
    · intro r hr hrd
      exact pureRestrict_component_eq_zero K c m f (by have := Finset.mem_range.mp hr; omega)
    · simp
  rw [hs] at hp
  rw [hp]
  exact hcomp.symm

/-- The normal-degree-zero component is the extension of the trace restriction. -/
theorem zero_component {d : ℕ} (f : Forms K (c + m) d) :
    component K c m 0 f.val = coneExtend K c m (coneRestrict K c m f.val) := by
  have hcomp := extend_restrict_of_normal_zero K c m (component_weighted K c m 0 f.val)
  have hp := congrArg (coneRestrict K c m) (sum_components K c m f)
  rw [map_sum] at hp
  have hs : (∑ r ∈ Finset.range (d + 1), coneRestrict K c m (component K c m r f.val)) =
      coneRestrict K c m (component K c m 0 f.val) := by
    apply Finset.sum_eq_single 0
    · intro r hr hr0
      exact restrict_component_eq_zero K c m (Nat.pos_of_ne_zero hr0) f.val
    · simp
  rw [hs] at hp
  rw [hp]
  exact hcomp.symm

/-- Package a normal-degree component without changing total degree. -/
def componentForm {d : ℕ} (r : ℕ) : Forms K (c + m) d →ₗ[K] Forms K (c + m) d where
  toFun f := ⟨component K c m r f.val, component_homogeneous K c m f.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- A normal-ideal quadric has only its mixed and pure-normal parts. -/
theorem quadratic_split (f : Forms K (c + m) 2)
    (hf : coneRestrictForm K c m 2 f = 0) :
    f.val = (componentForm K c m 1 f).val +
      pureExtend K c m (pureRestrict K c m f.val) := by
  have hs := sum_components K c m f
  have hz : component K c m 0 f.val = 0 := by
    rw [zero_component]
    have hzero : coneRestrict K c m f.val = 0 := congrArg Subtype.val hf
    rw [hzero, map_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  rw [hz, zero_add, top_component] at hs
  exact hs

/-- Coefficients of trace-linear homogeneous forms, in the normal polynomial ring. -/
def traceCoefficient (d : ℕ) (f : Forms K (c + m) (d + 1)) (i : Fin m) : Forms K c d :=
  ⟨pureRestrict K c m (pderiv (i.natAdd c) f.val),
    pureRestrict_homogeneous K c m (by simpa using f.property.pderiv (i := i.natAdd c))⟩

/-- Trace-weight-one forms reconstruct from their actual derivative coefficients. -/
theorem trace_linear_reconstruct {d : ℕ} (f : Forms K (c + m) (d + 1))
    (hf : f.val.IsWeightedHomogeneous (traceWeight c m) 1) :
    f.val = ∑ i : Fin m, X (i.natAdd c) *
      pureExtend K c m (traceCoefficient K c m d f i).val := by
  have heuler := hf.sum_weight_X_mul_pderiv
  simp only [Fin.sum_univ_add, traceWeight_normal, traceWeight_trace,
    one_nsmul, zero_nsmul, Finset.sum_const_zero, zero_add] at heuler
  rw [← heuler]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply (extend_restrict_of_trace_zero K c m
    (hf.pderiv (i := i.natAdd c) (by simp))).symm

/-- The normal-linear coefficient vector depends linearly on the form. -/
def linearCoefficientMap (d : ℕ) :
    Forms K (c + m) (d + 1) →ₗ[K] (Fin c → Forms K m d) where
  toFun f := linearCoefficient K c m d f
  map_add' f g := by
    funext i
    apply Subtype.ext
    simp [linearCoefficient, map_add]
  map_smul' a f := by
    funext i
    apply Subtype.ext
    simp [linearCoefficient, map_smul]

/-- The trace-linear coefficient vector depends linearly on the form. -/
def traceCoefficientMap (d : ℕ) :
    Forms K (c + m) (d + 1) →ₗ[K] (Fin m → Forms K c d) where
  toFun f := traceCoefficient K c m d f
  map_add' f g := by
    funext i
    apply Subtype.ext
    simp [traceCoefficient, map_add]
  map_smul' a f := by
    funext i
    apply Subtype.ext
    simp [traceCoefficient, map_smul]

end IdealGeneration.NormalDegree
