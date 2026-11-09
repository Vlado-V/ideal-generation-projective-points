module

public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.DeformationGeneral
public import IdealGeneration.DifferentialLine
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Moving one point away from a hyperplane

The first coordinate is normal to the hyperplane. Fixed conditions are imposed
on actual homogeneous Euler tuples, with an arbitrary linear trace condition.
-/

noncomputable section
namespace IdealGeneration.DifferentialPoint
open MvPolynomial HyperplaneEuler Module
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

local instance relationsGroup {n d : ℕ} : AddCommGroup (Relations K n d) :=
  Module.addCommMonoidToAddCommGroup K

/-- Evaluation of every component of an Euler tuple. -/
def vectorEvaluation {n d : ℕ} (y : Fin n → K) : Relations K n d →ₗ[K] (Fin n → K) where
  toFun f i := eval y (f.val i).val
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

@[simp] theorem vectorEvaluation_apply {n d : ℕ} (y : Fin n → K)
    (f : Relations K n d) (i : Fin n) :
    vectorEvaluation y f i = eval y (f.val i).val := rfl

/-- Fixed full point conditions together with any linear trace conditions. -/
def fixedSpace {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) :
    Submodule K (Relations K (n + 1) (d + 1)) where
  carrier := {f | trace K n (d + 1) f ∈ B ∧
    (∀ i, vectorEvaluation (off i) f = 0) ∧
    (∀ i, vectorEvaluation (on i) f = 0)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨by simpa using B.add_mem hf.1 hg.1,
      fun i => by simp [map_add, hf.2.1 i, hg.2.1 i],
      fun i => by simp [map_add, hf.2.2 i, hg.2.2 i]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨by simpa using B.smul_mem c hf.1,
      fun i => by simp [map_smul, hf.2.1 i],
      fun i => by simp [map_smul, hf.2.2 i]⟩

local instance fixedSpaceGroup {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) : AddCommGroup (fixedSpace off on B) :=
  Module.addCommMonoidToAddCommGroup K

/-- Full evaluation restricted to the fixed-condition space. -/
def fixedEvaluation {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K) :
    fixedSpace off on B →ₗ[K] (Fin (n + 1) → K) :=
  (vectorEvaluation y).comp (fixedSpace off on B).subtype

/-- The allowed tangential values at the point to be moved. -/
def traceImage {n d : ℕ} (B : Submodule K (Relations K n d))
    (y : Fin (n + 1) → K) : Submodule K (Fin n → K) :=
  B.map (vectorEvaluation (fun i => y i.succ))

/-- Evaluation of a restricted tangential component agrees with evaluation on `H`. -/
theorem trace_evaluation {n d : ℕ} (y : Fin (n + 1) → K) (hy : y 0 = 0)
    (f : Relations K (n + 1) d) (i : Fin n) :
    vectorEvaluation (fun j => y j.succ) (trace K n d f) i =
      vectorEvaluation y f i.succ := by
  have heq : Fin.cons 0 (fun j => y j.succ) = y := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hy.symm
    · rfl
  change eval (fun j => y j.succ) (hyperplaneRestrict K n (f.val i.succ).val) = _
  rw [eval_hyperplaneRestrict, heq]
  rfl

/-- A zero value at the moving point forces zero trace when trace evaluation is injective. -/
theorem trace_zero_of_evaluation_zero {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (y : Fin (n + 1) → K) (hy : y 0 = 0)
    (hinj : Function.Injective
      ((vectorEvaluation (fun i => y i.succ)).comp B.subtype))
    (f : fixedSpace off on B) (hf : vectorEvaluation y f.val = 0) :
    trace K n (d + 1) f.val = 0 := by
  have hz : (⟨trace K n (d + 1) f.val, f.property.1⟩ : B) = 0 := by
    apply hinj
    ext i
    change vectorEvaluation (fun j => y j.succ) (trace K n (d + 1) f.val) i = 0
    rw [trace_evaluation y hy]
    exact congrFun hf i.succ
  exact congrArg Subtype.val hz

/-- The actual fixed full conditions on a normal tuple give the first two residual conditions. -/
theorem normal_fixed_residual {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (hoff : ∀ i, off i 0 ≠ 0)
    (g : Fin n → Forms K (n + 1) d)
    (hg : normalInjection K n d g ∈ fixedSpace off on B) :
    (∀ i j, eval (off i) (g j).val = 0) ∧
      (∀ i, eval (on i) (tangentProduct K n d g).val = 0) := by
  constructor
  · intro i j
    have h := congrFun (hg.2.1 i) j.succ
    change eval (off i) (X 0 * (g j).val) = 0 at h
    rw [map_mul, eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left (hoff i)
  · intro i
    have h := congrFun (hg.2.2 i) 0
    change eval (on i) (-(tangentProduct K n d g).val) = 0 at h
    simpa only [map_neg, neg_eq_zero] using h

/-- The residual conditions force the induced first response to be injective.
The tangential first coefficient is the normal velocity times `g(y)`.
-/
theorem response_injective_of_residual {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (y : Fin (n + 1) → K) (hy : y 0 = 0)
    (hoff : ∀ i, off i 0 ≠ 0)
    (hinj : Function.Injective
      ((vectorEvaluation (fun i => y i.succ)).comp B.subtype))
    (c : K) (hc : c ≠ 0)
    (D : fixedSpace off on B →ₗ[K] (Fin (n + 1) → K))
    (hD : ∀ (g : Fin n → Forms K (n + 1) d)
      (hg : normalInjection K n d g ∈ fixedSpace off on B) (i : Fin n),
      D ⟨normalInjection K n d g, hg⟩ i.succ = c * eval y (g i).val)
    (hres : ∀ g : Fin n → Forms K (n + 1) d,
      (∀ i j, eval (off i) (g j).val = 0) →
      (∀ i, eval (on i) (tangentProduct K n d g).val = 0) →
      (fun i => eval y (g i).val) ∈ traceImage B y → g = 0) :
    Function.Injective (DeformationGeneral.response (V := fixedSpace off on B)
      (fixedEvaluation off on B y) D
      ((fixedEvaluation off on B y).range.mkQ)) := by
  let A₀ := fixedEvaluation off on B y
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  have hfeval : vectorEvaluation y f.val.val = 0 := f.property
  have htrace := trace_zero_of_evaluation_zero off on B y hy hinj f.val hfeval
  obtain ⟨g, hg⟩ := exists_normal_of_trace_eq_zero K n d f.val.val htrace
  have hfixed : normalInjection K n d g ∈ fixedSpace off on B := hg.symm ▸ f.val.property
  have hfg : f.val = (⟨normalInjection K n d g, hfixed⟩ : fixedSpace off on B) :=
    Subtype.ext hg.symm
  have hderiv (i : Fin n) : D f.val i.succ = c * eval y (g i).val := by
    rw [hfg]
    exact hD g hfixed i
  have hq : A₀.range.mkQ (D f.val) = 0 := hf
  have hrange : D f.val ∈ A₀.range := (Submodule.Quotient.mk_eq_zero _).mp hq
  obtain ⟨h, hh⟩ := hrange
  have hscaled : c • (fun i => eval y (g i).val) ∈ traceImage B y := by
    refine ⟨trace K n (d + 1) h.val, h.property.1, ?_⟩
    ext i
    change vectorEvaluation (fun j => y j.succ) (trace K n (d + 1) h.val) i =
      c * eval y (g i).val
    rw [trace_evaluation y hy]
    exact (congrFun hh i.succ).trans (hderiv i)
  have hmem : (fun i => eval y (g i).val) ∈ traceImage B y := by
    have ht := (traceImage B y).smul_mem c⁻¹ hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using ht
  have hconditions := normal_fixed_residual off on B hoff g hfixed
  have hgzero := hres g hconditions.1 hconditions.2 hmem
  apply Subtype.ext
  apply Subtype.ext
  simpa only [hgzero, map_zero, Submodule.coe_zero] using hg.symm

section LinearRank
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- An injective first response makes the deformed map injective on a principal open. -/
theorem injective_principal_open_of_response_injective
    (A D : (Fin 1 → K) → (V →ₗ[K] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (hinj : Function.Injective (DeformationGeneral.response
      (A 0) (D 0) (A 0).range.mkQ)) :
    ∃ p : MvPolynomial (Fin 1) K, eval 0 p ≠ 0 ∧
      ∀ a : Fin 1 → K, a 0 ≠ 0 → eval a p ≠ 0 → Function.Injective (A a) := by
  obtain ⟨p, hp, hgood⟩ := DeformationGeneral.rank_gain_principal_open
    A D hA hD hfactor (A 0).range.mkQ (LinearMap.range_mkQ_comp (A 0))
  refine ⟨p, hp, fun a ha hpa => ?_⟩
  have hr := hgood a ha hpa
  rw [LinearMap.finrank_range_of_inj hinj] at hr
  have hzero := (A 0).finrank_range_add_finrank_ker
  have hdim := (A a).finrank_range_add_finrank_ker
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

end LinearRank

/-- The actual polynomial evaluation family along the chosen line. -/
def lineEvaluation {n d : ℕ} (y v : Fin n → K) (t : K) :
    Relations K n d →ₗ[K] (Fin n → K) where
  toFun f i := DifferentialLine.evalLine y v t (f.val i).val
  map_add' f g := by
    ext i
    exact (DifferentialLine.evalLine y v t).map_add _ _
  map_smul' c f := by
    ext i
    exact (DifferentialLine.evalLine y v t).map_smul c _

/-- The first-order quotient of the actual polynomial evaluation family. -/
def lineQuotient {n d : ℕ} (y v : Fin n → K) (t : K) :
    Relations K n d →ₗ[K] (Fin n → K) where
  toFun f i := DifferentialLine.quotientLine y v t (f.val i).val
  map_add' f g := by
    ext i
    exact (DifferentialLine.quotientLine y v t).map_add _ _
  map_smul' c f := by
    ext i
    exact (DifferentialLine.quotientLine y v t).map_smul c _

@[simp] theorem lineEvaluation_apply {n d : ℕ} (y v : Fin n → K) (t : K)
    (f : Relations K n d) (i : Fin n) :
    lineEvaluation y v t f i = eval (fun j => y j + t * v j) (f.val i).val :=
  DifferentialLine.evalLine_apply y v t (f.val i).val

@[simp] theorem lineEvaluation_zero {n d : ℕ} (y v : Fin n → K) :
    (lineEvaluation (d := d) y v 0) = vectorEvaluation y := by
  ext f i
  simp

/-- Exact first-order expansion before any rank argument is applied. -/
theorem lineEvaluation_expansion {n d : ℕ} (y v : Fin n → K) (t : K) :
    (lineEvaluation (d := d) y v t) = lineEvaluation y v 0 + t • lineQuotient y v t := by
  ext f i
  exact LinearMap.congr_fun (DifferentialLine.evalLine_expansion y v t) (f.val i).val

/-- The actual evaluation family is polynomial in its line parameter. -/
theorem lineEvaluation_polynomial {n d : ℕ} (y v : Fin n → K) :
    IsPolynomialFamily (fun a : Fin 1 → K => lineEvaluation (d := d) y v (a 0)) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro i
  exact DeformationMatrix.polynomial_eval_isPolynomialFamily
    (DifferentialLine.lineSubstitution y v (f.val i).val)

/-- Its first-order quotient is also a polynomial family. -/
theorem lineQuotient_polynomial {n d : ℕ} (y v : Fin n → K) :
    IsPolynomialFamily (fun a : Fin 1 → K => lineQuotient (d := d) y v (a 0)) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro i
  exact DeformationMatrix.polynomial_eval_isPolynomialFamily
    (DifferentialLine.lineSubstitution y v (f.val i).val).divX

/-- The normal tuple's tangential first response is exactly normal velocity times `g(y)`. -/
theorem lineQuotient_normal_succ {n d : ℕ} (y v : Fin (n + 1) → K)
    (hy : y 0 = 0) (g : Fin n → Forms K (n + 1) d) (i : Fin n) :
    lineQuotient y v 0 (normalInjection K n d g) i.succ =
      v 0 * eval y (g i).val := by
  change DifferentialLine.quotientLine y v 0 (X 0 * (g i).val) = _
  rw [DifferentialLine.quotientLine_zero]
  exact DifferentialLine.coeff_one_normal_mul y v (g i).val hy

/-- The injective assertion of Lemma 3.4 on a nonempty principal open of the chosen line. -/
theorem moving_point_injective_principal_open {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (y v : Fin (n + 1) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hoff : ∀ i, off i 0 ≠ 0)
    (hinj : Function.Injective
      ((vectorEvaluation (fun i => y i.succ)).comp B.subtype))
    (hres : ∀ g : Fin n → Forms K (n + 1) d,
      (∀ i j, eval (off i) (g j).val = 0) →
      (∀ i, eval (on i) (tangentProduct K n d g).val = 0) →
      (fun i => eval y (g i).val) ∈ traceImage B y → g = 0) :
    ∃ p : MvPolynomial (Fin 1) K, eval 0 p ≠ 0 ∧
      ∀ t : K, t ≠ 0 → eval (fun _ => t) p ≠ 0 →
        Function.Injective (fixedEvaluation off on B (fun i => y i + t * v i)) := by
  let A : (Fin 1 → K) → (fixedSpace off on B →ₗ[K] (Fin (n + 1) → K)) :=
    fun a => (lineEvaluation y v (a 0)).comp (fixedSpace off on B).subtype
  let D : (Fin 1 → K) → (fixedSpace off on B →ₗ[K] (Fin (n + 1) → K)) :=
    fun a => (lineQuotient y v (a 0)).comp (fixedSpace off on B).subtype
  have hA : IsPolynomialFamily A := by
    apply isPolynomialFamily_linearMap
    intro f
    exact (lineEvaluation_polynomial y v).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin (n + 1) → K) f.val)
  have hD : IsPolynomialFamily D := by
    apply isPolynomialFamily_linearMap
    intro f
    exact (lineQuotient_polynomial y v).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin (n + 1) → K) f.val)
  have hfactor : ∀ a, A a = A 0 + a 0 • D a := by
    intro a
    ext f i
    exact congrFun (LinearMap.congr_fun (lineEvaluation_expansion y v (a 0)) f.val) i
  have hzero : A 0 = fixedEvaluation off on B y := by
    dsimp [A, fixedEvaluation]
    rw [lineEvaluation_zero]
  have hresponse : Function.Injective (DeformationGeneral.response
      (A 0) (D 0) (A 0).range.mkQ) := by
    rw [hzero]
    apply response_injective_of_residual off on B y hy hoff hinj (v 0) hv
    · intro g hg i
      exact lineQuotient_normal_succ y v hy g i
    · exact hres
  obtain ⟨p, hp, hgood⟩ := injective_principal_open_of_response_injective A D hA hD hfactor hresponse
  refine ⟨p, hp, fun t ht hpt => ?_⟩
  have h := hgood (fun _ => t) ht hpt
  have heq : A (fun _ => t) = fixedEvaluation off on B (fun i => y i + t * v i) := by
    ext f i
    exact lineEvaluation_apply y v t f.val i
  rwa [heq] at h

/-- Over an infinite field an ordinary point off the hyperplane attains zero kernel. -/
theorem exists_moving_point_injective [Infinite K] {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (y v : Fin (n + 1) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hoff : ∀ i, off i 0 ≠ 0)
    (hinj : Function.Injective
      ((vectorEvaluation (fun i => y i.succ)).comp B.subtype))
    (hres : ∀ g : Fin n → Forms K (n + 1) d,
      (∀ i j, eval (off i) (g j).val = 0) →
      (∀ i, eval (on i) (tangentProduct K n d g).val = 0) →
      (fun i => eval y (g i).val) ∈ traceImage B y → g = 0) :
    ∃ t : K, t ≠ 0 ∧ (y 0 + t * v 0) ≠ 0 ∧
      Function.Injective (fixedEvaluation off on B (fun i => y i + t * v i)) := by
  obtain ⟨p, hp, hgood⟩ := moving_point_injective_principal_open
    off on B y v hy hv hoff hinj hres
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  have hprod : p * X (0 : Fin 1) ≠ 0 := mul_ne_zero hpn (X_ne_zero _)
  have hex : ∃ a : Fin 1 → K, eval a (p * X 0) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  obtain ⟨a, ha⟩ := hex
  have hparts : eval a p ≠ 0 ∧ a 0 ≠ 0 := by simpa using ha
  refine ⟨a 0, hparts.2, by simpa [hy] using mul_ne_zero hparts.2 hv, ?_⟩
  apply hgood (a 0) hparts.2
  have heq : (fun _ : Fin 1 => a 0) = a := by ext i; exact congrArg a (Subsingleton.elim _ _)
  rw [heq]
  exact hparts.1

end IdealGeneration.DifferentialPoint
