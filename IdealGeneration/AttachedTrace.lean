module

public import IdealGeneration.ScalarProductTrace
public import IdealGeneration.HyperplaneEulerScalar
public import IdealGeneration.SubspaceInterpolation
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar interpolation at attached projections

The projections of the residual points remain attached to the same points
that define their ideal. The lifting argument below handles that dependence
by correcting each tangential coefficient with a trace polynomial.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

namespace AttachedTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m p : ℕ}

/-- The homogeneous representative of a residual point's trace projection. -/
def projectedPoint (a : PointCoordinates K m p) (i : Fin p) : Fin m → K :=
  fun j => chartPoint K a i j.succ

/-- Evaluation at the attached trace projections, without renormalizing. -/
def projectedEvaluation (a : PointCoordinates K m p) (d : ℕ) :
    Forms K m d →ₗ[K] (Fin p → K) :=
  LinearMap.pi (fun i => evaluationLinear K m d (projectedPoint a i))

@[simp] theorem projectedEvaluation_apply (a : PointCoordinates K m p)
    {d : ℕ} (f : Forms K m d) (i : Fin p) :
    projectedEvaluation a d f i = eval (projectedPoint a i) f.val := rfl

/-- Evaluation of the degree-`d+1` part of the tangential coordinate ideal. -/
def tangentEvaluation (a : PointCoordinates K m p) (d : ℕ) :
    (Fin m → Forms K (m + 1) d) →ₗ[K] (Fin p → K) :=
  (pointEvaluation K a (d + 1)).comp
    (HyperplaneEulerScalar.tangentForm K m d)

@[simp] theorem tangentEvaluation_apply (a : PointCoordinates K m p)
    {d : ℕ} (f : Fin m → Forms K (m + 1) d) (i : Fin p) :
    tangentEvaluation a d f i =
      ∑ j, chartPoint K a i j.succ * eval (chartPoint K a i) (f j).val := by
  simp [tangentEvaluation, HyperplaneEulerScalar.tangentForm]

/-- The scalar trace-product values on the same attached projections. -/
def attachedProductEvaluation (a : PointCoordinates K m p) (d : ℕ) :
    (Fin m → pointPolynomialPiece a d) →ₗ[K] (Fin p → K) :=
  (projectedEvaluation a (d + 1)).comp (tangentPointProductForm a d)

@[simp] theorem attachedProductEvaluation_apply (a : PointCoordinates K m p)
    {d : ℕ} (f : Fin m → pointPolynomialPiece a d) (i : Fin p) :
    attachedProductEvaluation a d f i =
      ∑ j, chartPoint K a i j.succ *
        eval (projectedPoint a i) (hyperplaneRestrict K m (f j).val) := by
  simp [attachedProductEvaluation, projectedEvaluation, tangentPointProductForm,
    tangentPointProduct, projectedPoint]

/-- A residual coefficient with prescribed normal part can be made to vanish
at all residual points by a trace correction. -/
theorem exists_trace_corrected_coefficient (a : PointCoordinates K m p)
    (d : ℕ) (htrace : Function.Surjective (projectedEvaluation a (d + 1)))
    (v : Forms K (m + 1) d) :
    ∃ w : pointPolynomialPiece a (d + 1), ∃ w₀ : Forms K m (d + 1),
      w.val = (extendForm K m (d + 1) w₀).val + X 0 * v.val ∧
      (∀ i, projectedEvaluation a (d + 1) w₀ i =
        -chartPoint K a i 0 * eval (chartPoint K a i) v.val) := by
  obtain ⟨w₀, hw₀⟩ := htrace
    (fun i => -chartPoint K a i 0 * eval (chartPoint K a i) v.val)
  let w := extendForm K m (d + 1) w₀ + normalFormMul K m d v
  have hw : w.val ∈ pointPolynomialPiece a (d + 1) := by
    apply (mem_pointPolynomialPiece_iff a w.val).mpr
    refine ⟨w.property, ?_⟩
    intro i
    have hi := congrFun hw₀ i
    change eval (chartPoint K a i)
      ((extendForm K m (d + 1) w₀).val + X 0 * v.val) = 0
    rw [map_add, map_mul, eval_X, extendForm_val, eval_hyperplaneExtend]
    change projectedEvaluation a (d + 1) w₀ i +
      chartPoint K a i 0 * eval (chartPoint K a i) v.val = 0
    rw [hi]
    ring
  refine ⟨⟨w.val, hw⟩, w₀, rfl, ?_⟩
  intro i
  exact congrFun hw₀ i

/-- The attached rows of the trace-product code are independent. The two
scalar interpolation assumptions concern ordinary trace forms and the
tangential coordinate ideal, respectively. -/
theorem attachedProductEvaluation_surjective (a : PointCoordinates K m p)
    (d : ℕ) (hnormal : ∀ i, chartPoint K a i 0 ≠ 0)
    (htrace : Function.Surjective (projectedEvaluation a (d + 1)))
    (htangent : Function.Surjective (tangentEvaluation a d)) :
    Function.Surjective (attachedProductEvaluation a (d + 1)) := by
  intro z
  obtain ⟨v, hv⟩ := htangent (fun i => -(chartPoint K a i 0)⁻¹ * z i)
  choose w w₀ hw hw₀ using fun j => exists_trace_corrected_coefficient a d htrace (v j)
  refine ⟨w, ?_⟩
  funext i
  rw [attachedProductEvaluation_apply]
  have hwi (j : Fin m) :
      eval (projectedPoint a i) (hyperplaneRestrict K m (w j).val) =
        -chartPoint K a i 0 * eval (chartPoint K a i) (v j).val := by
    rw [hw j]
    simp only [map_add, map_mul, hyperplaneRestrict_X_zero, zero_mul, add_zero,
      extendForm_val, hyperplaneRestrict_extend]
    exact hw₀ j i
  simp_rw [hwi]
  have hsum : (∑ j : Fin m, chartPoint K a i j.succ *
      (-chartPoint K a i 0 * eval (chartPoint K a i) (v j).val)) =
      -chartPoint K a i 0 * tangentEvaluation a d v i := by
    rw [tangentEvaluation_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, congrFun hv i]
  field_simp [hnormal i]

/-- The same conclusion phrased as surjective evaluation on the actual
homogeneous trace-product image `U_A`. -/
theorem traceProductImage_evaluation_surjective (a : PointCoordinates K m p)
    (d : ℕ) (hnormal : ∀ i, chartPoint K a i 0 ≠ 0)
    (htrace : Function.Surjective (projectedEvaluation a (d + 1)))
    (htangent : Function.Surjective (tangentEvaluation a d)) :
    Function.Surjective ((projectedEvaluation a (d + 2)).comp
      (tangentPointProductForm a (d + 1)).range.subtype) := by
  intro z
  obtain ⟨w, hw⟩ := attachedProductEvaluation_surjective a d hnormal htrace htangent z
  exact ⟨⟨tangentPointProductForm a (d + 1) w, ⟨w, rfl⟩⟩, hw⟩

/-- Ordinary scalar interpolation on the projections already supplies
interpolation by the tangential coordinate ideal. -/
theorem tangentEvaluation_surjective_of_projected [CharZero K]
    (a : PointCoordinates K m p) (d : ℕ)
    (htrace : Function.Surjective (projectedEvaluation a (d + 1))) :
    Function.Surjective (tangentEvaluation a d) := by
  intro z
  obtain ⟨f, hf⟩ := htrace z
  obtain ⟨g, hg⟩ := formMultiplication_surjective (K := K) m d f
  refine ⟨fun j => extendForm K m d (g j), ?_⟩
  funext i
  rw [tangentEvaluation_apply]
  simp only [extendForm_val, eval_hyperplaneExtend]
  have hi := congrFun hf i
  rw [← hg] at hi
  simp only [projectedEvaluation_apply, formMultiplication_val, map_sum, map_mul,
    eval_X] at hi
  exact hi

/-- The attached-projection part of Lemma 4.3 follows solely from scalar
postulation of the projected points and nonzero normal coordinates. -/
theorem attachedProductEvaluation_surjective_of_projected [CharZero K]
    (a : PointCoordinates K m p) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i 0 ≠ 0)
    (htrace : Function.Surjective (projectedEvaluation a (d + 1))) :
    Function.Surjective (attachedProductEvaluation a (d + 1)) :=
  attachedProductEvaluation_surjective a d hnormal htrace
    (tangentEvaluation_surjective_of_projected a d htrace)

/-- Evaluation on the trace-product image is onto at all attached labels. -/
theorem traceProductImage_evaluation_surjective_of_projected [CharZero K]
    (a : PointCoordinates K m p) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i 0 ≠ 0)
    (htrace : Function.Surjective (projectedEvaluation a (d + 1))) :
    Function.Surjective ((projectedEvaluation a (d + 2)).comp
      (tangentPointProductForm a (d + 1)).range.subtype) :=
  traceProductImage_evaluation_surjective a d hnormal htrace
    (tangentEvaluation_surjective_of_projected a d htrace)

/-- Independent fixed rows can be completed by general evaluations on a
fixed homogeneous polynomial space. -/
theorem generic_evaluation_completion [Infinite K] {n d r : ℕ}
    (U : Submodule K (Forms K (n + 1) d))
    (E : U →ₗ[K] (Fin r → K)) (q : ℕ)
    (hq : Module.finrank K E.ker ≤ q) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ a : PointCoordinates K n q, eval a P ≠ 0) ∧
      ∀ a, eval a P ≠ 0 →
        Function.Injective (E.prod (subspaceEvaluation U a)) := by
  let V := E.ker.map U.subtype
  let e : E.ker ≃ₗ[K] V :=
    Submodule.equivMapOfInjective U.subtype (Submodule.injective_subtype U) E.ker
  have hd : Module.finrank K V ≤ q := e.finrank_eq.symm.trans_le hq
  obtain ⟨P, hP, hgood⟩ := generic_subspaceEvaluation_injective V q hd
  refine ⟨P, hP, ?_⟩
  intro a ha f g hfg
  have hEfg : E f = E g := congrArg Prod.fst hfg
  have hefg : subspaceEvaluation U a f = subspaceEvaluation U a g :=
    congrArg Prod.snd hfg
  have hker : f + (-1 : K) • g ∈ E.ker := by
    change E (f + (-1 : K) • g) = 0
    rw [map_add, map_smul, hEfg]
    simp
  let v : V := ⟨(f + (-1 : K) • g).val, ⟨f + (-1 : K) • g, hker, rfl⟩⟩
  have hv : subspaceEvaluation V a v = 0 := by
    change pointEvaluation K a d (f.val + (-1 : K) • g.val) = 0
    change pointEvaluation K a d f.val = pointEvaluation K a d g.val at hefg
    rw [map_add, map_smul, hefg]
    simp
  have hvzero : v = 0 := hgood a ha (by simpa using hv)
  have hzero : f.val + (-1 : K) • g.val = 0 :=
    congrArg (fun w : V => w.val) hvzero
  apply Subtype.ext
  apply Subtype.ext
  have hpoly : f.val.val + (-1 : K) • g.val.val = 0 := congrArg Subtype.val hzero
  apply sub_eq_zero.mp
  simpa only [neg_one_smul, sub_eq_add_neg] using hpoly

/-- If the fixed rows are surjective, the number of needed extra rows is
the dimension of the polynomial space minus their number. -/
theorem generic_evaluation_completion_of_surjective [Infinite K] {n d r : ℕ}
    (U : Submodule K (Forms K (n + 1) d))
    (E : U →ₗ[K] (Fin r → K)) (hE : Function.Surjective E)
    (q : ℕ) (hq : Module.finrank K U - r ≤ q) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ a : PointCoordinates K n q, eval a P ≠ 0) ∧
      ∀ a, eval a P ≠ 0 →
        Function.Injective (E.prod (subspaceEvaluation U a)) := by
  apply generic_evaluation_completion U E q
  have hdim : Module.finrank K E.range + Module.finrank K E.ker =
      Module.finrank K U := TwoGroup.rank_nullity_monoid E
  rw [LinearMap.range_eq_top.mpr hE, finrank_top] at hdim
  have hr : Module.finrank K (Fin r → K) = r := by simp
  rw [hr] at hdim
  omega

end AttachedTrace
end IdealGeneration
