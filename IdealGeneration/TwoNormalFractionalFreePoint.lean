module

public import IdealGeneration.TwoNormalFractionalTrace
public import IdealGeneration.TwoNormalFractionalSource
public import IdealGeneration.PointMonotonicity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The free projection detects a fractional trace kernel

The last off-slice point is the free point. Vanishing at the attached off-slice
points puts the lower-degree coefficients in the ideal obtained by deleting
that last point. Once either normal trace is zero, the enlarged slice
interpolation kills the residual coefficients. The free point then detects
the remaining trace Euler relation.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d p r q k : ℕ}

/-- The retained off-slice group, with the free last point removed. -/
abbrev attachedOffPoints (x : PointCoordinates K (m + 1) (q + 1)) :
    PointCoordinates K (m + 1) q := restrictPoints x Fin.castSucc

/-- The common projection of an ambient representative. -/
def commonProjection (x : Fin (m + 2) → K) : Fin m → K := fun j => x j.succ.succ

/-- A trace kernel extension vanishes at any point with an attached projection. -/
theorem extendTraceRelation_vanishes_at_attached
    (z : Fin k → Fin m → K) (τ : HyperplaneEuler.Relations K m d)
    (hτ : relationEvaluation z d τ = 0) (x : Fin (m + 2) → K)
    (hattach : ∃ i : Fin k, commonProjection x = z i) :
    ∀ j, eval x ((extendTraceRelation K m d τ).val j).val = 0 := by
  obtain ⟨i, hi⟩ := hattach
  have he := eval_extendTraceRelation K m τ x
  change (fun j => eval x ((extendTraceRelation K m d τ).val j).val) =
    Fin.cons 0 (Fin.cons 0 (fun j => eval (commonProjection x) (τ.val j).val)) at he
  have hzi := congrFun hτ i
  change (fun j => eval (z i) (τ.val j).val) = 0 at hzi
  rw [hi, hzi] at he
  intro j
  rw [congrFun he j]
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

/-- The free projection kills an extended trace kernel when the augmented trace
evaluation is injective. -/
theorem trace_eq_zero_of_free_projection
    (z : Fin k → Fin m → K) (τ : HyperplaneEuler.Relations K m d)
    (hτ : relationEvaluation z d τ = 0) (x : Fin (m + 2) → K)
    (hfree : Function.Injective (relationEvaluation (Fin.snoc z (commonProjection x)) d))
    (hx : ∀ j, eval x ((extendTraceRelation K m d τ).val j).val = 0) : τ = 0 := by
  have hfreeValues (j : Fin m) : eval (commonProjection x) (τ.val j).val = 0 := by
    have he := congrFun (eval_extendTraceRelation K m τ x) j.succ.succ
    exact he.symm.trans (hx j.succ.succ)
  have hall : relationEvaluation (Fin.snoc z (commonProjection x)) d τ = 0 := by
    funext i j
    refine Fin.lastCases ?_ (fun t => ?_) i
    · change eval ((Fin.snoc z (commonProjection x) : Fin (k + 1) → Fin m → K)
        (Fin.last k)) (τ.val j).val = 0
      rw [Fin.snoc_last]
      exact hfreeValues j
    · change eval ((Fin.snoc z (commonProjection x) : Fin (k + 1) → Fin m → K)
        t.castSucc) (τ.val j).val = 0
      rw [Fin.snoc_castSucc]
      exact congrFun (congrFun hτ t) j
  exact hfree (by simpa using hall)

/-- The actual sum of a trace extension and a two-normal residual section. -/
def assembledRelation (τ : HyperplaneEuler.Relations K m (d + 1 + 1))
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :
    HyperplaneEuler.Relations K (m + 2) (d + 1 + 1) :=
  extendTraceRelation K m (d + 1 + 1) τ + residualEuler K m d w

/-- On the attached off-slice group, the tangential and first normal
coefficients belong to the enlarged residual point ideals. -/
theorem assembledRelation_coefficients_in_attached_ideal
    (z : Fin k → Fin m → K)
    (x : PointCoordinates K (m + 1) (q + 1))
    (τ : HyperplaneEuler.Relations K m (d + 1 + 1))
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1))
    (hτ : relationEvaluation z (d + 1 + 1) τ = 0)
    (hattach : ∀ i : Fin q, ∃ j : Fin k,
      commonProjection (chartPoint K x i.castSucc) = z j)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hx : ∀ i j, eval (chartPoint K x i) ((assembledRelation τ w).val j).val = 0) :
    (∀ j, w.1 j ∈ pointDegreePiece K (attachedOffPoints x) d) ∧
      w.2 ∈ pointDegreePiece K (attachedOffPoints x) (d + 1) := by
  have hres (i : Fin q) (j : Fin (m + 2)) : eval (chartPoint K x i.castSucc)
      ((residualEuler K m d w).val j).val = 0 := by
    have he := extendTraceRelation_vanishes_at_attached z τ hτ
      (chartPoint K x i.castSucc) (hattach i) j
    have hv := hx i.castSucc j
    change eval (chartPoint K x i.castSucc)
      (((extendTraceRelation K m (d + 1 + 1) τ).val j).val +
       ((residualEuler K m d w).val j).val) = 0 at hv
    rw [map_add, he, zero_add] at hv
    exact hv
  constructor
  · intro j
    apply (mem_pointDegreePiece (attachedOffPoints x) (w.1 j)).mpr
    intro i
    have hi := hres i j.succ.succ
    change eval (chartPoint K x i.castSucc)
      (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val)) = 0 at hi
    simp only [map_mul, eval_X] at hi
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (hs i.castSucc))).resolve_left
      (ht i.castSucc)
  · apply (mem_pointDegreePiece (attachedOffPoints x) w.2).mpr
    intro i
    have hi := hres i 0
    change eval (chartPoint K x i.castSucc) (X (0 : Fin (m + 1)).succ * w.2.val) = 0 at hi
    simp only [map_mul, eval_X] at hi
    exact (mul_eq_zero.mp hi).resolve_left (ht i.castSucc)

/-- Equation (5.10) on the actual normal form. Both scalar normal traces
separately detect the section. The evaluation hypotheses are only those on
lower-degree forms and on the enlarged slice product spaces. -/
theorem assembledRelation_detected_by_each_normal_trace
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) (q + 1)) (z : Fin k → Fin m → K)
    (τ : HyperplaneEuler.Relations K m (d + 1 + 1))
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1))
    (hτ : relationEvaluation z (d + 1 + 1) τ = 0)
    (hattach : ∀ i : Fin q, ∃ j : Fin k,
      commonProjection (chartPoint K x i.castSucc) = z j)
    (hfree : Function.Injective (relationEvaluation (Fin.snoc z
      (commonProjection (chartPoint K x (Fin.last q)))) (d + 1 + 1)))
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (haEval : Function.Injective (pointEvaluation K a d))
    (hbEval : Function.Injective (pointEvaluation K b d))
    (hlargeA : Function.Injective ((pointEvaluation K a (d + 1)).comp
      (sliceAProduct K m (pointDegreePiece K (attachedOffPoints x) d))))
    (hlargeB : Function.Injective ((pointEvaluation K b (d + 1)).comp
      (sliceBProduct K m (pointDegreePiece K (attachedOffPoints x) d))))
    (hA : pointEvaluation K a (d + 1) (restrictAForm K m (d + 1)
      (w.2 + tangentProduct K m d w.1)) = 0)
    (hB : pointEvaluation K b (d + 1) (restrictForm K (m + 1) (d + 1) w.2) = 0)
    (hx : ∀ i j, eval (chartPoint K x i) ((assembledRelation τ w).val j).val = 0) :
    (restrictTraceForm K m (d + 1) w.2 = 0 → assembledRelation τ w = 0) ∧
      (restrictTraceForm K m (d + 1) (-w.2 - tangentProduct K m d w.1) = 0 →
        assembledRelation τ w = 0) := by
  obtain ⟨hcoeff, hh⟩ := assembledRelation_coefficients_in_attached_ideal
    z x τ w hτ hattach hs ht hx
  have finish (hw : w = 0) : assembledRelation τ w = 0 := by
    have hext : assembledRelation τ w = extendTraceRelation K m (d + 1 + 1) τ := by
      simp [assembledRelation, hw]
    have hτ0 : τ = 0 := trace_eq_zero_of_free_projection z τ hτ
      (chartPoint K x (Fin.last q)) hfree (by simpa only [hext] using hx (Fin.last q))
    rw [hext, hτ0, map_zero]
  constructor
  · intro hz
    apply finish
    exact residual_eq_zero_of_first_normal_trace a b (attachedOffPoints x) w
      (fun i => hs i.castSucc) hb hbEval hcoeff hh hA hB hlargeA hz
  · intro hz
    apply finish
    exact residual_eq_zero_of_second_normal_trace a b (attachedOffPoints x) w
      (fun i => ht i.castSucc) ha haEval hcoeff hh hA hB hlargeB hz

end IdealGeneration.TwoNormalFractional
