module

public import IdealGeneration.TwoNormalResponse
public import IdealGeneration.TwoNormalSlice

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Extension of the trace kernel for a fractional trace

The two normal coordinates are prepended to the common trace. Extending an
Euler relation from the trace is polynomially constant along both normal
motions. On a slice, subtracting this extension removes the full kernel under
the lower-degree scalar and multiplication hypotheses.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoNormalTrace TwoNormalSlice DifferentialLine
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ)

/-- Extend a trace Euler relation with both normal components zero. -/
def extendTraceRelation (D : ℕ) :
    HyperplaneEuler.Relations K m D →ₗ[K] HyperplaneEuler.Relations K (m + 2) D :=
  (HyperplaneEuler.extend K (m + 1) D).comp (HyperplaneEuler.extend K m D)

/-- Evaluation of a one-normal extension depends only on the projected point. -/
theorem eval_extendRelation {D : ℕ} (τ : HyperplaneEuler.Relations K m D)
    (x : Fin (m + 1) → K) :
    (fun j => eval x (((HyperplaneEuler.extend K m D) τ).val j).val) =
      Fin.cons 0 (fun i => eval (fun j => x j.succ) (τ.val i).val) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · change eval x (0 : Poly K (m + 1)) = 0
    exact map_zero _
  · exact eval_hyperplaneExtend K m (τ.val i).val x

/-- Evaluation of a two-normal extension depends only on its common projection. -/
theorem eval_extendTraceRelation {D : ℕ} (τ : HyperplaneEuler.Relations K m D)
    (x : Fin (m + 2) → K) :
    (fun j => eval x ((extendTraceRelation K m D τ).val j).val) =
      Fin.cons 0 (Fin.cons 0 (fun i => eval (fun j => x j.succ.succ) (τ.val i).val)) := by
  change (fun j => eval x ((HyperplaneEuler.extend K (m + 1) D
    (HyperplaneEuler.extend K m D τ)).val j).val) = _
  rw [eval_extendRelation K (m + 1), eval_extendRelation K m]

private theorem lineSubstitution_extendTrace (y v : Fin (m + 2) → K)
    (hv : ∀ i : Fin m, v i.succ.succ = 0) (f : Poly K m) :
    lineSubstitution y v (hyperplaneExtend K (m + 1) (hyperplaneExtend K m f)) =
      Polynomial.C (eval (fun j => y j.succ.succ) f) := by
  have h : (lineSubstitution y v).toRingHom.comp ((hyperplaneExtend K (m + 1)).toRingHom.comp
      (hyperplaneExtend K m).toRingHom) = Polynomial.C.comp (eval (fun j => y j.succ.succ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      change lineSubstitution y v (hyperplaneExtend K (m + 1) (hyperplaneExtend K m (X i))) =
        Polynomial.C (eval (fun j => y j.succ.succ) (X i))
      simp [hv i]
  exact congrArg (fun F : Poly K m →+* Polynomial K => F f) h

/-- Extending a trace kernel gives zero first response to a normal motion. -/
theorem extendTraceRelation_first_coefficient {D : ℕ}
    (τ : HyperplaneEuler.Relations K m D) (y : Fin m → K) (u v : K) :
    (fun j => (lineSubstitution (TwoNormalIntegral.commonTracePoint y)
      (TwoNormalIntegral.twoNormalVelocity (m := m) u v)
      ((extendTraceRelation K m D τ).val j).val).coeff 1) = 0 := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change (lineSubstitution (TwoNormalIntegral.commonTracePoint y)
      (TwoNormalIntegral.twoNormalVelocity (m := m) u v) (0 : Poly K (m + 2))).coeff 1 = 0
    simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · change (lineSubstitution (TwoNormalIntegral.commonTracePoint y)
        (TwoNormalIntegral.twoNormalVelocity (m := m) u v)
        (hyperplaneExtend K (m + 1) (0 : Poly K (m + 1)))).coeff 1 = 0
      simp
    · change (lineSubstitution (TwoNormalIntegral.commonTracePoint y)
        (TwoNormalIntegral.twoNormalVelocity (m := m) u v)
        (hyperplaneExtend K (m + 1) (hyperplaneExtend K m (τ.val i).val))).coeff 1 = 0
      rw [lineSubstitution_extendTrace K m _ _ (fun _ => rfl)]
      simp

variable {K m} {p q : ℕ}

/-- A vanishing slice section restricts to the genuine trace kernel. -/
theorem trace_vanishing_of_slice_vanishing
    (a : PointCoordinates K m p) (z : Fin q → Fin m → K) {D : ℕ}
    (F : HyperplaneEuler.Relations K (m + 1) D)
    (hF : sliceEvaluation a z D F = 0) :
    relationEvaluation z D (HyperplaneEuler.trace K m D F) = 0 := by
  funext i j
  have hZ : relationEvaluation (fun i => Fin.cons 0 (z i)) D F = 0 := congrArg Prod.snd hF
  have hj := congrFun (congrFun hZ i) j.succ
  change eval (z i) (hyperplaneRestrict K m (F.val j.succ).val) = 0
  rw [eval_hyperplaneRestrict]
  exact hj

/-- The only zero-trace slice kernel comes from zero lower-degree coefficients. -/
theorem slice_eq_zero_of_trace_eq_zero
    (a : PointCoordinates K m p) (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (hscalar : Function.Injective ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype))
    (F : HyperplaneEuler.Relations K (m + 1) (d + 1))
    (hF : sliceEvaluation a z (d + 1) F = 0)
    (hT : HyperplaneEuler.trace K m (d + 1) F = 0) : F = 0 := by
  obtain ⟨g, hg⟩ := HyperplaneEuler.exists_normal_of_trace_eq_zero K m d F hT
  have hA : relationEvaluation (fun i => chartPoint K a i) (d + 1)
      (HyperplaneEuler.normalInjection K m d g) = 0 := by
    rw [hg]
    exact congrArg Prod.fst hF
  have hZ : relationEvaluation (fun i => Fin.cons 0 (z i)) (d + 1)
      (HyperplaneEuler.normalInjection K m d g) = 0 := by
    rw [hg]
    exact congrArg Prod.snd hF
  have hgi (j : Fin m) : g j ∈ pointDegreePiece K a d := by
    rw [mem_pointDegreePiece]
    intro i
    have hj := congrFun (congrFun hA i) j.succ
    change eval (chartPoint K a i) (X 0 * (g j).val) = 0 at hj
    rw [map_mul, eval_X] at hj
    exact (mul_eq_zero.mp hj).resolve_left (hnormal i)
  let w : Fin m → pointPolynomialPiece a d :=
    fun j => pointPolynomialPieceEquiv a d ⟨g j, hgi j⟩
  let u : (tangentPointProductForm a d).range :=
    ⟨tangentPointProductForm a d w, ⟨w, rfl⟩⟩
  have huEval : ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype) u = 0 := by
    funext i
    have hi := congrFun (congrFun hZ i) 0
    change eval (Fin.cons 0 (z i)) (-(HyperplaneEuler.tangentProduct K m d g).val) = 0 at hi
    rw [map_neg, neg_eq_zero] at hi
    change eval (z i) (tangentPointProduct a d w) = 0
    have heq : eval (z i) (tangentPointProduct a d w) =
        eval (Fin.cons 0 (z i)) (HyperplaneEuler.tangentProduct K m d g).val := by
      simp [tangentPointProduct, HyperplaneEuler.tangentProduct,
        eval_hyperplaneRestrict, w]
    exact heq.trans hi
  have hu : u = 0 := hscalar (by simpa using huEval)
  have huw : tangentPointProductForm a d w = 0 := congrArg Subtype.val hu
  have hw : w = 0 := tangentPointProductForm_injective a hnormal hmul (by simpa using huw)
  have hgzero : g = 0 := by
    funext j
    apply Subtype.ext
    have hj := congrArg (fun v : Fin m → pointPolynomialPiece a d => (v j).val) hw
    simpa [w] using hj
  rw [← hg, hgzero, map_zero]

/-- If a slice point projects to the trace configuration, a trace kernel
extension vanishes there as well as at the common trace itself. -/
theorem extendRelation_slice_vanishing
    (a : PointCoordinates K m p) (z : Fin q → Fin m → K) {D : ℕ}
    (hattach : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (τ : HyperplaneEuler.Relations K m D) (hτ : relationEvaluation z D τ = 0) :
    sliceEvaluation a z D (HyperplaneEuler.extend K m D τ) = 0 := by
  apply Prod.ext
  · funext i
    obtain ⟨k, hk⟩ := hattach i
    change (fun j => eval (chartPoint K a i) ((HyperplaneEuler.extend K m D τ).val j).val) = 0
    rw [eval_extendRelation K m, hk]
    have hz := congrFun hτ k
    change (fun j => eval (z k) (τ.val j).val) = 0 at hz
    rw [hz]
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  · funext i
    change (fun j => eval (Fin.cons 0 (z i)) ((HyperplaneEuler.extend K m D τ).val j).val) = 0
    rw [eval_extendRelation K m]
    have hz := congrFun hτ i
    change (fun j => eval (z i) (τ.val j).val) = 0 at hz
    simp only [Fin.cons_succ, hz]
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

/-- The full slice kernel is exactly the extended trace kernel, including the
case of nonzero trace kernel used in Proposition 5.1. -/
theorem slice_eq_extend_of_vanishing
    (a : PointCoordinates K m p) (z : Fin q → Fin m → K) (d : ℕ)
    (hattach : ∀ i : Fin p, ∃ j : Fin q, (fun k => chartPoint K a i k.succ) = z j)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (hscalar : Function.Injective ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype))
    (F : HyperplaneEuler.Relations K (m + 1) (d + 1))
    (hF : sliceEvaluation a z (d + 1) F = 0) :
    F = HyperplaneEuler.extend K m (d + 1) (HyperplaneEuler.trace K m (d + 1) F) := by
  let τ := HyperplaneEuler.trace K m (d + 1) F
  have hτ : relationEvaluation z (d + 1) τ = 0 := trace_vanishing_of_slice_vanishing a z F hF
  have hE := extendRelation_slice_vanishing a z hattach τ hτ
  apply sub_eq_zero.mp
  apply slice_eq_zero_of_trace_eq_zero a z d hnormal hmul hscalar
  · rw [map_sub, hF, hE, sub_self]
  · rw [map_sub, HyperplaneEuler.trace_extend, sub_self]

end IdealGeneration.TwoNormalFractional
