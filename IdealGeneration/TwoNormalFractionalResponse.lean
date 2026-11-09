module

public import IdealGeneration.TwoNormalFractionalKernel
public import IdealGeneration.ScalarSelection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# First normal response for a fractional trace

The two source families are actual coefficients of the line substitution on
the ambient Euler kernel. The extended trace contribution is constant, so
each family is determined by one of the two residual normal traces.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice TwoNormalIntegral DifferentialLine
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d p r q k : ℕ}

/-- One component of the genuine first coefficient of a normally moving point. -/
def normalFirstCoefficient (D : ℕ) (y : Fin m → K) (u v : K) (j : Fin (m + 2)) :
    HyperplaneEuler.Relations K (m + 2) D →ₗ[K] K :=
  (Polynomial.lcoeff K 1).comp ((lineForm (commonTracePoint y)
    (twoNormalVelocity u v) D).comp
      ((LinearMap.proj j).comp (HyperplaneEuler.Relations K (m + 2) D).subtype))

/-- The trace extension drops out of the actual response. -/
theorem normalFirstCoefficient_assembled
    (y : Fin m → K) (u v : K)
    (τ : HyperplaneEuler.Relations K m (d + 1 + 1))
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :
    (fun j => normalFirstCoefficient (d + 1 + 1) y u v j (assembledRelation τ w)) =
      Fin.cons (v * eval y (restrictTrace K m w.2.val))
        (Fin.cons (u * eval y (restrictTrace K m
          (-w.2 - tangentProduct K m d w.1).val)) (fun _ => 0)) := by
  funext j
  change normalFirstCoefficient (d + 1 + 1) y u v j
    (extendTraceRelation K m (d + 1 + 1) τ + residualEuler K m d w) = _
  rw [(normalFirstCoefficient (d + 1 + 1) y u v j).map_add]
  have hτ := congrFun (extendTraceRelation_first_coefficient K m τ y u v) j
  change normalFirstCoefficient (d + 1 + 1) y u v j
    (extendTraceRelation K m (d + 1 + 1) τ) = 0 at hτ
  rw [hτ, zero_add]
  exact congrFun (residualEuler_first_coefficient y u v w) j

/-- The special ambient Euler kernel. -/
abbrev AmbientKernel (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K) (D : ℕ) :=
  (ambientEvaluation K m a b x z D).ker

/-- The first source family is the response in the first component to unit t motion. -/
def firstNormalSource
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K) (D : ℕ)
    (i : Fin k) : Module.Dual K (AmbientKernel a b x z D) :=
  (normalFirstCoefficient D (z i) 0 1 0).comp (AmbientKernel a b x z D).subtype

/-- The second source family is the response in the second component to unit s motion. -/
def secondNormalSource
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K) (D : ℕ)
    (i : Fin k) : Module.Dual K (AmbientKernel a b x z D) :=
  (normalFirstCoefficient D (z i) 1 0 (0 : Fin (m + 1)).succ).comp
    (AmbientKernel a b x z D).subtype

/-- The first coefficient on the ambient kernel is supported on the two normal components. -/
theorem normalFirstCoefficient_kernel
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d) (i : Fin k) (u v : K)
    (f : AmbientKernel a b x z (d + 1 + 1)) :
    (fun j => normalFirstCoefficient (d + 1 + 1) (z i) u v j f.val) =
      Fin.cons (v * firstNormalSource a b x z (d + 1 + 1) i f)
        (Fin.cons (u * secondNormalSource a b x z (d + 1 + 1) i f) (fun _ => 0)) := by
  let τ := ambientTraceRelation K m (d + 1 + 1) f.val
  obtain ⟨_, w, hw, _, _⟩ := exists_assembledRelation_of_ambient_eq_zero a b x z hc f.val
    (LinearMap.mem_ker.mp f.property)
  change assembledRelation τ w = f.val at hw
  have h₁ := congrFun (normalFirstCoefficient_assembled (z i) 0 1 τ w) (0 : Fin (m + 2))
  have h₂ := congrFun (normalFirstCoefficient_assembled (z i) 1 0 τ w) (0 : Fin (m + 1)).succ
  rw [hw] at h₁ h₂
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul] at h₁ h₂
  change _ = (Fin.cons (v * normalFirstCoefficient (d + 1 + 1) (z i) 0 1 0 f.val)
    (Fin.cons (u * normalFirstCoefficient (d + 1 + 1) (z i) 1 0
      (0 : Fin (m + 1)).succ f.val) (fun _ => 0)) : Fin (m + 2) → K)
  rw [h₁, h₂]
  simpa only [hw] using normalFirstCoefficient_assembled (z i) u v τ w

/-- Off-slice and enlarged interpolation conditions used by the source detection. -/
structure SourceConditions (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) (q + 1)) (z : Fin k → Fin m → K) (d : ℕ) : Prop where
  attachedX : ∀ i : Fin q, ∃ j : Fin k, commonProjection (chartPoint K x i.castSucc) = z j
  freeTrace : Function.Injective (relationEvaluation (Fin.snoc z
    (commonProjection (chartPoint K x (Fin.last q)))) (d + 1 + 1))
  normalS : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0
  normalT : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0
  scalarA : Function.Injective (pointEvaluation K a d)
  scalarB : Function.Injective (pointEvaluation K b d)
  enlargedA : Function.Injective ((pointEvaluation K a (d + 1)).comp
    (sliceAProduct K m (pointDegreePiece K (attachedOffPoints x) d)))
  enlargedB : Function.Injective ((pointEvaluation K b (d + 1)).comp
    (sliceBProduct K m (pointDegreePiece K (attachedOffPoints x) d)))
  scalarTrace : Function.Injective (scalarEvaluation z (d + 1))

/-- Each of the two genuine first-response source families spans the dual
of the full fractional ambient kernel. -/
theorem normalSources_span
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) (q + 1)) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d) (hs : SourceConditions a b x z d) :
    Submodule.span K (Set.range (firstNormalSource a b x z (d + 1 + 1))) = ⊤ ∧
      Submodule.span K (Set.range (secondNormalSource a b x z (d + 1 + 1))) = ⊤ := by
  let D := d + 1 + 1
  let : AddCommGroup (AmbientKernel a b x z D) := Module.addCommMonoidToAddCommGroup K
  have detect (f : AmbientKernel a b x z D) :
      ((∀ i, firstNormalSource a b x z D i f = 0) → f = 0) ∧
        ((∀ i, secondNormalSource a b x z D i f = 0) → f = 0) := by
    let τ := ambientTraceRelation K m D f.val
    have hf := LinearMap.mem_ker.mp f.property
    obtain ⟨hτ, w, hw, hA, hB⟩ := exists_assembledRelation_of_ambient_eq_zero a b x z hc
      f.val hf
    have hx (i : Fin (q + 1)) (j : Fin (m + 2)) :
        eval (chartPoint K x i) ((assembledRelation τ w).val j).val = 0 := by
      rw [hw]
      exact congrFun (congrFun (congrArg (fun v => v.2.1) hf) i) j
    obtain ⟨h₁, h₂⟩ := assembledRelation_detected_by_each_normal_trace a b x z τ w hτ
      hs.attachedX hs.freeTrace hs.normalS hs.normalT hc.normalA hc.normalB hs.scalarA hs.scalarB
      hs.enlargedA hs.enlargedB hA hB hx
    constructor
    · intro h
      apply Subtype.ext
      rw [← hw]
      apply h₁
      apply hs.scalarTrace
      rw [map_zero]
      funext i
      have hi := congrFun (normalFirstCoefficient_assembled (z i) 0 1 τ w) (0 : Fin (m + 2))
      rw [hw] at hi
      simp only [Fin.cons_zero, one_mul] at hi
      change eval (z i) (restrictTrace K m w.2.val) = 0
      rw [← hi]
      exact h i
    · intro h
      apply Subtype.ext
      rw [← hw]
      apply h₂
      apply hs.scalarTrace
      rw [map_zero]
      funext i
      have hi := congrFun (normalFirstCoefficient_assembled (z i) 1 0 τ w)
        (0 : Fin (m + 1)).succ
      rw [hw] at hi
      simp only [Fin.cons_succ, Fin.cons_zero, one_mul] at hi
      change eval (z i) (restrictTrace K m (-w.2 - tangentProduct K m d w.1).val) = 0
      rw [← hi]
      exact h i
  have hfirst : Function.Injective (LinearMap.pi (firstNormalSource a b x z D)) := by
    intro f g h
    apply sub_eq_zero.mp
    apply (detect (f - g)).1
    intro i
    rw [map_sub, sub_eq_zero]
    exact congrFun h i
  have hsecond : Function.Injective (LinearMap.pi (secondNormalSource a b x z D)) := by
    intro f g h
    apply sub_eq_zero.mp
    apply (detect (f - g)).2
    intro i
    rw [map_sub, sub_eq_zero]
    exact congrFun h i
  let : FiniteDimensional K (AmbientKernel a b x z D) := FiniteDimensional.of_injective _ hfirst
  exact ⟨scalarRows_span_of_injective _ hfirst, scalarRows_span_of_injective _ hsecond⟩

end IdealGeneration.TwoNormalFractional
