module

public import IdealGeneration.FractionalHyperplane
public import IdealGeneration.FractionalScalarCancellation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The outer scalar-cancellation bridge

The lower scalar-reduced map and the two-level parameter map have the same
actual kernel. Their target dimensions agree, so independence transfers as
well as injectivity.
-/

noncomputable section
namespace IdealGeneration.FractionalOuterCancellation
open MvPolynomial Module HyperplaneEuler DifferentialPoint DifferentialFiber
open FractionalHyperplane FractionalCompatibility ScalarTraceReduction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

section KernelTransport
variable {V W Q : Type*} [AddCommMonoid V] [Module K V]
  [AddCommMonoid W] [Module K W] [AddCommMonoid Q] [Module K Q]

/-- Kernel comparison using the additive structures of the given linear maps. -/
theorem injective_iff_of_kernel_eq_monoid (f : V →ₗ[K] W) (g : V →ₗ[K] Q)
    (hker : f.ker = g.ker) : Function.Injective f ↔ Function.Injective g := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup Q := Module.addCommMonoidToAddCommGroup K
  exact FractionalHyperplane.injective_iff_of_kernel_eq f g hker

/-- Independence compares equal kernels with the given condition-space dimensions. -/
theorem surjective_iff_of_kernel_eq_monoid [Module.Finite K V]
    [Module.Finite K W] [Module.Finite K Q]
    (f : V →ₗ[K] W) (g : V →ₗ[K] Q) (hker : f.ker = g.ker)
    (hdim : finrank K W = finrank K Q) : Function.Surjective f ↔ Function.Surjective g := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup Q := Module.addCommMonoidToAddCommGroup K
  exact FractionalHyperplane.surjective_iff_of_kernel_eq f g hker hdim

end KernelTransport

/-- The full tangent partial subspace is an allowed scalar-reduction subspace. -/
theorem partial_le_traceFiber {n : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) :
    L ≤ TraceFiber (Fin.snoc y 1) := by
  intro l hl
  change dot (Fin.snoc y 1) l = 0
  exact hL l hl

/-- The actual outer residual map at a specialized joint configuration. -/
abbrev specializedResidualMap {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z) :=
  FractionalScalarCancellation.residualMap (d := d)
    (fun i => chartPoint K (offCoordinates a) i) (fun i => chartPoint K A i)
    (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L

/-- The lower Euler map obtained by cancelling the scalar quotient. -/
abbrev specializedLowerMap {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) :=
  FractionalScalarCancellation.lowerMap (d := d)
    (fun i => chartPoint K (offCoordinates a) i) (fun i => chartPoint K A i)
    (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
    (partial_le_traceFiber y L hL)

/-- The target of the actual lower scalar-reduced map. -/
abbrev SpecializedLowerTarget {n p q z : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) :=
  (conditionScalarProjection (p := z)
    (FractionalScalarCancellation.allOn (fun i => chartPoint K A i)
      (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i))
    (FractionalScalarCancellation.allAllowed (fun i => chartPoint K A i) L q)
    (FractionalScalarCancellation.allAllowed_le (fun i => chartPoint K A i)
      (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
      (partial_le_traceFiber y L hL))).ker

/-- The two-level map records full point values and the fixed partial trace condition. -/
theorem twoLevelEvaluation_eq_zero_iff {n q z d : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (a : JointCoordinates (K := K) n q z) (f : EulerRelations K (n + 1) d) :
    twoLevelEvaluation y (L.map dropLast) a d f = 0 ↔
      (∀ i, vectorEvaluation (chartPoint K (offCoordinates a) i) f = 0) ∧
      (∀ i, vectorEvaluation (chartPoint K (traceCoordinates a) i)
        (trace K (n + 1) d f) = 0) ∧
      vectorEvaluation (Fin.snoc y 1) (trace K (n + 1) d f) ∈ L := by
  change (eulerTraceEvaluation (offCoordinates a) d f,
      (eulerTraceEvaluation (traceCoordinates a) d (trace K (n + 1) d f),
        (L.map dropLast).mkQ (eulerTraceAt y d (trace K (n + 1) d f)))) = 0 ↔ _
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero, reduced_full_conditions_iff,
    reduced_full_conditions_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← full_partial_iff_reduced y L hL (trace K (n + 1) d f)]

/-- The actual lower map and the two-level parameter map have identical kernels. -/
theorem specializedLowerMap_kernel {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (hoff : ∀ i, offCoordinates a (i, 0) ≠ 0) :
    (specializedLowerMap (d := d) A y L a hL).ker =
      (twoLevelEvaluation y (L.map dropLast) a d).ker := by
  have hoff' (i : Fin z) : chartPoint K (offCoordinates a) i 0 ≠ 0 := by
    simpa only [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
      chartPoint_castSucc] using hoff i
  ext f
  change specializedLowerMap (d := d) A y L a hL f = 0 ↔
    twoLevelEvaluation y (L.map dropLast) a d f = 0
  have hc : specializedLowerMap (d := d) A y L a hL f = 0 ↔
      (∀ i, vectorEvaluation (chartPoint K (offCoordinates a) i) f = 0) ∧
      (∀ i, vectorEvaluation (chartPoint K (traceCoordinates a) i)
        (trace K (n + 1) d f) = 0) ∧
      vectorEvaluation (Fin.snoc y 1) (trace K (n + 1) d f) ∈ L :=
    FractionalScalarCancellation.lowerMap_eq_zero_iff_trace
      (fun i => chartPoint K (offCoordinates a) i) (fun i => chartPoint K A i)
      (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
      (partial_le_traceFiber y L hL) hoff' f
  exact hc.trans (twoLevelEvaluation_eq_zero_iff y L hL a f).symm

/-- The target dimensions match after discarding the normalized last tangent coordinate. -/
theorem specializedLowerTarget_finrank_eq {n p q z : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) :
    finrank K (SpecializedLowerTarget A y L a hL) =
      finrank K ((Fin z → Fin (n + 1) → K) ×
        ((Fin q → Fin n → K) × ((Fin n → K) ⧸ L.map dropLast))) := by
  have hlower : finrank K (SpecializedLowerTarget A y L a hL) =
      z * (n + 1) + q * n + (n - finrank K L) :=
    FractionalScalarCancellation.lowerTarget_finrank (fun i => chartPoint K A i)
      (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
      (partial_le_traceFiber y L hL) (fun i => by simp) (by simp) (fun i => by simp)
  rw [hlower]
  have hdrop := finrank_drop_tangent_subspace (Fin.snoc y 1) (by simp) L hL
  simp [Module.finrank_pi_fintype, valueQuotient_finrank, hdrop, Nat.add_assoc]

/-- The scalar completion from the joint configuration is exactly the required scalar isomorphism. -/
theorem specialized_scalar_bijective {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (a : JointCoordinates (K := K) n q z)
    (hscalar : Function.Bijective (pointEvaluation K
      (appendCoordinates (FractionalTraceChoice.adjoinPoint A y) (traceCoordinates a)) (d + 1))) :
    Function.Bijective (traceScalarEvaluation (d := d)
      (FractionalScalarCancellation.allOn (fun i => chartPoint K A i)
        (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i))) := by
  rw [FractionalScalarCancellation.traceScalarEvaluation_allOn_chart_eq]
  exact hscalar

/-- Low two-level injectivity gives the actual specialized outer residual injection. -/
theorem specialized_residual_injective {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (hoff : ∀ i, offCoordinates a (i, 0) ≠ 0)
    (hscalar : Function.Bijective (pointEvaluation K
      (appendCoordinates (FractionalTraceChoice.adjoinPoint A y) (traceCoordinates a)) (d + 1)))
    (hlo : Function.Injective (twoLevelEvaluation y (L.map dropLast) a d)) :
    Function.Injective (specializedResidualMap (d := d) A y L a) := by
  have hlower : Function.Injective (specializedLowerMap (d := d) A y L a hL) :=
    (injective_iff_of_kernel_eq_monoid (specializedLowerMap (d := d) A y L a hL)
      (twoLevelEvaluation y (L.map dropLast) a d)
      (specializedLowerMap_kernel A y L a hL hoff)).mpr hlo
  exact (FractionalScalarCancellation.cancellation_injective_iff
    (fun i => chartPoint K (offCoordinates a) i) (fun i => chartPoint K A i)
    (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
    (partial_le_traceFiber y L hL) (specialized_scalar_bijective A y a hscalar).1).mpr hlower

/-- Low two-level independence gives the actual specialized outer residual independence. -/
theorem specialized_residual_surjective [CharZero K] {n p q z d : ℕ}
    (A : PointCoordinates K n p) (y : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z)
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (hoff : ∀ i, offCoordinates a (i, 0) ≠ 0)
    (hscalar : Function.Bijective (pointEvaluation K
      (appendCoordinates (FractionalTraceChoice.adjoinPoint A y) (traceCoordinates a)) (d + 1)))
    (hlo : Function.Surjective (twoLevelEvaluation y (L.map dropLast) a d)) :
    Function.Surjective (specializedResidualMap (d := d) A y L a) := by
  have hlower : Function.Surjective (specializedLowerMap (d := d) A y L a hL) :=
    (surjective_iff_of_kernel_eq_monoid (specializedLowerMap (d := d) A y L a hL)
      (twoLevelEvaluation y (L.map dropLast) a d)
      (specializedLowerMap_kernel A y L a hL hoff)
      (specializedLowerTarget_finrank_eq A y L a hL)).mpr hlo
  exact (FractionalScalarCancellation.cancellation_surjective_iff
    (fun i => chartPoint K (offCoordinates a) i) (fun i => chartPoint K A i)
    (Fin.snoc y 1) (fun i => chartPoint K (traceCoordinates a) i) L
    (partial_le_traceFiber y L hL) (specialized_scalar_bijective A y a hscalar)).mpr hlower

end IdealGeneration.FractionalOuterCancellation
