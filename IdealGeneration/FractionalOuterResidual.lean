module

public import IdealGeneration.FractionalOuterCancellation
public import IdealGeneration.HyperplanePoints

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Regrouping the outer residual values

The full residual points consist of the joint off-hyperplane points followed
by the specialized trace points. The scalar and partial conditions stay fixed.
-/

noncomputable section
namespace IdealGeneration.FractionalOuterResidual
open MvPolynomial Module HyperplaneEuler DifferentialPoint DifferentialFiber
open FractionalCompatibility FractionalHyperplane FractionalOuterCancellation ScalarTraceReduction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

/-- The specialized full residual configuration includes all the trace points. -/
def specializedFullConfiguration {n q z : ℕ} (a : JointCoordinates (K := K) n q z) :
    PointCoordinates K (n + 1) (z + q) :=
  hyperplaneConfiguration (offCoordinates a) (traceCoordinates a)

/-- The fixed partial image in the top trace problem. -/
abbrev topTraceImage {n d : ℕ} (y : Fin n → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) :=
  traceImage B (Fin.cons 0 (Fin.snoc y 1))

/-- The direct residual map used by the final moving-point lemma. -/
abbrev directResidualMap {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) :=
  residualConditions (d := d) (fun i => chartPoint K (specializedFullConfiguration a) i)
    (fun i => Fin.cons 0 (chartPoint K A i)) B (Fin.cons 0 (Fin.snoc y 1))

/-- The direct residual condition-space type. -/
abbrev DirectResidualTarget (n p q z : ℕ) (L : Submodule K (Fin (n + 1) → K)) :=
  ((Fin (z + q) → Fin (n + 1) → K) × (Fin p → K)) × ((Fin (n + 1) → K) ⧸ L)

/-- The trace image is tangent at the partial point. -/
theorem topTraceImage_tangent {n d : ℕ} (y : Fin n → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) :
    ∀ l ∈ topTraceImage y B, dot (Fin.snoc y 1) l = 0 := by
  intro l hl
  exact traceImage_dot_eq_zero B (Fin.cons 0 (Fin.snoc y 1)) l hl

/-- Full residual values split into the original off points and the specialized trace points. -/
theorem fullValues_specialized_iff {n q z d : ℕ}
    (a : JointCoordinates (K := K) n q z) (g : Fin (n + 1) → Forms K (n + 2) d) :
    (∀ i, tangentEvaluation (chartPoint K (specializedFullConfiguration a) i) g = 0) ↔
      (∀ i, tangentEvaluation (chartPoint K (offCoordinates a) i) g = 0) ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (chartPoint K (traceCoordinates a) i)) g = 0) := by
  rw [Fin.forall_fin_add]
  simp only [specializedFullConfiguration, chartPoint_hyperplaneConfiguration_left,
    chartPoint_hyperplaneConfiguration_right]

/-- The direct residual map is tested by its actual full, scalar, and partial values. -/
theorem directResidualMap_eq_zero_iff {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) (g : Fin (n + 1) → Forms K (n + 2) d) :
    directResidualMap A y B a g = 0 ↔
      (∀ i, tangentEvaluation (chartPoint K (specializedFullConfiguration a) i) g = 0) ∧
      (∀ i, eval (Fin.cons 0 (chartPoint K A i)) (tangentProduct K (n + 1) d g).val = 0) ∧
      tangentEvaluation (Fin.cons 0 (Fin.snoc y 1)) g ∈ topTraceImage y B := by
  change (((fun i => tangentEvaluation (chartPoint K (specializedFullConfiguration a) i) g),
      (fun i => eval (Fin.cons 0 (chartPoint K A i)) (tangentProduct K (n + 1) d g).val)),
      (topTraceImage y B).mkQ (tangentEvaluation (Fin.cons 0 (Fin.snoc y 1)) g)) = 0 ↔ _
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero]
  simp only [funext_iff, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  tauto

/-- The scalar-cancellation residual and the direct residual have the same genuine kernel. -/
theorem specializedResidualMap_kernel {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) :
    (specializedResidualMap (d := d) A y (topTraceImage y B) a).ker =
      (directResidualMap (d := d) A y B a).ker := by
  ext g
  change specializedResidualMap (d := d) A y (topTraceImage y B) a g = 0 ↔
    directResidualMap A y B a g = 0
  rw [FractionalScalarCancellation.residualMap_eq_zero_iff,
    directResidualMap_eq_zero_iff, fullValues_specialized_iff]
  tauto

/-- Both descriptions of the residual target have the same dimension. -/
theorem specializedResidualTarget_finrank_eq {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) :
    finrank K (ConditionSpace (p := z)
      (FractionalScalarCancellation.allAllowed (fun i => chartPoint K A i) (topTraceImage y B) q)) =
      finrank K (DirectResidualTarget n p q z (topTraceImage y B)) := by
  have hdim := FractionalScalarCancellation.residualTarget_finrank (z := z)
    (fun i => chartPoint K A i) (Fin.snoc y 1)
    (fun i => chartPoint K (traceCoordinates a) i) (topTraceImage y B)
    (partial_le_traceFiber y _ (topTraceImage_tangent y B))
    (fun i => by simp) (by simp) (fun i => by simp)
  rw [hdim]
  simp [DirectResidualTarget, Module.finrank_pi_fintype, valueQuotient_finrank, Nat.add_assoc]

/-- Injection is unchanged by regrouping the full residual values. -/
theorem specialized_residual_injective_iff_direct {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) :
    Function.Injective (specializedResidualMap (d := d) A y (topTraceImage y B) a) ↔
      Function.Injective (directResidualMap (d := d) A y B a) := by
  exact injective_iff_of_kernel_eq_monoid
    (specializedResidualMap (d := d) A y (topTraceImage y B) a) (directResidualMap A y B a)
    (specializedResidualMap_kernel A y B a)

/-- Independence is unchanged because the two residual targets have equal dimension. -/
theorem specialized_residual_surjective_iff_direct {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z) :
    Function.Surjective (specializedResidualMap (d := d) A y (topTraceImage y B) a) ↔
      Function.Surjective (directResidualMap (d := d) A y B a) := by
  exact surjective_iff_of_kernel_eq_monoid
    (specializedResidualMap (d := d) A y (topTraceImage y B) a) (directResidualMap A y B a)
    (specializedResidualMap_kernel A y B a) (specializedResidualTarget_finrank_eq A y B a)

/-- The lower two-level injective witness yields the direct residual witness for the outer move. -/
theorem twoLevel_injective_to_direct {n p q z d : ℕ} (A : PointCoordinates K n p)
    (y : Fin n → K) (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z)
    (hoff : ∀ i, offCoordinates a (i, 0) ≠ 0)
    (hscalar : Function.Bijective (pointEvaluation K
      (appendCoordinates (FractionalTraceChoice.adjoinPoint A y) (traceCoordinates a)) (d + 1)))
    (hlo : Function.Injective (twoLevelEvaluation y ((topTraceImage y B).map dropLast) a d)) :
    Function.Injective (directResidualMap (d := d) A y B a) := by
  apply (specialized_residual_injective_iff_direct A y B a).mp
  exact FractionalOuterCancellation.specialized_residual_injective A y (topTraceImage y B) a
    (topTraceImage_tangent y B) hoff hscalar hlo

/-- The lower independent witness yields the direct residual independence for the outer move. -/
theorem twoLevel_surjective_to_direct [CharZero K] {n p q z d : ℕ}
    (A : PointCoordinates K n p) (y : Fin n → K)
    (B : Submodule K (Relations K (n + 1) (d + 1)))
    (a : JointCoordinates (K := K) n q z)
    (hoff : ∀ i, offCoordinates a (i, 0) ≠ 0)
    (hscalar : Function.Bijective (pointEvaluation K
      (appendCoordinates (FractionalTraceChoice.adjoinPoint A y) (traceCoordinates a)) (d + 1)))
    (hlo : Function.Surjective (twoLevelEvaluation y ((topTraceImage y B).map dropLast) a d)) :
    Function.Surjective (directResidualMap (d := d) A y B a) := by
  apply (specialized_residual_surjective_iff_direct A y B a).mp
  exact FractionalOuterCancellation.specialized_residual_surjective A y (topTraceImage y B) a
    (topTraceImage_tangent y B) hoff hscalar hlo

end IdealGeneration.FractionalOuterResidual
