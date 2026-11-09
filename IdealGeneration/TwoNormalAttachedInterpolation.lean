module

public import IdealGeneration.TwoNormalAttachedCode
public import IdealGeneration.AttachedTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Uniform interpolation for the actual slice product space

The attached point coordinates define the ideal and also occur among the
code coordinates. The scalar correction theorem supplies their independence,
so the remaining coordinates may be chosen on one open satisfying every
full-size subset condition.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial AttachedTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p q d : ℕ}

/-- Affine-chart coordinates of the projection obtained by dropping the normal coordinate. -/
def projectedCoordinates (a : PointCoordinates K (n + 1) p) : PointCoordinates K n p :=
  fun ij => a (ij.1, ij.2.succ)

/-- The projected chart representative is the attached projection. -/
theorem chartPoint_projectedCoordinates (a : PointCoordinates K (n + 1) p) (i : Fin p) :
    chartPoint K (projectedCoordinates a) i = projectedPoint a i := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [chartPoint, projectedCoordinates, projectedPoint]
  · simp only [chartPoint_castSucc, projectedCoordinates, projectedPoint, Fin.succ_castSucc]

/-- The attached evaluation is ordinary evaluation at these projected coordinates. -/
theorem projectedEvaluation_eq (a : PointCoordinates K (n + 1) p) (d : ℕ) :
    projectedEvaluation a d = pointEvaluation K (projectedCoordinates a) d := by
  ext f i
  simp [projectedEvaluation, pointEvaluation, evaluationLinear, chartPoint_projectedCoordinates]

/-- The product space `U_A` of Lemma 4.3. -/
def sliceProductSpace (a : PointCoordinates K (n + 1) p) (d : ℕ) :
    Submodule K (Forms K (n + 1) (d + 1 + 1)) :=
  (tangentPointProductForm a (d + 1)).range

local instance sliceProductGroup (a : PointCoordinates K (n + 1) p) (d : ℕ) :
    AddCommGroup (sliceProductSpace a d) := Module.addCommMonoidToAddCommGroup K

/-- Evaluation on the attached projections and the additional trace points. -/
def sliceProductEvaluation (a : PointCoordinates K (n + 1) p) (d : ℕ)
    (b : PointCoordinates K n q) :
    sliceProductSpace a d →ₗ[K] ((Fin p ⊕ Fin q) → K) :=
  attachedFreeEvaluation (sliceProductSpace a d) (projectedCoordinates a) b

/-- Multiplication injectivity gives the exact slice-product dimension. -/
theorem finrank_sliceProductSpace (a : PointCoordinates K (n + 1) p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 1 + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1))) :
    finrank K (sliceProductSpace a d) =
      (n + 1) * finrank K (pointDegreePiece K a (d + 1)) :=
  finrank_tangentPointProductForm_range a ha hmul

/-- Lemma 4.3, including uniform independence of quotient coordinate classes,
for the actual ideal cut out by the same attached points. -/
theorem generic_sliceProduct_code [Infinite K] [CharZero K]
    (a : PointCoordinates K (n + 1) p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 1 + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hprojected : Function.Surjective (projectedEvaluation a (d + 1)))
    (q : ℕ) (hcount : (n + 1) * finrank K (pointDegreePiece K a (d + 1)) ≤ p + q) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ b : PointCoordinates K n q, eval b P ≠ 0) ∧
      ∀ b, eval b P ≠ 0 → Function.Injective (sliceProductEvaluation a d b) ∧
        ∀ (r : ℕ) (f : Fin r ↪ (Fin p ⊕ Fin q)),
          r ≤ finrank K (((Fin p ⊕ Fin q) → K) ⧸ (sliceProductEvaluation a d b).range) →
          LinearIndependent K (coordinateClass (sliceProductEvaluation a d b) ∘ f) := by
  have hA : Function.Surjective
      (subspaceEvaluation (sliceProductSpace a d) (projectedCoordinates a)) := by
    change Function.Surjective ((pointEvaluation K (projectedCoordinates a) (d + 1 + 1)).comp
      (tangentPointProductForm a (d + 1)).range.subtype)
    rw [← projectedEvaluation_eq]
    exact traceProductImage_evaluation_surjective_of_projected a d ha hprojected
  have hdim : finrank K (sliceProductSpace a d) ≤ p + q := by
    rw [finrank_sliceProductSpace a ha hmul]
    exact hcount
  exact generic_attachedFree_code (sliceProductSpace a d) (projectedCoordinates a) hA q hdim

end IdealGeneration.TwoNormalIntegral
