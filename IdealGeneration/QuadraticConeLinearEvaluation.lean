module

public import IdealGeneration.QuadraticFlagLifts
public import IdealGeneration.QuadraticMiddleSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Mixed quadrics interpolate arbitrary values at the actual cone points. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial QuadraticFlag

/-- One cone point over each base coordinate and two over each layer. -/
abbrev ConeIndex (P J : Type*) := (P × Bool) ⊕ (J × Bool)

namespace QuadraticLiftParameters

variable {K P J : Type*} [Field K] (D : QuadraticLiftParameters K P J)

/-- Trace coordinates of the chosen cone representatives. -/
def coneTracePoint : ConeIndex P J → ((P × Bool) ⊕ J → K)
  | .inl i => traceBasePoint i
  | .inr (j, false) => layerPoint j
  | .inr (j, true) => pairedLayerPoint D.distinguishedPair j

/-- Actual normal coordinates, including the cone heights. -/
def coneNormalPoint : ConeIndex P J → (Bool → K)
  | .inl i => fun b => D.baseHeight i * (if b then -1 else D.slope i)
  | .inr (j, false) => fun b => D.height₀ j * (if b then (D.normal₀ j).2 else (D.normal₀ j).1)
  | .inr (j, true) => fun b => D.height₁ j * (if b then (D.normal₁ j).2 else (D.normal₁ j).1)

/-- Evaluate the trace coefficients and then the two normal variables. -/
def conePointEval (z : ConeIndex P J) : MvPolynomial Bool (MvPolynomial ((P × Bool) ⊕ J) K) →ₐ[K] K :=
  aevalTower (aeval (D.coneTracePoint z)) (D.coneNormalPoint z)

@[simp] theorem conePointEval_X (z : ConeIndex P J) (b : Bool) :
    D.conePointEval z (X b) = D.coneNormalPoint z b :=
  aevalTower_X _ _ _

@[simp] theorem conePointEval_C (z : ConeIndex P J) (p : MvPolynomial ((P × Bool) ⊕ J) K) :
    D.conePointEval z (C p) = eval (D.coneTracePoint z) p :=
  aevalTower_C _ _ _

/-- Simultaneous evaluation at the actual cone points. -/
def coneEvaluation : MvPolynomial Bool (MvPolynomial ((P × Bool) ⊕ J) K) →ₗ[K] (ConeIndex P J → K) :=
  LinearMap.pi fun z => (D.conePointEval z).toLinearMap

@[simp] theorem coneEvaluation_apply (p : MvPolynomial Bool (MvPolynomial ((P × Bool) ⊕ J) K))
    (z : ConeIndex P J) : D.coneEvaluation p z = D.conePointEval z p := rfl

/-- Actual evaluation of a normal-linear polynomial is the normal pairing. -/
theorem conePointEval_normalPairMap (q : MvPolynomial ((P × Bool) ⊕ J) K ×
    MvPolynomial ((P × Bool) ⊕ J) K) (z : ConeIndex P J) :
    D.conePointEval z (normalPairMap (K := K) q) =
      D.coneNormalPoint z false * eval (D.coneTracePoint z) q.1 +
      D.coneNormalPoint z true * eval (D.coneTracePoint z) q.2 := by
  simp only [normalPairMap_apply, conePointEval, map_add, map_mul,
    aevalTower_C, aevalTower_X, aeval_eq_eval]
  rw [mul_comm (eval (D.coneTracePoint z) q.1), mul_comm (eval (D.coneTracePoint z) q.2)]

variable [Fintype P] [Fintype J]

/-- Evaluate mixed quadrics specified by their two trace coefficient vectors. -/
def mixedConeEvaluation : (((P × Bool) ⊕ J → K) × ((P × Bool) ⊕ J → K)) →ₗ[K]
    (ConeIndex P J → K) :=
  D.coneEvaluation.comp (normalPairMap.comp
    (linearPolynomialLinearMap.prodMap linearPolynomialLinearMap))

theorem mixedConeEvaluation_apply
    (q : ((P × Bool) ⊕ J → K) × ((P × Bool) ⊕ J → K)) (z : ConeIndex P J) :
    D.mixedConeEvaluation q z =
      D.coneNormalPoint z false * eval (D.coneTracePoint z) (linearPolynomial q.1) +
      D.coneNormalPoint z true * eval (D.coneTracePoint z) (linearPolynomial q.2) :=
  D.conePointEval_normalPairMap _ _

/-- At each base point, use only its coefficient in the second trace form. -/
def mixedBaseCoefficient (a : ConeIndex P J → K) (i : P × Bool) : K :=
  -(a (.inl i) / D.baseHeight i)

/-- The base part of the second trace form on the distinguished paired support. -/
def mixedPairedBaseValue (a : ConeIndex P J → K) : K :=
  ∑ i, D.mixedBaseCoefficient a i * pairPoint D.distinguishedPair i

/-- The layer coefficients solve the two prescribed equations after removing
the contribution already assigned on the base. -/
def mixedLayerCoefficients (a : ConeIndex P J → K) (j : J) : K × K :=
  solveLayerNormal (D.normal₀ j) (D.normal₁ j)
    (a (.inr (j, false)) / D.height₀ j)
    (a (.inr (j, true)) / D.height₁ j - (D.normal₁ j).2 * D.mixedPairedBaseValue a)

omit [Fintype J] in
theorem mixedLayerCoefficients_spec (a : ConeIndex P J → K) (j : J) :
    (D.normal₀ j).1 * (D.mixedLayerCoefficients a j).1 +
      (D.normal₀ j).2 * (D.mixedLayerCoefficients a j).2 = a (.inr (j, false)) / D.height₀ j ∧
    (D.normal₁ j).1 * (D.mixedLayerCoefficients a j).1 +
      (D.normal₁ j).2 * (D.mixedLayerCoefficients a j).2 =
      a (.inr (j, true)) / D.height₁ j - (D.normal₁ j).2 * D.mixedPairedBaseValue a :=
  solveLayerNormal_spec _ _ _ _ (D.determinant_ne j)

/-- Explicit coefficients of a mixed quadric with prescribed cone values. -/
def mixedConeSection (a : ConeIndex P J → K) :
    ((P × Bool) ⊕ J → K) × ((P × Bool) ⊕ J → K) :=
  (Sum.elim (fun _ => 0) (fun j => (D.mixedLayerCoefficients a j).1),
    Sum.elim (D.mixedBaseCoefficient a) (fun j => (D.mixedLayerCoefficients a j).2))

private theorem section_eval_base (a : ConeIndex P J → K) (i : P × Bool) :
    eval (traceBasePoint i) (linearPolynomial (D.mixedConeSection a).1) = 0 ∧
    eval (traceBasePoint i) (linearPolynomial (D.mixedConeSection a).2) =
      D.mixedBaseCoefficient a i := by
  classical
  constructor <;> simp [mixedConeSection, traceBasePoint, coordinatePoint]

private theorem section_eval_layer₀ (a : ConeIndex P J → K) (j : J) :
    eval (layerPoint j) (linearPolynomial (D.mixedConeSection a).1) = (D.mixedLayerCoefficients a j).1 ∧
    eval (layerPoint j) (linearPolynomial (D.mixedConeSection a).2) = (D.mixedLayerCoefficients a j).2 := by
  classical
  constructor <;> simp [mixedConeSection, layerPoint, coordinatePoint]

private theorem section_eval_layer₁ (a : ConeIndex P J → K) (j : J) :
    eval (pairedLayerPoint D.distinguishedPair j) (linearPolynomial (D.mixedConeSection a).1) =
      (D.mixedLayerCoefficients a j).1 ∧
    eval (pairedLayerPoint D.distinguishedPair j) (linearPolynomial (D.mixedConeSection a).2) =
      D.mixedPairedBaseValue a + (D.mixedLayerCoefficients a j).2 := by
  classical
  constructor <;> simp [mixedConeSection, pairedLayerPoint, coordinatePoint, mixedPairedBaseValue]

/-- The explicit mixed quadrics recover all prescribed cone values. -/
theorem mixedConeSection_rightInverse : Function.RightInverse D.mixedConeSection D.mixedConeEvaluation := by
  intro a
  funext z
  rw [mixedConeEvaluation_apply]
  cases z with
  | inl i =>
    simp only [coneNormalPoint, coneTracePoint, Bool.false_eq_true, ↓reduceIte,
      (D.section_eval_base a i).1, (D.section_eval_base a i).2, mul_zero, zero_add,
      mixedBaseCoefficient, mul_neg_one, neg_mul_neg]
    exact mul_div_cancel₀ _ (D.baseHeight_ne i)
  | inr jb =>
    rcases jb with ⟨j,b⟩
    cases b
    · simp only [coneNormalPoint, coneTracePoint, Bool.false_eq_true, ↓reduceIte,
        (D.section_eval_layer₀ a j).1, (D.section_eval_layer₀ a j).2]
      calc
        _ = D.height₀ j * ((D.normal₀ j).1 * (D.mixedLayerCoefficients a j).1 +
            (D.normal₀ j).2 * (D.mixedLayerCoefficients a j).2) := by ring
        _ = D.height₀ j * (a (.inr (j, false)) / D.height₀ j) := by
          rw [(D.mixedLayerCoefficients_spec a j).1]
        _ = _ := mul_div_cancel₀ _ (D.height₀_ne j)
    · simp only [coneNormalPoint, coneTracePoint, Bool.false_eq_true, ↓reduceIte,
        (D.section_eval_layer₁ a j).1, (D.section_eval_layer₁ a j).2]
      calc
        _ = D.height₁ j * (a (.inr (j, true)) / D.height₁ j) := by
          linear_combination D.height₁ j * (D.mixedLayerCoefficients_spec a j).2
        _ = _ := mul_div_cancel₀ _ (D.height₁_ne j)

/-- The actual mixed normal rows impose independent scalar conditions. -/
theorem mixedConeEvaluation_surjective : Function.Surjective D.mixedConeEvaluation :=
  D.mixedConeSection_rightInverse.surjective

end QuadraticLiftParameters
end IdealGeneration.QuadraticElimination
