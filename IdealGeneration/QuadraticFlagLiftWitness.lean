module

public import IdealGeneration.QuadraticFlagLifts
public import IdealGeneration.QuadraticFlagEliminationBridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The explicit normal lifts and mixed generators satisfy every actual cone equation. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial QuadraticFlag Module

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

@[simp] theorem eval_firstKernelMap_base (a : P × Bool → J → K)
    (v : P × Bool → K) (i : P × Bool) :
    eval (traceBasePoint i) (firstKernelMap a v) = v i := by
  classical
  simp [firstKernelMap, Fintype.linearCombination_apply, firstGenerator,
    traceBasePoint, coordinatePoint, Algebra.smul_def]

@[simp] theorem eval_secondKernelMap_base (c : P × Bool → K) (b : P × Bool → J → K)
    (v : P × Bool → K) (i : P × Bool) :
    eval (traceBasePoint i) (secondKernelMap c b v) = c i * v i := by
  classical
  simp [secondKernelMap, Fintype.linearCombination_apply, secondGenerator,
    traceBasePoint, coordinatePoint, Algebra.smul_def, mul_comm]

@[simp] theorem eval_firstKernelMap_layer (a : P × Bool → J → K)
    (v : P × Bool → K) (j : J) :
    eval (layerPoint j) (firstKernelMap a v) = ∑ i, v i * a i j := by
  classical
  simp [firstKernelMap, Fintype.linearCombination_apply, firstGenerator,
    layerPoint, coordinatePoint, Algebra.smul_def]

@[simp] theorem eval_secondKernelMap_layer (c : P × Bool → K) (b : P × Bool → J → K)
    (v : P × Bool → K) (j : J) :
    eval (layerPoint j) (secondKernelMap c b v) = ∑ i, v i * b i j := by
  classical
  simp [secondKernelMap, Fintype.linearCombination_apply, secondGenerator,
    layerPoint, coordinatePoint, Algebra.smul_def]

@[simp] theorem eval_firstKernelMap_pairedLayer (a : P × Bool → J → K)
    (v : P × Bool → K) (p : P) (j : J) :
    eval (pairedLayerPoint p j) (firstKernelMap a v) = ∑ i, v i * (pairPoint p i + a i j) := by
  classical
  simp [firstKernelMap, Fintype.linearCombination_apply, firstGenerator,
    pairedLayerPoint, coordinatePoint, Algebra.smul_def]

@[simp] theorem eval_secondKernelMap_pairedLayer (c : P × Bool → K) (b : P × Bool → J → K)
    (v : P × Bool → K) (p : P) (j : J) :
    eval (pairedLayerPoint p j) (secondKernelMap c b v) =
      ∑ i, v i * (c i * pairPoint p i + b i j) := by
  classical
  simp [secondKernelMap, Fintype.linearCombination_apply, secondGenerator,
    pairedLayerPoint, coordinatePoint, Algebra.smul_def]

namespace QuadraticLiftParameters
variable (D : QuadraticLiftParameters K P J)

/-- The first component of the explicitly solved mixed generator correction. -/
def firstCorrection (i : P × Bool) (j : J) : K :=
  (layerCorrection D.slope D.distinguishedPair D.normal₀ D.normal₁ i j).1

/-- The second component of the explicitly solved mixed generator correction. -/
def secondCorrection (i : P × Bool) (j : J) : K :=
  (layerCorrection D.slope D.distinguishedPair D.normal₀ D.normal₁ i j).2

omit [Fintype P] [Fintype J] in
theorem first_normal_equation (i : P × Bool) (j : J) :
    (D.normal₀ j).1 * D.firstCorrection i j + (D.normal₀ j).2 * D.secondCorrection i j = 0 :=
  (layerCorrection_spec D.slope D.distinguishedPair D.normal₀ D.normal₁ D.determinant_ne i j).1

omit [Fintype P] [Fintype J] in
theorem second_normal_equation (i : P × Bool) (j : J) :
    (D.normal₁ j).1 * (pairPoint D.distinguishedPair i + D.firstCorrection i j) +
      (D.normal₁ j).2 * (D.slope i * pairPoint D.distinguishedPair i + D.secondCorrection i j) = 0 :=
  (layerCorrection_spec D.slope D.distinguishedPair D.normal₀ D.normal₁ D.determinant_ne i j).2

/-- All constructed normal lifts and mixed generators vanish at the prescribed cone points. -/
def actualNormalLiftVanishing :
    NormalLiftVanishing D.slope D.distinguishedPair D.normal₀ D.normal₁ D.firstLift D.secondLift
      (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection) :=
  D.normalLiftVanishing (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
    (by
      intro i v
      rw [eval_firstKernelMap_base, eval_secondKernelMap_base]
      ring)
    (by
      intro j v
      rw [eval_firstKernelMap_layer, eval_secondKernelMap_layer, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      linear_combination v i * D.first_normal_equation i j)
    (by
      intro j v
      rw [eval_firstKernelMap_pairedLayer, eval_secondKernelMap_pairedLayer, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      linear_combination v i * D.second_normal_equation i j)

/-- The actual constructed `W'` has the paper's upper bound for every choice
of independent layer directions and nonzero heights. -/
theorem finrank_actual_projected_space_le (hc : Function.Injective D.slope) :
    finrank K ↥(quadraticMiddleSpace D.firstLift D.secondLift D.slope
      D.firstCorrection D.secondCorrection ⊓
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
        (quadraticFlagVanishing (K := K) (P := P) (J := J))) ≤
      2 * Fintype.card (P × Bool) + 2 := by
  have hn₀ (j : J) : D.normal₀ j ≠ 0 := by
    intro h
    have hd := D.determinant_ne j
    simp [h] at hd
  have hn₁ (j : J) : D.normal₁ j ≠ 0 := by
    intro h
    have hd := D.determinant_ne j
    simp [h] at hd
  exact finrank_quadraticMiddleSpace_inf_flag_le D.slope D.firstCorrection D.secondCorrection
    D.distinguishedPair D.normal₀ D.normal₁ hc hn₀ hn₁ D.first_normal_equation D.second_normal_equation
    D.firstLift D.secondLift D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing

end QuadraticLiftParameters
end IdealGeneration.QuadraticElimination
