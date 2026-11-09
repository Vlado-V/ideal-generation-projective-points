module

public import IdealGeneration.CubicNormalExpansion
public import IdealGeneration.CubicUpperSolve

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The literal normal-degree three and two equations for supported cubic multiplication. -/

noncomputable section

namespace IdealGeneration.CubicUpperBlockEquations

open MvPolynomial CubicSupported CubicNormalExpansion CubicUpperSolve

variable {K : Type*} [Field K] {m : ℕ}

/-- The trace-quadratic target from the two normal multipliers. -/
def quadraticTarget (U V : Coefficients K m) (i j : Fin m) : Fin 3 → K :=
  ![upperCoefficient U.2.2.1 U.2.2.2 i j 0,
    upperCoefficient U.2.2.1 U.2.2.2 i j 1 + upperCoefficient V.2.2.1 V.2.2.2 i j 0,
    upperCoefficient V.2.2.1 V.2.2.2 i j 1]

theorem quadraticTarget_add (U V U' V' : Coefficients K m) :
    quadraticTarget (U + U') (V + V') = quadraticTarget U V + quadraticTarget U' V' := by
  funext i j q
  by_cases h : i < j
  · fin_cases q <;> simp [quadraticTarget, upperCoefficient, h]
    all_goals ring
  · by_cases hij : i = j <;>
      fin_cases q <;> simp [quadraticTarget, upperCoefficient, h, hij]
    all_goals ring

theorem quadraticTarget_smul (r : K) (U V : Coefficients K m) :
    quadraticTarget (r • U) (r • V) = r • quadraticTarget U V := by
  funext i j q
  by_cases h : i < j
  · fin_cases q <;> simp [quadraticTarget, upperCoefficient, h, smul_eq_mul]
    all_goals ring
  · by_cases hij : i = j <;>
      fin_cases q <;> simp [quadraticTarget, upperCoefficient, h, hij, smul_eq_mul]
    all_goals ring

/-- Each normal cubic coefficient is the trace-linear sum of its forced differences. -/
theorem productNormal3_eq_sum (U V : Coefficients K m) (W : Fin m → Coefficients K m)
    (q : Fin 4) :
    productNormal3 U V W q =
      ∑ i, C ((W i).1 q - cubicCorrection (U.2.1 i) (V.2.1 i) q) * X i := by
  fin_cases q <;>
    simp [productNormal3, traceB, cubicCorrection, QuadraticElimination.normalCubicMap,
      ← Finset.sum_add_distrib]
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The actual normal cubic block vanishes exactly for the forced cubic coefficients. -/
theorem productNormal3_eq_zero_iff (U V : Coefficients K m) (W : Fin m → Coefficients K m) :
    productNormal3 U V W = 0 ↔
      ∀ i, (W i).1 = cubicCorrection (U.2.1 i) (V.2.1 i) := by
  constructor
  · intro h i
    funext q
    have hq := congrFun h q
    rw [productNormal3_eq_sum] at hq
    have hi := congrArg (eval (vertexSupport i 1)) hq
    apply sub_eq_zero.mp
    simpa [map_sum, vertexSupport, mul_ite] using hi
  · intro h
    funext q
    rw [productNormal3_eq_sum]
    simp [h]

/-- The actual normal quadratic block is the sum of the target and mixed trace quadratics. -/
theorem productNormal2_eq_traceQuadratic
    (U V : Coefficients K m) (W : Fin m → Coefficients K m) (q : Fin 3) :
    productNormal2 U V W q =
      traceQuadratic (fun i j => C (quadraticTarget U V i j q)) X +
      traceQuadratic (fun i j => C ((W i).2.1 j q)) X := by
  have hW : (∑ i, X i * traceB (W i) q) =
      traceQuadratic (fun i j => C ((W i).2.1 j q)) X := by
    simp only [traceB, traceQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hA : ![traceA U 0, traceA U 1 + traceA V 0, traceA V 1] q =
      traceQuadratic (fun i j => C (quadraticTarget U V i j q)) X := by
    fin_cases q
    · rfl
    · simp [traceA, quadraticTarget, traceQuadratic, add_mul, Finset.sum_add_distrib]
    · rfl
  exact congrArg₂ (· + ·) hA hW

/-- Every solution of the actual normal quadratic block is a symmetric completion. -/
theorem productNormal2_eq_zero_iff (h₂ : (2 : K) ≠ 0)
    (U V : Coefficients K m) (W : Fin m → Coefficients K m) :
    productNormal2 U V W = 0 ↔
      ∃ z : Edge m → Fin 3 → K,
        (fun i j => (W i).2.1 j) = symmetricCompletion (quadraticTarget U V) z := by
  constructor
  · intro h
    apply symmetricCompletion_complete h₂ (quadraticTarget U V) (fun i j => (W i).2.1 j)
    intro q y
    have hq := congrFun h q
    rw [productNormal2_eq_traceQuadratic] at hq
    have hy := congrArg (eval y) hq
    rw [add_comm]
    simpa [traceQuadratic, map_sum] using hy
  · rintro ⟨z, hz⟩
    funext q
    rw [productNormal2_eq_traceQuadratic]
    have hB (i j : Fin m) : (W i).2.1 j q = symmetricCompletion (quadraticTarget U V) z i j q :=
      congrFun (congrFun (congrFun hz i) j) q
    simp only [hB, Pi.zero_apply]
    rw [add_comm]
    exact symmetricCompletion_polynomial_cancel h₂ (quadraticTarget U V) z q

end IdealGeneration.CubicUpperBlockEquations
