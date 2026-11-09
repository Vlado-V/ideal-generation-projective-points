module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace IdealGeneration

/-- The rational evaluation matrix displayed in Appendix C.4. -/
def finalCubicBlock : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -2 / 15, -1 / 15, 2 / 15;
    -1, -7 / 60, 7 / 30, 17 / 60;
    12, -63 / 10, 1 / 10, 33 / 10;
    -6, -1 / 5, 39 / 10, -23 / 10]

/-- Exact, kernel-checked determinant certificate for Appendix C.4. -/
theorem finalCubicBlock_det : finalCubicBlock.det = -(603 : ℚ) / 40 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [finalCubicBlock, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix, Fin.succAbove]

/-- The final cubic block is nonsingular over the rationals. -/
theorem finalCubicBlock_det_ne_zero : finalCubicBlock.det ≠ 0 := by
  rw [finalCubicBlock_det]
  norm_num

/-- Its four columns are independent as an evaluation map. -/
theorem finalCubicBlock_mulVec_injective :
    Function.Injective finalCubicBlock.mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero finalCubicBlock_det_ne_zero

/-- The same rational certificate is nonsingular over every characteristic-zero field. -/
theorem finalCubicBlock_det_ne_zero_over (K : Type*) [Field K] [CharZero K] :
    (finalCubicBlock.map (Rat.castHom K)).det ≠ 0 := by
  change (finalCubicBlock.map (fun x : ℚ => (x : K))).det ≠ 0
  rw [← Rat.cast_det]
  exact_mod_cast finalCubicBlock_det_ne_zero

/-- Coefficients of the three lifts at the vertex `u`.
The indices are `s², st, t²`, then `x, u, v`, then `s, t`. -/
def cubicLiftU : Fin 3 → Matrix (Fin 3) (Fin 2) ℚ :=
  ![!![0, 1 / 4; -1, 0; 7 / 12, -1 / 12],
    !![0, -1 / 2; 0, 0; -1 / 12, -5 / 12],
    !![0, -1 / 2; 0, -1 / 2; -5 / 12, 5 / 12]]

/-- Coefficients of the three lifts at the vertex `v`, with the same index order. -/
def cubicLiftV : Fin 3 → Matrix (Fin 3) (Fin 2) ℚ :=
  ![!![-2 / 15, 2 / 15; -1 / 12, -1 / 12; -1 / 3, 0],
    !![-1 / 15, -4 / 15; -1 / 12, -5 / 12; 0, 0],
    !![2 / 15, -13 / 60; -5 / 12, 1 / 6; 0, -1 / 4]]

/-- Evaluation of a vector-valued linear form in the trace coordinates `x,u,v`. -/
def evalCubicLift (a : Matrix (Fin 3) (Fin 2) ℚ)
    (y : Fin 3 → ℚ) (i : Fin 2) : ℚ :=
  ∑ j, y j * a j i

/-- The three quadratic normal monomials in their stated order. -/
def normalQuadratic (q : Fin 3) (σ : Fin 2 → ℚ) : ℚ :=
  ![σ 0 * σ 0, σ 0 * σ 1, σ 1 * σ 1] q

/-- The five cone conditions incident to `u`, in the order of Appendix C.4. -/
def cubicUDirections : Matrix (Fin 5) (Fin 2) ℚ :=
  !![1, 0; 0, 1; 1, 2; 1, 1; 1, -1]

def cubicUTrace : Matrix (Fin 5) (Fin 3) ℚ :=
  !![0, 1, 0; 0, 1, 0; 1, 1, 0; 0, 1, 1; 0, 1, 1]

def cubicUHeights : Fin 5 → ℚ := ![1, 2, 2, 2, 3]

/-- The six cone conditions incident to `v`, in the order of Appendix C.4. -/
def cubicVDirections : Matrix (Fin 6) (Fin 2) ℚ :=
  !![1, 0; 0, 1; 1, 1; 2, 1; 1, 1; 1, -1]

def cubicVTrace : Matrix (Fin 6) (Fin 3) ℚ :=
  !![0, 0, 1; 0, 0, 1; 1, 0, 1; 1, 0, 1; 0, 1, 1; 0, 1, 1]

def cubicVHeights : Fin 6 → ℚ := ![3, 4, 3, 5, 2, 3]

/-- The `u` lifts satisfy the normal-form cone equations B.4 for the stated data. -/
theorem cubicLiftU_cone_equations (q : Fin 3) (i : Fin 5) :
    normalQuadratic q (cubicUDirections i) + cubicUHeights i *
      (∑ c, cubicUDirections i c * evalCubicLift (cubicLiftU q) (cubicUTrace i) c) = 0 := by
  fin_cases q <;> fin_cases i <;>
    norm_num [normalQuadratic, cubicUDirections, cubicUHeights, evalCubicLift,
      cubicLiftU, cubicUTrace, Fin.sum_univ_succ]

/-- The `v` lifts satisfy the normal-form cone equations B.4 for the stated data. -/
theorem cubicLiftV_cone_equations (q : Fin 3) (i : Fin 6) :
    normalQuadratic q (cubicVDirections i) + cubicVHeights i *
      (∑ c, cubicVDirections i c * evalCubicLift (cubicLiftV q) (cubicVTrace i) c) = 0 := by
  fin_cases q <;> fin_cases i <;>
    norm_num [normalQuadratic, cubicVDirections, cubicVHeights, evalCubicLift,
      cubicLiftV, cubicVTrace, Fin.sum_univ_succ]

/-- The chosen gauge at the unique single edge is zero in the `s` component. -/
theorem cubicLiftU_gauge (q : Fin 3) : cubicLiftU q 0 0 = 0 := by
  fin_cases q <;> rfl

/-- Four polynomial columns, ordered as the single-edge column and then the three lift differences. -/
def finalCubicColumns (y : Fin 3 → ℚ) (c : Fin 4) (i : Fin 2) : ℚ :=
  let liftColumn := fun q => y 1 * y 2 *
    (evalCubicLift (cubicLiftV q) y i - evalCubicLift (cubicLiftU q) y i)
  ![y 0 * y 1 * y 2 * ![(2 : ℚ), -1] i,
    liftColumn 0, liftColumn 1, liftColumn 2] c

/-- The actual evaluations of the four polynomial columns are the displayed rational block. -/
theorem finalCubicColumns_evaluation (c : Fin 4) :
    finalCubicColumns ![1, 1, 1] c 0 = finalCubicBlock 0 c ∧
    finalCubicColumns ![1, 1, 1] c 1 = finalCubicBlock 1 c ∧
    finalCubicColumns ![1, 2, 3] c 0 = finalCubicBlock 2 c ∧
    finalCubicColumns ![1, 2, 3] c 1 = finalCubicBlock 3 c := by
  fin_cases c <;>
    norm_num [finalCubicColumns, evalCubicLift, cubicLiftV, cubicLiftU,
      finalCubicBlock, Fin.sum_univ_succ]

/-- Evaluation of a two-component function at the two chosen trace points. -/
def finalCubicColumnEvaluation :
    ((Fin 3 → ℚ) → Fin 2 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) where
  toFun f := ![f ![1, 1, 1] 0, f ![1, 1, 1] 1,
    f ![1, 2, 3] 0, f ![1, 2, 3] 1]
  map_add' f g := by ext i; fin_cases i <;> rfl
  map_smul' a f := by ext i; fin_cases i <;> rfl

/-- The four actual vector-valued cubic columns are linearly independent. -/
theorem finalCubicColumns_linearIndependent :
    LinearIndependent ℚ (fun c y i => finalCubicColumns y c i) := by
  apply LinearIndependent.of_comp finalCubicColumnEvaluation
  have evaluation_eq :
      finalCubicColumnEvaluation ∘ (fun c y i => finalCubicColumns y c i) =
        finalCubicBlock.col := by
    funext c i
    fin_cases i
    · exact (finalCubicColumns_evaluation c).1
    · exact (finalCubicColumns_evaluation c).2.1
    · exact (finalCubicColumns_evaluation c).2.2.1
    · exact (finalCubicColumns_evaluation c).2.2.2
  rw [evaluation_eq]
  exact Matrix.linearIndependent_cols_of_det_ne_zero finalCubicBlock_det_ne_zero

end IdealGeneration
