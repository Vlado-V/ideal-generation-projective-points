module

public import IdealGeneration.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact finite certificates for the six-variable core in Appendix A.2. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial

/-- The six cone points, in the coordinate order `s,t,y₁,y₂,z₁,z₂`. -/
def quadraticCoreConeMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1,-1,1,0,0,0;
     2,-1,0,1,0,0;
     1,1,0,0,1,0;
     2,4,1,1,1,0;
     1,3,0,0,0,1;
     3,12,1,1,0,1]

/-- Elimination of the four support coordinates leaves these two normal rows. -/
def quadraticCoreReducedMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![-2,5;-1,11]

theorem quadraticCoreReducedMatrix_det : quadraticCoreReducedMatrix.det = -17 := by
  norm_num [quadraticCoreReducedMatrix, Matrix.det_fin_two]

theorem quadraticCore_elimination (j : Fin 2) :
    quadraticCoreConeMatrix 3 (Fin.castLE (by omega : 2 ≤ 6) j) =
      quadraticCoreConeMatrix 0 (Fin.castLE (by omega : 2 ≤ 6) j) +
        quadraticCoreConeMatrix 1 (Fin.castLE (by omega : 2 ≤ 6) j) +
        quadraticCoreConeMatrix 2 (Fin.castLE (by omega : 2 ≤ 6) j) + quadraticCoreReducedMatrix 0 j ∧
    quadraticCoreConeMatrix 5 (Fin.castLE (by omega : 2 ≤ 6) j) =
      quadraticCoreConeMatrix 0 (Fin.castLE (by omega : 2 ≤ 6) j) +
        quadraticCoreConeMatrix 1 (Fin.castLE (by omega : 2 ≤ 6) j) +
        quadraticCoreConeMatrix 4 (Fin.castLE (by omega : 2 ≤ 6) j) + quadraticCoreReducedMatrix 1 j := by
  fin_cases j <;> norm_num [quadraticCoreConeMatrix, quadraticCoreReducedMatrix]

set_option maxHeartbeats 800000 in
/-- The actual six cone points are linearly independent. The full row ordering has determinant 17. -/
theorem quadraticCoreConeMatrix_det : quadraticCoreConeMatrix.det = 17 := by
  norm_num [quadraticCoreConeMatrix, Matrix.det_succ_row_zero, Matrix.submatrix,
    Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove]

theorem quadraticCoreConeMatrix_det_ne_zero : quadraticCoreConeMatrix.det ≠ 0 := by
  rw [quadraticCoreConeMatrix_det]
  norm_num

theorem quadraticCoreConeMatrix_det_ne_zero_over (K : Type*) [Field K] [CharZero K] :
    (quadraticCoreConeMatrix.map (Rat.castHom K)).det ≠ 0 := by
  change (quadraticCoreConeMatrix.map (fun x : ℚ => (x : K))).det ≠ 0
  rw [← Rat.cast_det]
  exact_mod_cast quadraticCoreConeMatrix_det_ne_zero

/-- The three core quadratic equations in coordinates `y₁,y₂,z₁,z₂`. -/
def quadraticCoreQuadrics : Fin 3 → MvPolynomial (Fin 4) ℚ :=
  ![(X 0 - X 1) * X 2, (X 0 - X 1) * X 3, X 2 * X 3]

/-- The seven core trace points in the two-layer flag. -/
def quadraticCoreFlag : Fin 7 → Fin 4 → ℚ :=
  ![![1,0,0,0], ![0,1,0,0], ![1,1,0,0], ![0,0,1,0],
    ![1,1,1,0], ![0,0,0,1], ![1,1,0,1]]

theorem quadraticCoreQuadrics_vanish (i : Fin 3) (j : Fin 7) :
    eval (quadraticCoreFlag j) (quadraticCoreQuadrics i) = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [quadraticCoreQuadrics, quadraticCoreFlag]

/-- The three extra scalar interpolation points in (A.4). -/
def quadraticCoreProbes : Fin 3 → Fin 4 → ℚ :=
  ![![1,0,1,0], ![1,0,0,1], ![0,0,1,1]]

theorem quadraticCoreQuadrics_probe (i j : Fin 3) :
    eval (quadraticCoreProbes i) (quadraticCoreQuadrics j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [quadraticCoreQuadrics, quadraticCoreProbes]

/-- The three core equations are independent, with the stated probes as dual coordinates. -/
theorem quadraticCoreQuadrics_linearIndependent : LinearIndependent ℚ quadraticCoreQuadrics := by
  let ev : MvPolynomial (Fin 4) ℚ →ₗ[ℚ] (Fin 3 → ℚ) :=
    { toFun := fun f i => eval (quadraticCoreProbes i) f
      map_add' := by intro f g; ext i; simp
      map_smul' := by intro c f; ext i; simp }
  apply LinearIndependent.of_comp ev
  have heq : ev ∘ quadraticCoreQuadrics = (1 : Matrix (Fin 3) (Fin 3) ℚ).col := by
    funext j i
    change eval (quadraticCoreProbes i) (quadraticCoreQuadrics j) = if i = j then 1 else 0
    exact quadraticCoreQuadrics_probe i j
  rw [heq]
  exact Matrix.linearIndependent_cols_of_det_ne_zero (by simp)

end IdealGeneration
