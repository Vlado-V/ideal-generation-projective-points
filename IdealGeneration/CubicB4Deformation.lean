module

public import IdealGeneration.CubicB11Actual
public import IdealGeneration.CubicB22Higher
public import IdealGeneration.BlockDeterminantDeformation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual B.4 columns give the two diagonal blocks of the first-order determinant. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B4

open MvPolynomial
open B5 B22

variable {K : Type*} [Field K] {m f : ℕ}
variable (Q : Parameters K (m + 2)) (hQ : ∀ e, Q.single e = B5.single e)
variable (free : Fin f → Fin (m + 2) → K) (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (near : A → B11Probe K m) (low : A → B7Column m) (high : B → HigherColumn Q)

/-- A fixed new row is a single-edge allowed scalar or one component at a far probe. -/
abbrev FixedRow := NewIncidence Q ⊕ ((Fin (m + 2) → K) × Fin 2)

variable (far : B → FixedRow Q)

/-- The fixed new row evaluates an actual parameter, with the allowed single-edge sign. -/
def fixedValue (r : FixedRow Q) (x : Q.EliminatedParameters) : K :=
  match r with
  | .inl e => -eval (edgeRow Q e) (Q.parameterPhi free h₂ h₆ x 1).val
  | .inr (y, k) => eval y (Q.parameterPhi free h₂ h₆ x k).val

/-- The upper-left moving row block of the actual cubic columns. -/
def movingLower : Matrix A A (Polynomial K) := Matrix.of fun i j =>
  movingEvaluation (near i).point (near i).weight
    (Q.parameterPhi free h₂ h₆ (b7Parameter Q hQ (low j)) (near i).component).val

/-- The upper-right moving row block of the actual cubic columns. -/
def movingHigher : Matrix A B (Polynomial K) := Matrix.of fun i j =>
  movingEvaluation (near i).point (near i).weight
    (Q.parameterPhi free h₂ h₆ (highParameter Q (high j)) (near i).component).val

/-- The fixed lower-left row block. -/
def fixedLower : Matrix B A (Polynomial K) := Matrix.of fun i j =>
  Polynomial.C (fixedValue Q free h₂ h₆ (far i) (b7Parameter Q hQ (low j)))

/-- The fixed higher right block. -/
def fixedHigher : Matrix B B (Polynomial K) := Matrix.of fun i j =>
  Polynomial.C (fixedValue Q free h₂ h₆ (far i) (highParameter Q (high j)))

omit [Fintype A] [DecidableEq A] in
/-- The upper first-order matrix is the literal B.5 evaluation of the lower families. -/
theorem movingLower_coeff_one :
    (movingLower Q hQ free h₂ h₆ near low).map (fun p => p.coeff 1) =
      Matrix.of (fun i j => b7Value (actualB7Data Q) (near i).point (near i).weight
        (near i).component (low j)) := by
  ext i j
  exact movingEvaluation_b7Parameter_coeff_one Q hQ free h₂ h₆
    (near i).point (near i).weight (low j) (near i).component

/-- The first-order determinant argument applies to the matrices of actual cubic products. -/
theorem exists_actual_block_det_ne_zero [Infinite K]
    (h11 : (Matrix.of (fun i j => b7Value (actualB7Data Q) (near i).point (near i).weight
      (near i).component (low j)) : Matrix A A K).det ≠ 0)
    (h22 : (Matrix.of (fun i j => fixedValue Q free h₂ h₆ (far i) (highParameter Q (high j))) :
      Matrix B B K).det ≠ 0) :
    ∃ eps : K, eps ≠ 0 ∧
      ((Matrix.fromBlocks (movingLower Q hQ free h₂ h₆ near low)
        (movingHigher Q free h₂ h₆ near high) (fixedLower Q hQ free h₂ h₆ low far)
        (fixedHigher Q free h₂ h₆ high far)).map (Polynomial.evalRingHom eps)).det ≠ 0 := by
  apply exists_block_det_eval_ne_zero
  · intro i j
    exact movingEvaluation_b7Parameter_coeff_zero Q hQ free h₂ h₆
      (near i).point (near i).weight (low j) (near i).component
  · intro i j
    change (movingEvaluation (near i).point (near i).weight
      (Q.parameterPhi free h₂ h₆ (highParameter Q (high j)) (near i).component).val).coeff 0 = 0
    rw [higherPolynomial_parameterPhi, movingEvaluation_higherPolynomial_coeff_zero]
  · intro i j
    change (movingEvaluation (near i).point (near i).weight
      (Q.parameterPhi free h₂ h₆ (highParameter Q (high j)) (near i).component).val).coeff 1 = 0
    rw [higherPolynomial_parameterPhi, movingEvaluation_higherPolynomial_coeff_one]
  · rw [movingLower_coeff_one]
    exact h11
  · have heq : (fixedHigher Q free h₂ h₆ high far).map (Polynomial.evalRingHom 0) =
        (Matrix.of fun i j => fixedValue Q free h₂ h₆ (far i) (highParameter Q (high j))) := by
      ext i j
      simp [fixedHigher]
    rw [heq]
    exact h22

end IdealGeneration.CubicSupported.B4
