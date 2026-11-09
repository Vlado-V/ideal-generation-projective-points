module

public import IdealGeneration.QuadraticCore
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The explicit core calculation for the injective quadratic endpoint in Appendix A.3. -/

noncomputable section
namespace IdealGeneration.QuadraticInjectiveCore
open MvPolynomial

variable {K : Type*} [Field K]

abbrev CorePolynomial (K : Type*) [Field K] := MvPolynomial (Fin 3) K

def u₁ : CorePolynomial K := X 0 + 3 * X 2
def v₁ : CorePolynomial K := X 0 - 3 * X 2
def u₂ : CorePolynomial K := X 1 + 5 * X 2
def v₂ : CorePolynomial K := 2 * X 1 - 5 * X 2
def U₂ : CorePolynomial K := -4 * X 2
def V₂ : CorePolynomial K := -X 0 - 2 * X 1 + 3 * X 2
def U₃ : CorePolynomial K := 10 * X 2
def V₃ : CorePolynomial K := X 0 + X 1 - 11 * X 2

/-- The coefficient pair of the actual product corresponding to `(0,H₁)`. -/
def response₁ : CorePolynomial K × CorePolynomial K :=
  (-u₁ * U₂ - v₁ * U₃, -u₁ * V₂ - v₁ * V₃)

/-- The coefficient pair of the actual product corresponding to `(0,H₂)`. -/
def response₂ : CorePolynomial K × CorePolynomial K :=
  (-u₂ * U₂ - v₂ * U₃, -u₂ * V₂ - v₂ * V₃)

def projected₁ : CorePolynomial K × CorePolynomial K :=
  response₁ - ((-X 1 - 41 * X 2) * u₁, (-X 1 - 41 * X 2) * v₁) -
    ((X 0 + 33 * X 2) * u₂, (X 0 + 33 * X 2) * v₂)

def projected₂ : CorePolynomial K × CorePolynomial K :=
  response₂ - ((X 1 - 70 * X 2) * u₁, (X 1 - 70 * X 2) * v₁) -
    ((-X 0 + 56 * X 2) * u₂, (-X 0 + 56 * X 2) * v₂)

/-- The first projected pair is the stated scalar quadric in direction `(1,2)`. -/
theorem projected₁_formula : projected₁ (K := K) =
    (30 * (X 0 - X 1) * X 2, 60 * (X 0 - X 1) * X 2) := by
  apply Prod.ext <;> dsimp [projected₁, response₁, u₁, v₁, u₂, v₂, U₂, V₂, U₃, V₃] <;> ring

/-- The second projected pair is the stated scalar quadric in direction `(1,1)`. -/
theorem projected₂_formula : projected₂ (K := K) =
    (75 * (X 0 - X 1) * X 2, 75 * (X 0 - X 1) * X 2) := by
  apply Prod.ext <;> dsimp [projected₂, response₂, u₁, v₁, u₂, v₂, U₂, V₂, U₃, V₃] <;> ring

def probe : Fin 3 → K := ![1, 0, 1]

theorem projected₁_probe :
    (eval (probe (K := K)) projected₁.1, eval (probe (K := K)) projected₁.2) = (30, 60) := by
  rw [projected₁_formula]
  norm_num [probe]

theorem projected₂_probe :
    (eval (probe (K := K)) projected₂.1, eval (probe (K := K)) projected₂.2) = (75, 75) := by
  rw [projected₂_formula]
  norm_num [probe]

/-- Columns are the two actual projected values at the core probe. -/
def responseMatrix : Matrix (Fin 2) (Fin 2) K := !![30, 75; 60, 75]

theorem responseMatrix_det : (responseMatrix (K := K)).det = -2250 := by
  norm_num [responseMatrix, Matrix.det_fin_two]

theorem responseMatrix_det_ne_zero [CharZero K] : (responseMatrix (K := K)).det ≠ 0 := by
  rw [responseMatrix_det]
  norm_num

theorem responseMatrix_injective [CharZero K] :
    Function.Injective (responseMatrix (K := K)).mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero responseMatrix_det_ne_zero

/-- The full core coefficient of `K₁`, retaining the second layer variable. -/
def coefficientConstraint (α₁ α₂ a b : K) : MvPolynomial (Fin 5) K :=
  -(C α₁ * (X 0 + 3 * X 2 + 15 * X 3)) -
    C α₂ * (X 1 + 5 * X 2 + 27 * X 3) -
    C a * (X 4 - 4 * X 2 - 12 * X 3) - C b * (10 * X 2 + 132 * X 3)

/-- Its four indicated coefficients already determine the four core parameters. -/
theorem coefficientConstraint_eq_zero [CharZero K] (α₁ α₂ a b : K)
    (h : coefficientConstraint α₁ α₂ a b = 0) : α₁ = 0 ∧ α₂ = 0 ∧ a = 0 ∧ b = 0 := by
  have hα₁ : α₁ = 0 := by
    have hx := congrArg (eval (Pi.single (0 : Fin 5) (1 : K))) h
    simpa [coefficientConstraint, Pi.single_apply] using hx
  have hα₂ : α₂ = 0 := by
    have hy := congrArg (eval (Pi.single (1 : Fin 5) (1 : K))) h
    simpa [coefficientConstraint, Pi.single_apply] using hy
  have ha : a = 0 := by
    have ht := congrArg (eval (Pi.single (4 : Fin 5) (1 : K))) h
    simpa [coefficientConstraint, Pi.single_apply] using ht
  have hb : b = 0 := by
    have hz := congrArg (eval (Pi.single (2 : Fin 5) (1 : K))) h
    have hh : -(b * 10) = 0 := by
      simpa [coefficientConstraint, Pi.single_apply, hα₁, hα₂, ha] using hz
    have hmul : b * 10 = 0 := neg_eq_zero.mp hh
    exact (mul_eq_zero.mp hmul).resolve_right (by norm_num)
  exact ⟨hα₁, hα₂, ha, hb⟩

/-- The coefficient constraint and the two projected probe values kill the entire core kernel. -/
theorem core_parameters_eq_zero [CharZero K] (α₁ α₂ a b β₁ β₂ : K)
    (hC : coefficientConstraint α₁ α₂ a b = 0)
    (hprobe : responseMatrix.mulVec ![β₁, β₂] = 0) :
    α₁ = 0 ∧ α₂ = 0 ∧ a = 0 ∧ b = 0 ∧ β₁ = 0 ∧ β₂ = 0 := by
  obtain ⟨hα₁, hα₂, ha, hb⟩ := coefficientConstraint_eq_zero α₁ α₂ a b hC
  have hzero : (![β₁, β₂] : Fin 2 → K) = 0 :=
    responseMatrix_injective (hprobe.trans (Matrix.mulVec_zero _).symm)
  have hβ₁ := congrFun hzero 0
  have hβ₂ := congrFun hzero 1
  exact ⟨hα₁, hα₂, ha, hb, by simpa using hβ₁, by simpa using hβ₂⟩

end IdealGeneration.QuadraticInjectiveCore
