module

public import IdealGeneration.CubicSupportedRestriction
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The polynomial evaluations at the moving free probes of Appendix B.4. -/

noncomputable section
namespace IdealGeneration.CubicSupported

open MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- A probe with fixed old coordinates and two new coordinates proportional to the motion parameter. -/
def movingTrace (y : Fin m → K) (c : Fin 2 → K) : Fin (m + 2) → Polynomial K :=
  Fin.addCases (fun i => Polynomial.C (y i)) (fun j => Polynomial.C (c j) * Polynomial.X)

/-- Evaluating a trace form at a moving probe gives a polynomial in the motion parameter. -/
def movingEvaluation (y : Fin m → K) (c : Fin 2 → K) :
    Poly K (m + 2) →ₐ[K] Polynomial K := MvPolynomial.aeval (movingTrace y c)

@[simp] theorem movingEvaluation_oldX (y : Fin m → K) (c : Fin 2 → K) (i : Fin m) :
    movingEvaluation y c (X (Fin.castAdd 2 i)) = Polynomial.C (y i) := by
  simp [movingEvaluation, movingTrace]

@[simp] theorem movingEvaluation_newX (y : Fin m → K) (c : Fin 2 → K) (j : Fin 2) :
    movingEvaluation y c (X (Fin.natAdd m j)) = Polynomial.C (c j) * Polynomial.X := by
  simp [movingEvaluation, movingTrace]

/-- Specializing the motion parameter gives the actual moving free trace representative. -/
theorem movingEvaluation_aeval (y : Fin m → K) (c : Fin 2 → K)
    (epsilon : K) (F : Poly K (m + 2)) :
    Polynomial.aeval epsilon (movingEvaluation y c F) =
      eval (Fin.addCases y (fun j => c j * epsilon)) F := by
  have h : (Polynomial.aeval epsilon).comp (movingEvaluation y c) =
      MvPolynomial.aeval (Fin.addCases y (fun j => c j * epsilon)) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have hh := congrArg (fun f : Poly K (m + 2) →ₐ[K] K => f F) h
  simpa using hh

/-- The constant term is evaluation at the old-space probe. -/
theorem movingEvaluation_coeff_zero (y : Fin m → K) (c : Fin 2 → K)
    (F : Poly K (m + 2)) :
    (movingEvaluation y c F).coeff 0 = eval (extendTrace y) F := by
  have h : (Polynomial.aeval (0 : K)).comp (movingEvaluation y c) =
      MvPolynomial.aeval (extendTrace y) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have hh := congrArg (fun f : Poly K (m + 2) →ₐ[K] K => f F) h
  rw [Polynomial.coeff_zero_eq_aeval_zero]
  simpa using hh

/-- A column factored by one new variable has the prescribed first-order evaluation. -/
theorem movingEvaluation_Xnew (y : Fin m → K) (c : Fin 2 → K)
    (j : Fin 2) (F : Poly K (m + 2)) :
    movingEvaluation y c (X (Fin.natAdd m j) * F) =
      Polynomial.X * (Polynomial.C (c j) * movingEvaluation y c F) := by
  rw [map_mul, movingEvaluation_newX]
  ring

theorem movingEvaluation_Xnew_coeff_one (y : Fin m → K) (c : Fin 2 → K)
    (j : Fin 2) (F : Poly K (m + 2)) :
    (movingEvaluation y c (X (Fin.natAdd m j) * F)).coeff 1 =
      c j * eval (extendTrace y) F := by
  rw [movingEvaluation_Xnew, show (1 : ℕ) = 0 + 1 by omega, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul, movingEvaluation_coeff_zero]

/-- A product with two new-variable factors is divisible by the square of the motion parameter. -/
theorem movingEvaluation_Xnew_Xnew (y : Fin m → K) (c : Fin 2 → K)
    (i j : Fin 2) (F : Poly K (m + 2)) :
    movingEvaluation y c (X (Fin.natAdd m i) * (X (Fin.natAdd m j) * F)) =
      Polynomial.X ^ 2 * (Polynomial.C (c i * c j) * movingEvaluation y c F) := by
  rw [movingEvaluation_Xnew, movingEvaluation_Xnew, map_mul]
  ring

/-- Every column vanishing on the old trace space has a factor of the motion parameter. -/
theorem movingEvaluation_dvd_of_eval_zero (y : Fin m → K) (c : Fin 2 → K)
    (F : Poly K (m + 2)) (h : eval (extendTrace y) F = 0) :
    Polynomial.X ∣ movingEvaluation y c F := by
  rw [Polynomial.X_dvd_iff, movingEvaluation_coeff_zero]
  exact h

end IdealGeneration.CubicSupported
