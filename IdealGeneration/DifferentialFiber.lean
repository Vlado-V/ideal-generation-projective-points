module

public import IdealGeneration.HyperplaneEuler

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Coordinates on a normalized Euler fiber

The final coordinate is normalized to one.  Dropping that coordinate identifies
the Euler fiber with an ordinary coordinate space, and the final coordinate
vector provides a complement.
-/

noncomputable section
namespace IdealGeneration.DifferentialFiber

variable {K : Type*} [Field K] {n : ℕ}

/-- The linear equation defining the Euler fiber at `y`. -/
def dot (y : Fin (n + 1) → K) : (Fin (n + 1) → K) →ₗ[K] K where
  toFun w := ∑ i, y i * w i
  map_add' w z := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem dot_apply (y w : Fin (n + 1) → K) :
    dot y w = ∑ i, y i * w i := rfl

/-- Forget the last coordinate of a fiber vector. -/
def dropLast : (Fin (n + 1) → K) →ₗ[K] (Fin n → K) where
  toFun w i := w i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dropLast_apply (w : Fin (n + 1) → K) (i : Fin n) :
    dropLast w i = w i.castSucc := rfl

/-- Complete the first coordinates to a vector satisfying the Euler equation. -/
def tangentLift (y : Fin (n + 1) → K) : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun w := Fin.snoc w (-(∑ i, y i.castSucc * w i))
  map_add' w z := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [mul_add, Finset.sum_add_distrib, add_comm]
    · simp
  map_smul' c w := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Finset.mul_sum, mul_left_comm]
    · simp

@[simp] theorem tangentLift_castSucc (y : Fin (n + 1) → K) (w : Fin n → K)
    (i : Fin n) : tangentLift y w i.castSucc = w i := by
  simp [tangentLift]

@[simp] theorem tangentLift_last (y : Fin (n + 1) → K) (w : Fin n → K) :
    tangentLift y w (Fin.last n) = -(∑ i, y i.castSucc * w i) := by
  simp [tangentLift]

@[simp] theorem dropLast_tangentLift (y : Fin (n + 1) → K) (w : Fin n → K) :
    dropLast (tangentLift y w) = w := by
  funext i
  simp

/-- Normalization makes the completion lie in the Euler fiber. -/
theorem dot_tangentLift (y : Fin (n + 1) → K) (hy : y (Fin.last n) = 1)
    (w : Fin n → K) : dot y (tangentLift y w) = 0 := by
  rw [dot_apply, Fin.sum_univ_castSucc]
  simp [hy]

/-- The final coordinate vector complements the Euler fiber. -/
def lastUnit : Fin (n + 1) → K := Fin.snoc 0 1

@[simp] theorem lastUnit_castSucc (i : Fin n) : (lastUnit : Fin (n + 1) → K) i.castSucc = 0 := by
  simp [lastUnit]

@[simp] theorem lastUnit_last : (lastUnit : Fin (n + 1) → K) (Fin.last n) = 1 := by
  simp [lastUnit]

@[simp] theorem dropLast_lastUnit : dropLast (lastUnit : Fin (n + 1) → K) = 0 := by
  funext i
  simp

/-- Its Euler coordinate is one in the normalized chart. -/
theorem dot_lastUnit (y : Fin (n + 1) → K) (hy : y (Fin.last n) = 1) :
    dot y lastUnit = 1 := by
  rw [dot_apply, Fin.sum_univ_castSucc]
  simp [hy]

/-- Every vector splits into its tangent part and its Euler coordinate. -/
theorem tangentLift_add_dot_lastUnit (y w : Fin (n + 1) → K)
    (hy : y (Fin.last n) = 1) :
    tangentLift y (dropLast w) + dot y w • lastUnit = w := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, tangentLift_last, dropLast_apply,
      lastUnit_last, mul_one, dot_apply, Fin.sum_univ_castSucc, hy, one_mul]
    ring
  · simp

/-- A tangent vector is determined by its first coordinates. -/
theorem tangentLift_dropLast_of_dot_eq_zero (y w : Fin (n + 1) → K)
    (hy : y (Fin.last n) = 1) (hw : dot y w = 0) :
    tangentLift y (dropLast w) = w := by
  simpa [hw] using tangentLift_add_dot_lastUnit y w hy

/-- Evaluating an Euler relation lands in the Euler fiber. -/
theorem dot_evaluation_eq_zero (y : Fin (n + 1) → K) (d : ℕ)
    (f : HyperplaneEuler.Relations K (n + 1) d) :
    dot y (fun i => MvPolynomial.eval y (f.val i).val) = 0 := by
  have hf : (∑ i, MvPolynomial.X i * (f.val i).val) = 0 :=
    congrArg Subtype.val f.property
  have he := congrArg (MvPolynomial.eval y) hf
  simpa only [dot_apply, map_sum, map_mul, MvPolynomial.eval_X, map_zero] using he

end IdealGeneration.DifferentialFiber
