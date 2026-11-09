module

public import IdealGeneration.CubicConeWitness
public import IdealGeneration.CubicTenPoints
public import IdealGeneration.ConeJointMatrix
public import IdealGeneration.GenericRectangularDescent
public import Mathlib.Data.List.Nodup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Descent of the actual cubic cone equations from the finite coefficient certificate. -/

namespace IdealGeneration.CubicTen
open MvPolynomial Matrix ConeParameterSpace ConeMonomialChart

noncomputable section

variable {K : Type*} [Field K]

def normalEvaluationMatrix (R : Type*) [CommSemiring R] : Matrix (Fin 75) (Fin 100) R :=
  evaluationMatrix (fun i j => pointCoordinate i j) normalExponent

def traceEvaluationMatrix (R : Type*) [CommSemiring R] : Matrix (Fin 90) (Fin 120) R :=
  evaluationMatrix (fun i j => traceCoordinate i j) traceExponent

@[simp] theorem normalEvaluationMatrix_intCast {R : Type*} [CommRing R] :
    (normalEvaluationMatrix ℤ).map (Int.castRingHom R) = normalEvaluationMatrix R := by
  unfold normalEvaluationMatrix
  rw [evaluationMatrix_map]
  simp only [Int.coe_castRingHom, Int.cast_natCast]

@[simp] theorem traceEvaluationMatrix_intCast {R : Type*} [CommRing R] :
    (traceEvaluationMatrix ℤ).map (Int.castRingHom R) = traceEvaluationMatrix R := by
  unfold traceEvaluationMatrix
  rw [evaluationMatrix_map]
  simp only [Int.coe_castRingHom, Int.cast_natCast]

private theorem configuration_point (i : Fin 75) (j : Fin 10) :
    (configuration support (parameters K)).point i j = (pointCoordinate i j : K) := by
  refine Fin.addCases (motive := fun j =>
    (configuration support (parameters K)).point i j = (pointCoordinate i j : K))
    (fun k : Fin 2 => ?_) (fun k : Fin 8 => ?_) j
  · simp only [ConeConfiguration.point, pointCoordinate, Fin.addCases_left]; rfl
  · simp only [ConeConfiguration.point, pointCoordinate, Fin.addCases_right, Nat.cast_mul]; rfl

private theorem configuration_trace (i : Fin 90) (j : Fin 8) :
    (configuration support (parameters K)).trace i j = (traceCoordinate i j : K) := rfl

theorem arrayGet_injective (a : Array ℕ) (n : ℕ) (ha : a.size = n)
    (hn : a.toList.Nodup) : Function.Injective (fun i : Fin n => a[i.val]!) := by
  intro i j hij
  have hi : i.val < a.size := ha.symm ▸ i.isLt
  have hj : j.val < a.size := ha.symm ▸ j.isLt
  change a[i.val]! = a[j.val]! at hij
  rw [getElem!_pos a i.val hi, getElem!_pos a j.val hj] at hij
  have hil : i.val < a.toList.length := by simpa using hi
  have hjl : j.val < a.toList.length := by simpa using hj
  apply Fin.ext
  apply (hn.getElem_inj_iff (hi := hil) (hj := hjl)).mp
  simpa only [Array.getElem_toList] using hij

private def exponentCode {n : ℕ} (e : Fin n →₀ ℕ) : ℕ := ∑ j, e j * 5 ^ j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normalExponent_injective : Function.Injective normalExponent := by
  have hcode : ∀ i : Fin 100, exponentCode (normalExponent i) = normalExponentCodes[i.val]! := by
    decide +kernel
  intro i j hij
  apply arrayGet_injective normalExponentCodes 100 (by decide) (by decide +kernel)
  simpa only [hcode] using congrArg exponentCode hij

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem traceExponent_injective : Function.Injective traceExponent := by
  have hcode : ∀ i : Fin 120, exponentCode (traceExponent i) = traceExponentCodes[i.val]! := by
    decide +kernel
  intro i j hij
  apply arrayGet_injective traceExponentCodes 120 (by decide) (by decide +kernel)
  simpa only [hcode] using congrArg exponentCode hij

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem normalExponent_degree (i : Fin 100) : (normalExponent i).degree = 3 := by
  rw [Finsupp.degree_eq_sum]
  exact (by decide +kernel : ∀ k : Fin 100, (∑ j, normalExponent k j) = 3) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem traceExponent_degree (i : Fin 120) : (traceExponent i).degree = 3 := by
  rw [Finsupp.degree_eq_sum]
  exact (by decide +kernel : ∀ k : Fin 120, (∑ j, traceExponent k j) = 3) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normalExponent_positive :
    ∀ i : Fin 100, ∃ j : Fin 2, normalExponent i (j.castAdd 8) ≠ 0 := by decide +kernel

variable [CharZero K]

/-- The modular joint matrix verifies the concrete integer-coordinate middle map. -/
theorem middle_injective_of_modular_stack (p : ℕ) [Fact (Nat.Prime p)]
    (h : Function.Injective
      (jointMatrix normalExponent traceExponent quarticExponent
        (normalEvaluationMatrix (ZMod p)) (traceEvaluationMatrix (ZMod p))).mulVec) :
    Function.Injective ((configuration support (parameters K)).middleMultiplication 3) := by
  let A := jointMatrix normalExponent traceExponent quarticExponent
    (normalEvaluationMatrix ℤ) (traceEvaluationMatrix ℤ)
  have hmod : Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec := by
    simpa only [A, jointMatrix_map, normalEvaluationMatrix_intCast,
      traceEvaluationMatrix_intCast] using h
  have hcast := integer_matrix_mulVec_injective_of_mod (K := K) A p hmod
  have hnormal := normalSynth_surjective (K := K) (c := 2) (m := 8) (d := 3) normalExponent normalExponent_degree
    normalExponent_positive normalExponent_injective (by decide)
  have htrace := formSynth_surjective (K := K) (n := 8) (d := 3) traceExponent traceExponent_degree
    traceExponent_injective (by decide)
  apply middle_injective_of_jointMatrix _ _ _ quarticExponent normalExponent_degree
    traceExponent_degree normalExponent_positive hnormal htrace
  dsimp only [A] at hcast
  rw [jointMatrix_map, normalEvaluationMatrix_intCast, traceEvaluationMatrix_intCast] at hcast
  have hpoint : (configuration support (parameters K)).point =
      (fun i j => (pointCoordinate i j : K)) := funext fun i => funext (configuration_point i)
  have hrep : (configuration support (parameters K)).trace =
      (fun i j => (traceCoordinate i j : K)) := funext fun i => funext (configuration_trace i)
  rw [hpoint, hrep]
  exact hcast

end
end IdealGeneration.CubicTen
