module

public import IdealGeneration.CubicInitialPoints
public import Mathlib.Data.List.Nodup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual evaluation matrices of the initial cubic cone. -/

namespace IdealGeneration.CubicInitial
open MvPolynomial Matrix ConeParameterSpace ConeMonomialChart

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

def normalEvaluationMatrix (R : Type*) [CommSemiring R] : Matrix (Fin 108) (Fin 144) R :=
  evaluationMatrix (fun i j => pointCoordinate i j) normalExponent

def traceEvaluationMatrix (R : Type*) [CommSemiring R] : Matrix (Fin 165) (Fin 220) R :=
  evaluationMatrix (fun i j => traceCoordinate i j) traceExponent

@[simp] theorem normalEvaluationMatrix_intCast {R : Type*} [CommRing R] :
    (normalEvaluationMatrix ℤ).map (Int.castRingHom R) = normalEvaluationMatrix R := by
  rw [normalEvaluationMatrix, evaluationMatrix_map]
  unfold normalEvaluationMatrix
  congr 1
  funext i j
  exact Int.cast_natCast (pointCoordinate i j)

@[simp] theorem traceEvaluationMatrix_intCast {R : Type*} [CommRing R] :
    (traceEvaluationMatrix ℤ).map (Int.castRingHom R) = traceEvaluationMatrix R := by
  rw [traceEvaluationMatrix, evaluationMatrix_map]
  unfold traceEvaluationMatrix
  congr 1
  funext i j
  exact Int.cast_natCast (traceCoordinate i j)

theorem configuration_point (i : Fin 108) (j : Fin 12) :
    (configuration support (parameters K)).point i j = (pointCoordinate i j : K) := by
  exact Fin.addCases
    (motive := fun j : Fin (2 + 10) =>
      (configuration support (parameters K)).point i j = (pointCoordinate i j : K))
    (fun k => by
      rw [ConeConfiguration.point, pointCoordinate, Fin.addCases_left, Fin.addCases_left]
      rfl)
    (fun k => by
      rw [ConeConfiguration.point, pointCoordinate, Fin.addCases_right, Fin.addCases_right,
        Nat.cast_mul]
      rfl) j

theorem configuration_trace (i : Fin 165) (j : Fin 10) :
    (configuration support (parameters K)).trace i j = (traceCoordinate i j : K) := rfl

private theorem arrayGet_injective (a : Array ℕ) (n : ℕ) (ha : a.size = n)
    (hn : a.toList.Nodup) : Function.Injective (fun i : Fin n => a[i.val]!) := by
  intro i j hij
  have hi : i.val < a.size := ha.symm ▸ i.isLt
  have hj : j.val < a.size := ha.symm ▸ j.isLt
  change a[i.val]! = a[j.val]! at hij
  rw [getElem!_pos a i.val hi, getElem!_pos a j.val hj] at hij
  apply Fin.ext
  have hi' : i.val < a.toList.length := hi
  have hj' : j.val < a.toList.length := hj
  apply (hn.getElem_inj_iff (hi := hi') (hj := hj')).mp
  rw [Array.getElem_toList hi', Array.getElem_toList hj']
  exact hij

private def exponentCode {n : ℕ} (e : Fin n →₀ ℕ) : ℕ := ∑ j, e j * 5 ^ j.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normalExponent_injective : Function.Injective normalExponent := by
  have hcode : ∀ i : Fin 144, exponentCode (normalExponent i) = normalCodes[i.val]! := by
    decide +kernel
  intro i j hij
  apply arrayGet_injective normalCodes 144 (by decide) (by decide +kernel)
  simpa only [hcode] using congrArg exponentCode hij

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem traceExponent_injective : Function.Injective traceExponent := by
  have hcode : ∀ i : Fin 220, exponentCode (traceExponent i) = traceCodes[i.val]! := by
    decide +kernel
  intro i j hij
  apply arrayGet_injective traceCodes 220 (by decide) (by decide +kernel)
  simpa only [hcode] using congrArg exponentCode hij

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normalExponent_degree (i : Fin 144) : (normalExponent i).degree = 3 := by
  rw [Finsupp.degree_eq_sum]
  exact (by decide +kernel : ∀ k : Fin 144, (∑ j, normalExponent k j) = 3) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem traceExponent_degree (i : Fin 220) : (traceExponent i).degree = 3 := by
  rw [Finsupp.degree_eq_sum]
  exact (by decide +kernel : ∀ k : Fin 220, (∑ j, traceExponent k j) = 3) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem normalExponent_positive :
    ∀ i : Fin 144, ∃ j : Fin 2, normalExponent i (j.castAdd 10) ≠ 0 := by decide +kernel

/-- The normal evaluation matrix is the evaluation of the synthesized form. -/
theorem normalEvaluation_synth (u : Fin 144 → K) :
    ConeMiddleFamily.normalEvaluation support (parameters K) 3
      (normalSynth normalExponent normalExponent_degree normalExponent_positive u) =
      (normalEvaluationMatrix K).mulVec u := by
  funext i
  change eval ((configuration support (parameters K)).point i) (synth normalExponent u) = _
  simp only [configuration_point, normalEvaluationMatrix, evaluationMatrix_mulVec]
  rfl

/-- The trace evaluation matrix is the evaluation of the synthesized form. -/
theorem traceEvaluation_synth (u : Fin 220 → K) :
    traceEvaluation (parameters K) 3 (formSynth traceExponent traceExponent_degree u) =
      (traceEvaluationMatrix K).mulVec u := by
  funext i
  change eval ((configuration support (parameters K)).trace i) (synth traceExponent u) = _
  simp only [configuration_trace, traceEvaluationMatrix, evaluationMatrix_mulVec]
  rfl

theorem normalEvaluation_surjective_of_matrix
    (h : Function.Surjective (normalEvaluationMatrix K).mulVec) :
    Function.Surjective (ConeMiddleFamily.normalEvaluation support (parameters K) 3) := by
  intro w
  obtain ⟨u, hu⟩ := h w
  exact ⟨_, (normalEvaluation_synth u).trans hu⟩

theorem traceEvaluation_surjective_of_matrix
    (h : Function.Surjective (traceEvaluationMatrix K).mulVec) :
    Function.Surjective (traceEvaluation (parameters K) 3) := by
  intro w
  obtain ⟨u, hu⟩ := h w
  exact ⟨_, (traceEvaluation_synth u).trans hu⟩

theorem point_ne_zero (i : Fin 108) :
    (configuration support (parameters K)).point i ≠ 0 := by
  intro h
  have h0 := congrFun h (Fin.castAdd 10 (0 : Fin 2))
  rw [configuration_point] at h0
  rw [pointCoordinate, Fin.addCases_left] at h0
  rw [normalCoordinate, ite_eq_left rfl, Nat.cast_one, Pi.zero_apply] at h0
  exact one_ne_zero h0

end
end IdealGeneration.CubicInitial
