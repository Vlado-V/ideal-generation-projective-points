module

public import IdealGeneration.CubicExtendedCert.Base

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicExtended

open MvPolynomial Matrix ConeParameterSpace ConeMonomialChart CertifiedRank

@[simp] theorem normalEvaluationMatrix_intCast {R : Type*} [CommRing R] :
    (normalEvaluationMatrix ℤ).map (Int.castRingHom R) = normalEvaluationMatrix R := by
  rw [normalEvaluationMatrix, evaluationMatrix_map]
  unfold normalEvaluationMatrix
  congr 1
  funext i j
  exact Int.cast_natCast (pointCoordinate i j)

theorem configuration_point {K : Type*} [Field K] (i : Fin 147) (j : Fin 14) :
    (configuration support (parameters K)).point i j = (pointCoordinate i j : K) := by
  exact Fin.addCases
    (motive := fun j : Fin (2 + 12) =>
      (configuration support (parameters K)).point i j = (pointCoordinate i j : K))
    (fun k => by
      rw [ConeConfiguration.point, pointCoordinate, Fin.addCases_left, Fin.addCases_left]
      rfl)
    (fun k => by
      rw [ConeConfiguration.point, pointCoordinate, Fin.addCases_right, Fin.addCases_right,
        Nat.cast_mul]
      rfl) j

theorem normalExponent_degree (i : Fin 196) : (normalExponent i).degree = 3 := by
  rw [Finsupp.degree_eq_sum]
  exact (by decide +kernel : ∀ k : Fin 196, (∑ j, normalExponent k j) = 3) i

theorem normalExponent_positive :
    ∀ i : Fin 196, ∃ j : Fin 2, normalExponent i (j.castAdd 12) ≠ 0 := by
  decide +kernel

theorem normalExponent_injective : Function.Injective normalExponent := by
  have hcode : ∀ i : Fin 196, packCoefficients 5 (normalExponent i) = normalCode i := by
    decide +kernel
  intro i j hij
  apply List.nodup_ofFn.mp (by decide +kernel : (List.ofFn normalCode).Nodup)
  simpa only [hcode] using congrArg (fun e : Fin 14 →₀ ℕ => packCoefficients 5 e) hij

/-- The 196 monomials span the actual normal cubic forms on the extended space. -/
theorem normalChart_surjective (K : Type*) [Field K] :
    Function.Surjective (normalSynth (K := K) (c := 2) (m := 12)
      normalExponent normalExponent_degree normalExponent_positive) :=
  normalSynth_surjective _ _ _ normalExponent_injective (by decide +kernel)

/-- The extended matrix acts by actual polynomial evaluation at the marked cone points. -/
theorem normalEvaluation_synth {K : Type*} [Field K] (u : Fin 196 → K) :
    ConeMiddleFamily.normalEvaluation support (parameters K) 3
      (normalSynth normalExponent normalExponent_degree normalExponent_positive u) =
      (normalEvaluationMatrix K).mulVec u := by
  funext i
  change eval ((configuration support (parameters K)).point i) (synth normalExponent u) = _
  simp only [configuration_point, normalEvaluationMatrix, evaluationMatrix_mulVec]
  rfl

#print axioms normalEvaluation_synth
#print axioms normalChart_surjective

end IdealGeneration.CubicExtended
