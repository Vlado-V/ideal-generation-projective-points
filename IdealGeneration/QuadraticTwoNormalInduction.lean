module

public import IdealGeneration.QuadraticInduction
public import IdealGeneration.QuadraticEndpointA1
public import IdealGeneration.TripleNormalQuadraticTransfer

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The quadratic induction with the concrete two-normal steps

The only cone witnesses still supplied by the caller are the three-normal
ones in the residue-zero branch. Their actual middle and scalar evaluations
enter the marked-cone transfer directly.
-/

noncomputable section
namespace IdealGeneration

open ConeParameterSpace ConeMiddleFamily

variable {K : Type*} [Field K] [CharZero K]

/-- The verified two-normal constructions, the twelve-variable base, and
the three-normal cone witnesses prove the quadratic assertion for every
projective dimension and point count. -/
theorem idealGenerationAt_quadratic_of_three_normal_witnesses
    (hTwelve : ∀ p, IdealGenerationAt K 11 2 p)
    (hCone : ∀ h : ℕ, 8 ≤ h → h % 3 = 2 →
      ∃ C : ConeConfiguration K 3 (h + 4) (2 * h + 12) ((h + 4) * (h + 5) / 3),
        Function.Surjective (normalEvaluation C.support (encode C) 2) ∧
        Function.Surjective (representativeEvaluation K C.trace 2) ∧
        Function.Bijective (C.middleMultiplication 2)) :
    ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p := by
  have hModZero (h : ℕ) (hh : 8 ≤ h) (hmod : h % 3 = 2)
      (htrace : IdealGenerationAt K (h + 3) 2 ((h + 4) * (h + 5) / 3)) :
      IdealGenerationAt K (h + 6) 2 ((h + 7) * (h + 8) / 3) := by
    obtain ⟨C, hn, hs, hm⟩ := hCone h hh hmod
    exact TripleNormal.quadratic_tripleNormal_endpoint h hmod C hn hs hm htrace
  intro n p hn
  exact quadratic_induction_of_steps hTwelve QuadraticEndpointA1.quadratic_mod_one_all
    QuadraticEndpointA1.quadratic_mod_two_all hModZero (n + 1) (by omega) p

end IdealGeneration
