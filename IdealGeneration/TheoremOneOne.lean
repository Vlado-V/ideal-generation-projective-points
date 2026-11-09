module

public import IdealGeneration.TheoremOneOneStatement
public import IdealGeneration.QuadraticLowDimensionTwelve
public import IdealGeneration.QuadraticTwoNormalInduction
public import IdealGeneration.TripleNormalFlagInitial
public import IdealGeneration.TripleNormalEnlargement
public import IdealGeneration.TripleNormalInitialCertified
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import IdealGeneration.CubicTen
public import IdealGeneration.CubicDimensionInduction
public import IdealGeneration.CubicB6Terminal
public import IdealGeneration.TwoNormalInduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Ideal generation for general reduced projective points. -/

namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The initial certificate and the two- and three-normal steps prove the quadratic case. -/
theorem idealGenerationAt_quadratic :
    ∀ n p, 1 ≤ n → IdealGenerationAt K n 2 p := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 3 K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos 3 K (by decide)))
  have hprimitive := (Polynomial.isRoot_cyclotomic_iff_charZero (by decide : 0 < 3)).mp hω
  let F₈ := TripleNormal.flagEight_of_certificate ω hprimitive TripleNormalInitial.initialCertificate
  apply idealGenerationAt_quadratic_of_three_normal_witnesses
    QuadraticLowDimension.quadratic_twelve_all
  intro h hh hm
  obtain ⟨s, rfl⟩ : ∃ s, h = 8 + 3 * s := ⟨(h - 8) / 3, by omega⟩
  obtain ⟨F⟩ := TripleNormal.exists_flagWitness_of_initial F₈ s
  exact ⟨F.cone, F.normal_surjective, F.trace_surjective,
    TripleNormal.quadratic_tripleNormal_middle_bijective _ hm F.cone
      F.normal_surjective F.trace_surjective F.middle_injective⟩

/-- The finite low-dimensional cases and the supported even witnesses prove the cubic case. -/
theorem idealGenerationAt_cubic :
    ∀ n p, 1 ≤ n → IdealGenerationAt K n 3 p :=
  cubic_all_dimensions_of_even_middle idealGenerationAt_quadratic
    (cubic_through_eleven_variables_of_quadratic (fun n hn _ p => idealGenerationAt_quadratic n p hn))
    (cubicEvenMiddleWitness_all K)

/-- General points have maximal-rank multiplication in the initial degree. -/
theorem idealGenerationConjecture : IdealGenerationConjecture K := by
  intro n d p hn hd _ _
  exact allPointCounts_of_quadratic_and_cubic idealGenerationAt_quadratic
    idealGenerationAt_cubic d hd n hn p

/-- Theorem 1.1 with its tensor multiplication and minimal homogeneous generators. -/
theorem theorem_one_one : TheoremOneOne K :=
  theoremOneOne_of_idealGenerationConjecture idealGenerationConjecture

end IdealGeneration
