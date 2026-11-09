module

public import IdealGeneration.TripleNormalEnlargement
public import IdealGeneration.TripleNormalFlagInitial
public import IdealGeneration.TripleNormalInitialCertified
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The certified three-normal quadratic step with the paper's field hypotheses. -/
namespace IdealGeneration.TripleNormal

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Appendix A.4. The critical quadratic assertion for the smaller trace
implies the critical assertion after adding three normal variables. -/
theorem quadratic_three_normal_step (h : ℕ) (hh : 8 ≤ h) (hmod : h % 3 = 2)
    (htrace : IdealGenerationAt K (h + 3) 2 ((h + 4) * (h + 5) / 3)) :
    IdealGenerationAt K (h + 6) 2 ((h + 7) * (h + 8) / 3) := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 3 K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos 3 K (by decide)))
  have hprimitive := (Polynomial.isRoot_cyclotomic_iff_charZero (by decide : 0 < 3)).mp hω
  exact quadratic_three_normal_step_of_initial
    (flagEight_of_certificate ω hprimitive TripleNormalInitial.initialCertificate) h hh hmod htrace

end IdealGeneration.TripleNormal
