module

public import IdealGeneration.ConeMiddleOpen
public import IdealGeneration.ConeChart
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A marked ten-variable cubic cone witness suffices for the critical count. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial ConeParameterSpace

variable {K : Type*} [Field K] [CharZero K]

/-- A ten-variable cubic middle witness combines with the generic trace
condition on the same marked cone parameter space. -/
theorem cubic_ten_variables_of_middle_witness
    (htrace : IdealGenerationAt K 7 3 90) (support : Fin 75 → Fin 90)
    (a₀ : Parameters K 2 8 75 90)
    (h₀ : Function.Injective ((configuration support a₀).middleMultiplication 3)) :
    ∀ p, IdealGenerationAt K 9 3 p := by
  obtain ⟨P, hP, hgoodP⟩ := ConeMiddleFamily.middle_injective_principal_open support a₀ 3 h₀
  obtain ⟨D, hD, hgoodD⟩ := idealGenerationAt_injective_open (by decide)
    (by norm_num [N, Nat.choose]) (by norm_num [E, N, Nat.choose]) htrace
  obtain ⟨Δ, hΔ, hgoodΔ⟩ := HomogeneousTraceOpen.exists_homogeneous_trace_open D hD
  obtain ⟨a, haP, haΔ, han, _⟩ := compatible_trace_open_nonzero (fun _ => 0) P ⟨a₀, hP⟩ Δ hΔ
  obtain ⟨hat, haD⟩ := hgoodΔ (traceCoordinates a) haΔ
  let C := configuration support a
  have hnormal : ∀ i, C.normal i ≠ 0 := by
    intro i h
    exact han i (congrFun h 0)
  have htraceRep : ∀ i, C.trace i ≠ 0 := by
    intro i h
    exact hat i (congrFun h (Fin.last 7))
  have htraceMul : Function.Injective (C.traceMultiplication 3) := by
    apply (normalization_multiplication_injective_iff C.trace (d := 3) hat).mpr
    exact (hgoodD _ haD).2.2
  have hcritical : IdealGenerationAt K 9 3 165 :=
    C.idealGenerationAt_of_injective_blocks (by decide)
      (C.representatives_ne_zero hnormal htraceRep) htraceMul (hgoodP a haP)
  apply idealGenerationAt_all_of_critical (by decide) (by decide)
  · have h : lowerCritical 10 3 = 55 := by norm_num [lowerCritical, E, N, Nat.choose]
    simpa only [h, show N 10 3 - 55 = 165 by decide] using hcritical
  · have h : upperCritical 10 3 = 55 := by norm_num [upperCritical, E, N, Nat.choose]
    simpa only [h, show N 10 3 - 55 = 165 by decide] using hcritical

end IdealGeneration
