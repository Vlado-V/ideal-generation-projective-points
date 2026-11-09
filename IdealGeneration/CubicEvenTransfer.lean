module

public import IdealGeneration.ConeMiddleOpen
public import IdealGeneration.ConeChart
public import IdealGeneration.CubicSupportedCounts
public import IdealGeneration.CubicInductionNumerics
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The cubic transfer from an actual even cone witness -/

noncomputable section
namespace IdealGeneration
open MvPolynomial ConeParameterSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- A marked cone with the Appendix B.1 counts and an injective actual
middle multiplication map. The index is the number of trace variables. -/
def CubicEvenMiddleWitness (K : Type*) [Field K] (m : ℕ) : Prop :=
  ∃ (p q : ℕ) (C : ConeConfiguration K 2 m p q),
    4 * p = 3 * (m + 2) ^ 2 ∧ 4 * q = 3 * N m 3 ∧
      Function.Injective (C.middleMultiplication 3)

variable {K : Type*} [Field K]

/-- The B.5 support counts turn an injective supported middle map into the
actual marked witness used by the dimension induction. -/
theorem cubicEvenMiddleWitness_of_supported
    (k : ℕ) (P : CubicSupported.Parameters K (10 + 2 * k))
    (hs : P.single = CubicSupported.B5.single)
    (free : Fin (CubicSupported.B5.freeCount k) → Fin (10 + 2 * k) → K)
    (hmiddle : Function.Injective ((P.toConeConfiguration free).middleMultiplication 3)) :
    CubicEvenMiddleWitness K (10 + 2 * k) := by
  refine ⟨_, _, P.toConeConfiguration free, ?_, CubicSupported.B5.four_mul_card_traceLabel k, hmiddle⟩
  rw [CubicSupported.B5.card_coneLabel_even k P hs]
  ring

/-- The special cone's middle injection meets the inductive trace open,
giving the integral cubic critical count and hence every ambient count. -/
theorem cubic_twoVariable_transfer_of_middle [CharZero K]
    (m : ℕ) (hm : 2 ≤ m)
    (hcone : CubicEvenMiddleWitness K m)
    (htrace : ∀ q, IdealGenerationAt K (m - 1) 3 q) :
    ∀ p, IdealGenerationAt K (m + 1) 3 p := by
  cases m with
  | zero => omega
  | succ n =>
    have hn : 1 ≤ n := by omega
    obtain ⟨p, q, C, hp, hq, hmiddle⟩ := hcone
    have hqle : q ≤ N (n + 1) 3 := by omega
    have hcrit := E_cubic_eq_of_three_fourths (n + 1) q hq
    obtain ⟨D, hD, hDgood⟩ := idealGenerationAt_injective_open hn hqle
      (le_of_eq hcrit.symm) (htrace q)
    obtain ⟨H, hH, hHgood⟩ := HomogeneousTraceOpen.exists_homogeneous_trace_open D hD
    have hencode : Function.Injective ((configuration C.support (encode C)).middleMultiplication 3) := by
      cases C
      exact hmiddle
    obtain ⟨P, hP, hPgood⟩ := ConeMiddleFamily.middle_injective_principal_open
      C.support (encode C) 3 hencode
    obtain ⟨a, haP, haH, han, _⟩ := compatible_trace_open_nonzero (fun _ => 0) P
      ⟨encode C, hP⟩ H hH
    obtain ⟨hat, haD⟩ := hHgood (traceCoordinates a) haH
    let C' := configuration C.support a
    have hnormal (i : Fin p) : C'.normal i ≠ 0 := by
      intro hi
      exact han i (congrFun hi 0)
    have htraceRep (i : Fin q) : C'.trace i ≠ 0 := by
      intro hi
      exact hat i (congrFun hi (Fin.last n))
    have htraceMul : Function.Injective (C'.traceMultiplication 3) := by
      apply (normalization_multiplication_injective_iff C'.trace (d := 3) hat).mpr
      exact (hDgood _ haD).2.2
    have hactual : IdealGenerationAt K (n + 2) 3 (p + q) := by
      have h := C'.idealGenerationAt_of_injective_blocks (by omega)
        (C'.representatives_ne_zero hnormal htraceRep) htraceMul (hPgood a haP)
      simpa only [show 2 + (n + 1) - 1 = n + 2 by omega] using h
    have hcount : N (n + 3) 3 = N (n + 1) 3 + (n + 3) ^ 2 :=
      cubic_N_add_two (n + 1)
    have hsum : 4 * (p + q) = 3 * N (n + 3) 3 := by
      change 4 * p = 3 * (n + 3) ^ 2 at hp
      omega
    have hambient := E_cubic_eq_of_three_fourths (n + 3) (p + q) hsum
    have hcounts : lowerCritical (n + 3) 3 = N (n + 3) 3 - (p + q) ∧
        upperCritical (n + 3) 3 = N (n + 3) 3 - (p + q) := by
      simp [lowerCritical, upperCritical, hambient]
    have hpoints : p + q ≤ N (n + 3) 3 := by omega
    have hcriticalI : IdealGenerationAt K (n + 2) 3
        (N (n + 3) 3 - lowerCritical (n + 3) 3) := by
      rw [show lowerCritical (n + 3) 3 = N (n + 3) 3 - (p + q) from hcounts.1,
        Nat.sub_sub_self hpoints]
      exact hactual
    have hcriticalS : IdealGenerationAt K (n + 2) 3
        (N (n + 3) 3 - upperCritical (n + 3) 3) := by
      rw [show upperCritical (n + 3) 3 = N (n + 3) 3 - (p + q) from hcounts.2,
        Nat.sub_sub_self hpoints]
      exact hactual
    exact idealGenerationAt_all_of_critical (by omega) (by omega) hcriticalI hcriticalS

end IdealGeneration
