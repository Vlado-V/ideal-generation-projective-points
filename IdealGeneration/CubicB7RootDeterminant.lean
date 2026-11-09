module

public import IdealGeneration.CubicB7RootFormula

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Modular-to-characteristic-zero transfer for the actual C.2 pool blocks. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B7Root

open B5 CubicRationalFormula

local instance rootPrime : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

private theorem evalPolynomial_zero_as_cast {σ K : Type*} [Field K]
    (p : MvPolynomial σ ℤ) :
    evalPolynomial (fun _ => (0 : K)) p = (MvPolynomial.eval (fun _ => (0 : ℤ)) p : K) := by
  rw [evalPolynomial]
  symm
  change Int.castRingHom K (MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun _ => (0 : ℤ)) p) = _
  simp only [MvPolynomial.map_eval₂Hom, RingHom.comp_id, map_zero]

private theorem evalPolynomial_zero_ne_zero_of_mod {σ K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial σ ℤ) (h : evalPolynomial (fun _ => (0 : ZMod 1009)) p ≠ 0) :
    evalPolynomial (fun _ => (0 : K)) p ≠ 0 := by
  rw [evalPolynomial_zero_as_cast, Int.cast_ne_zero]
  intro hz
  exact h (by rw [evalPolynomial_zero_as_cast, hz, Int.cast_zero])

variable {K : Type*} [Field K] [CharZero K]

def diagonal0 (Q : Parameters K 12) : Matrix (Fin 86) (Fin 86) K :=
  fun i j => probeEntry (actualB7Data Q) (probe0 K i) (column0 j)

def diagonal1 (Q : Parameters K 12) : Matrix (Fin 74) (Fin 74) K :=
  fun i j => probeEntry (actualB7Data Q) (probe1 K i) (column1 j)

private def modularParameters : Parameters (ZMod 1009) 12 := parameters _ fun _ _ h => h

private theorem block_det_of_mod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : ι → B11ProbeFormula Unit 10) (cols : ι → B7Column 10)
    (probes : ι → B11Probe K 10) (probesMod : ι → B11Probe (ZMod 1009) 10)
    (hrows : ∀ i, (rows i).Matches (fun _ => 0) (probes i))
    (hrowsMod : ∀ i, (rows i).Matches (fun _ => 0) (probesMod i))
    (hmod : (evalMatrix (fun _ => (0 : ZMod 1009))
      (b11FormulaMatrix primitiveFormula single rows cols)).det ≠ 0) :
    (Matrix.of fun i j => probeEntry (actualB7Data (parametersCharZero K)) (probes i) (cols j)).det ≠ 0 := by
  let A := b11FormulaMatrix primitiveFormula single rows cols
  have ha : EntriesAdmissible (fun _ => (0 : ZMod 1009)) A :=
    (b11FormulaMatrix_spec modularParameters _ primitiveFormula
      (primitiveFormula_matches _ _) rows probesMod cols hrowsMod).1
  have hz := (eval_matrixCertificate_ne_zero_iff _ A).mpr ⟨ha, hmod⟩
  apply (eval_b11Certificate_ne_zero_iff (parametersCharZero K) (fun _ => 0)
    primitiveFormula (primitiveFormula_matches _ _) rows probes cols hrows).mp
  exact evalPolynomial_zero_ne_zero_of_mod (matrixCertificate A) hz

omit [CharZero K] in
private theorem probeEntry_wrong_direction (Q : Parameters K 12) (y : Fin 10 → K)
    (b r : Fin 2) (c : B7Column 10) (hc : b7Direction c ≠ b) :
    probeEntry (actualB7Data Q) ⟨y, pureDirection b, r⟩ c = 0 := by
  rw [probeEntry, b7Value_actual_eq_oldValue]
  cases c <;> simp_all [b7Direction, b7OldValue, localValue, pureDirection]

omit [CharZero K] in
theorem poolMatrix_eq_blocks (Q : Parameters K 12) :
    poolMatrix (actualB7Data Q) (pool K) =
      Matrix.fromBlocks (diagonal0 Q) 0 0 (diagonal1 Q) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · change probeEntry (actualB7Data Q) (probe0 K i) (column1 j) = 0
    apply probeEntry_wrong_direction
    rw [column1_direction]
    decide
  · change probeEntry (actualB7Data Q) (probe1 K i) (column0 j) = 0
    apply probeEntry_wrong_direction
    rw [column0_direction]
    decide
  · rfl

/-- Two finite-field determinants certify the concrete characteristic-zero pool. -/
theorem pool_det_ne_zero_of_mod
    (h0 : (evalMatrix (fun _ => (0 : ZMod 1009)) formula0).det ≠ 0)
    (h1 : (evalMatrix (fun _ => (0 : ZMod 1009)) formula1).det ≠ 0) :
    (poolMatrix (actualB7Data (parametersCharZero K)) (pool K)).det ≠ 0 := by
  have hd0 : (diagonal0 (parametersCharZero K)).det ≠ 0 :=
    block_det_of_mod rowFormula0 column0 (probe0 K) (probe0 _)
      (rowFormula0_matches _) (rowFormula0_matches _) h0
  have hd1 : (diagonal1 (parametersCharZero K)).det ≠ 0 :=
    block_det_of_mod rowFormula1 column1 (probe1 K) (probe1 _)
      (rowFormula1_matches _) (rowFormula1_matches _) h1
  rw [poolMatrix_eq_blocks, Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero hd0 hd1

end IdealGeneration.CubicSupported.B7Root
