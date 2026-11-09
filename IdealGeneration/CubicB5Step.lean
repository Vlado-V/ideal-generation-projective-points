module

public import IdealGeneration.CubicB4Step
public import IdealGeneration.CubicB11RowIndices
public import IdealGeneration.CubicB11PoolCounts
public import IdealGeneration.CubicB22Rows
public import IdealGeneration.CubicSupportedCounts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The B.5 blocks give the genuine pair step with its exact free-point count. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open Module CubicUpperSolve B4 B22

variable {K : Type*} [Field K] {k : ℕ}
local notation "m" => 10 + 2 * k
variable (P : Parameters K (10 + 2 * k)) (Q : Parameters K ((10 + 2 * k) + 2))
variable (hP : P.single = single) (hQ : Q.single = single)
variable (h : Compatible P Q)
variable (old : Fin (freeCount k) → Fin (10 + 2 * k) → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

private theorem sourceCount_eq_allowed (j : ℕ) (R : Parameters K (10 + 2 * j))
    (hs : R.single = single) :
    finrank K R.EliminatedParameters = Fintype.card R.SingleEdge + 2 * freeCount j := by
  rw [R.finrank_eliminatedParameters, ← R.finrank_coefficientKernel,
    eliminatedParameterCount_eq j R hs, ← finrank_allowedValues_even j R hs (fun _ => 0),
    R.finrank_allowedValues]

private theorem newSource_finrank (h : Compatible P Q) :
    finrank K P.EliminatedParameters + finrank K h.restrictParameters.ker =
      finrank K Q.EliminatedParameters := by
  let _ : AddCommGroup Q.EliminatedParameters := Module.addCommMonoidToAddCommGroup K
  let _ : AddCommGroup P.EliminatedParameters := Module.addCommMonoidToAddCommGroup K
  let _ : FiniteDimensional K Q.coefficientKernel := FiniteDimensional.finiteDimensional_submodule _
  let _ : FiniteDimensional K (Omega Q.cubicTop) := FiniteDimensional.finiteDimensional_submodule _
  let _ : FiniteDimensional K Q.EliminatedParameters := by
    change FiniteDimensional K (Omega Q.cubicTop ×
      (Edge (m + 2) → Fin 3 → K) × (Fin (m + 2) → Q.SingleEdge → K))
    infer_instance
  have hdim := h.restrictParameters.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h.restrictParameters_surjective, finrank_top] at hdim
  exact hdim

include hP hQ in
private theorem freeCount_eq_of_indexing {A B : Type*} [Fintype A] [Fintype B] {n l : ℕ}
    (nearIndex : A ≃ Fin n × Fin 2)
    (fixedIndex : B ≃ NewIncidence Q ⊕ (Fin l × Fin 2))
    (basis : Basis (A ⊕ B) K h.restrictParameters.ker)
    (hpair : Q.single (newPairEdge m) = false) :
    freeCount k + (n + l) = freeCount (k + 1) := by
  have hdim := newSource_finrank P Q h
  have hA : Fintype.card A = n * 2 := by
    rw [Fintype.card_congr nearIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hB : Fintype.card B = Fintype.card (NewIncidence Q) + l * 2 := by
    rw [Fintype.card_congr fixedIndex, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  have hI : Fintype.card Q.SingleEdge = Fintype.card P.SingleEdge + Fintype.card (NewIncidence Q) := by
    rw [Fintype.card_congr (h.singleEdgeExtensionEquiv hpair), Fintype.card_sum]
  have hQcount : finrank K Q.EliminatedParameters =
      Fintype.card Q.SingleEdge + 2 * freeCount (k + 1) :=
    sourceCount_eq_allowed (k + 1) Q hQ
  rw [finrank_eq_card_basis basis, Fintype.card_sum, hA, hB,
    sourceCount_eq_allowed k P hP, hQcount, hI] at hdim
  omega

variable [Infinite K]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
variable (poolIndex : J ≃ I × Fin 2)
variable (poolPoint : I → Fin (10 + 2 * k) → K) (poolWeight : I → Fin 2 → K)
variable (R : PoolBlockData K (10 + 2 * k) J) (D : ∀ j : Fin k, PairBlockData K k j)
variable {r : ℕ} (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)
variable (probes : Fin 2 → Fin 3 → K)

include hP hQ h h₂ h₆ in
open Classical in
/-- The pool, pair, and fixed higher witnesses produce the actual enlarged middle map. -/
theorem exists_b5_step_of_witnesses
    (hold : Function.Injective ((P.toConeConfiguration old).middleMultiplication 3))
    (hcard : Fintype.card J = 160)
    (hpool : ∀ j, R.probe j = ⟨poolPoint (poolIndex j).1, poolWeight (poolIndex j).1, (poolIndex j).2⟩)
    (hD : ∀ j, (D j).coreColumn = canonicalPairCoreColumn j)
    (hR : (poolMatrix (actualB7Data Q) R).det ≠ 0)
    (hE : ∀ j, (pairCoreMatrix (actualB7Data Q) (D j)).det ≠ 0)
    (hτ : Set.InjOn (fun e : Edge (m + 2) => Q.edgeSlope e 0) {e | single e = true})
    (h22 : (fixedHigherMatrix Q pairing probes).det ≠ 0) :
    ∃ free' : Fin (freeCount (k + 1)) → Fin (m + 2) → K,
      Function.Injective ((Q.toConeConfiguration free').middleMultiplication 3) := by
  let a := actualB7Data Q
  have h11 := det_b11Matrix_ne_zero a R D hR hE hτ
  let low := b11ColumnEquiv D a R hD (poolColumn_coverage_of_det a R hcard hR) h11
  let nearIndex := b11NearIndex (k := k) poolIndex
  let fixedIndex := B22.fixedIndex Q pairing
  let near := b11NearPoint D poolPoint
  let weight := b11NearWeight D poolWeight
  let far := B22.farPoint Q pairing probes
  let base : Fin 0 → Fin (m + 2) → K := fun i => i.elim0
  have hpair := b5_newPair_double k Q hQ
  have h₁₁ : (Matrix.of (fun i j => probeEntry a (nearEnumeration near weight nearIndex i)
      (low j)) : Matrix (B11ScalarIndex J k) (B11ScalarIndex J k) K).det ≠ 0 := by
    change (Matrix.of (fun i j => probeEntry a
      (nearEnumeration (b11NearPoint D poolPoint) (b11NearWeight D poolWeight) (b11NearIndex poolIndex) i)
      (b11Column D R j)) : Matrix (B11ScalarIndex J k) (B11ScalarIndex J k) K).det ≠ 0
    rw [← b11Matrix_eq_nearEnumeration D poolPoint poolWeight poolIndex a R hpool]
    exact h11
  have h₂₂ : (Matrix.of (fun i j => fixedValue Q base h₂ h₆ (fixedEnumeration Q far fixedIndex i)
      (highParameter Q j)) : Matrix (HigherColumn Q) (HigherColumn Q) K).det ≠ 0 := by
    rw [← fixedHigherMatrix_eq_actual Q pairing base h₂ h₆ probes]
    exact h22
  obtain ⟨eps, _, hinj⟩ :=
    exists_supported_pair_step old near weight far base h₂ h₆ nearIndex fixedIndex low (Equiv.refl _)
      h (fun e => congrFun hP e) (fun e => congrFun hQ e) hpair hold h₁₁ h₂₂
  have hold' := (P.middleMultiplication_injective_iff_markedEvaluation old h₂ h₆).mp hold
  let basis := (h.actualNewBasis (fun e => congrFun hP e) (fun e => congrFun hQ e)
    old h₂ h₆ hpair hold').reindex (Equiv.sumCongr low (Equiv.refl _)).symm
  have hc := freeCount_eq_of_indexing P Q hP hQ h nearIndex fixedIndex basis hpair
  rw [← hc]
  exact ⟨enlargedFree old near weight far eps, hinj⟩

end IdealGeneration.CubicSupported.B5
