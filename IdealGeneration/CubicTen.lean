module

public import IdealGeneration.CubicTenEvaluationComparison
public import IdealGeneration.CubicTenMiddleComparison
public import IdealGeneration.CubicSmallDimension
public import IdealGeneration.MatrixKernelFree
public import IdealGeneration.CertifiedFiniteRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A checked characteristic-zero witness closes the ten-variable cubic case. -/

noncomputable section
namespace IdealGeneration.CubicTen
open ConeParameterSpace ConeMonomialChart CubicTenPackedData Matrix
local instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

private def tablePermutation (a : Array ℕ) (n : ℕ) [NeZero n] (hs : a.size = n)
    (hn : a.toList.Nodup) (hb : ∀ i : Fin n, a[i.val]! < n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun i => Fin.ofNat n a[i.val]!) <| by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, rfl⟩
    intro i j hij
    apply arrayGet_injective a n hs hn
    have h := congrArg Fin.val hij
    change a[i.val]! % n = a[j.val]! % n at h
    simpa only [Nat.mod_eq_of_lt (hb i), Nat.mod_eq_of_lt (hb j)] using h

private def normalSplitTable : Array ℕ := normalPivotIndices ++ normalFreeIndices
private def traceSplitTable : Array ℕ := tracePivotIndices ++ traceFreeIndices

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def normalSplit : Fin 75 ⊕ Fin 25 ≃ Fin 100 :=
  finSumFinEquiv.trans (tablePermutation normalSplitTable 100
    (by decide) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def traceSplit : Fin 90 ⊕ Fin 30 ≃ Fin 120 :=
  finSumFinEquiv.trans (tablePermutation traceSplitTable 120
    (by decide) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem normalSplit_pivot : (fun i => normalSplit (.inl i)) = normalPivotColumn := by
  funext i
  exact (by decide +kernel : ∀ j, normalSplit (.inl j) = normalPivotColumn j) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem normalSplit_free : (fun i => normalSplit (.inr i)) = normalFreeRow := by
  funext i
  exact (by decide +kernel : ∀ j, normalSplit (.inr j) = normalFreeRow j) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem traceSplit_pivot : (fun i => traceSplit (.inl i)) = tracePivotColumn := by
  funext i
  exact (by decide +kernel : ∀ j, traceSplit (.inl j) = tracePivotColumn j) i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem traceSplit_free : (fun i => traceSplit (.inr i)) = traceFreeRow := by
  funext i
  exact (by decide +kernel : ∀ j, traceSplit (.inr j) = traceFreeRow j) i

private theorem normalKernel_spans (u : Fin 100 → ZMod modulus) (hu : EP.mulVec u = 0) :
    ∃ v, Kn.mulVec v = u := by
  apply MatrixKernelFree.exists_mulVec_eq_of_kernel EP Kn normalSplit _ normal_annihilation _ u hu
  · rw [normalSplit_pivot, normalPivot_eq_submatrix]
    exact mulVec_injective_of_leftInverse normal_pivot_leftInverse
  · rw [normalSplit_free]
    exact normal_free_identity

private theorem traceKernel_spans (u : Fin 120 → ZMod modulus) (hu : ET.mulVec u = 0) :
    ∃ v, Kt.mulVec v = u := by
  apply MatrixKernelFree.exists_mulVec_eq_of_kernel ET Kt traceSplit _ trace_annihilation _ u hu
  · rw [traceSplit_pivot, tracePivot_eq_submatrix]
    exact mulVec_injective_of_leftInverse trace_pivot_leftInverse
  · rw [traceSplit_free]
    exact trace_free_identity

private theorem middleMatrix_injective :
    Function.Injective
      (middleMatrix normalExponent traceExponent quarticExponent Kn Kt).mulVec := by
  intro x y hxy
  have hcert : targetM.mulVec (x ∘ permutedColumn) = targetM.mulVec (y ∘ permutedColumn) := by
    rw [← middle_eq_targetM, Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hxy
  have h := middle_injective hcert
  funext i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    congrFun h (permutedColumn.symm i)

/-- The numerical coefficient certificates verify the actual middle map. -/
theorem middleWitness {K : Type*} [Field K] [CharZero K] :
    Function.Injective ((configuration support (parameters K)).middleMultiplication 3) := by
  apply middle_injective_of_modular_stack modulus
  rw [normalEvaluationMatrix_eq_EP, traceEvaluationMatrix_eq_ET]
  apply jointMatrix_injective_of_kernel_columns (c := 2) (m := 8) _ _ _ _ _
    Kn Kt normalKernel_spans traceKernel_spans
  exact middleMatrix_injective

end IdealGeneration.CubicTen

namespace IdealGeneration

variable {K : Type*} [Field K] [CharZero K]

/-- The certified cone gives cubic ideal generation in ten variables from the
eight-variable cubic trace. -/
theorem cubic_ten_variables
    (htrace : ∀ p, IdealGenerationAt K 7 3 p) : ∀ p, IdealGenerationAt K 9 3 p :=
  cubic_ten_variables_of_middle_witness (htrace 90) CubicTen.support (CubicTen.parameters K)
    CubicTen.middleWitness

/-- Cubic ideal generation through eleven variables follows from quadratic ideal generation. -/
theorem cubic_through_eleven_variables_of_quadratic
    (hquadratic : ∀ n, 1 ≤ n → n ≤ 10 → ∀ p, IdealGenerationAt K n 2 p)
    (n : ℕ) (hn : 1 ≤ n) (hle : n ≤ 10) : ∀ p, IdealGenerationAt K n 3 p := by
  have hsmall : ∀ k, 1 ≤ k → k ≤ 8 → ∀ p, IdealGenerationAt K k 3 p :=
    cubic_through_nine_variables_of_quadratic (fun k hk hle p =>
      hquadratic k hk (by omega) p)
  have h₉ := cubic_ten_variables (hsmall 7 (by decide) (by decide))
  have h₁₀ := cubic_eleven_variables (hquadratic 10 (by decide) (by decide)) h₉
  by_cases h : n ≤ 8
  · exact hsmall n hn h
  · interval_cases n
    · exact h₉
    · exact h₁₀

end IdealGeneration
