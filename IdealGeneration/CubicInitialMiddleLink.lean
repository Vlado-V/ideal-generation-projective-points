module

public import IdealGeneration.CubicInitialMiddleData
public import IdealGeneration.ConeLookupGuards
public import IdealGeneration.CubicInitialMatrixData
public import IdealGeneration.CubicInitialKernelBridge
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The packed C.2 rank certificate concerns the actual product coefficients. -/

noncomputable section

set_option maxRecDepth 50000
set_option maxHeartbeats 900000
namespace IdealGeneration.CubicInitial
open ConeMonomialChart CertifiedRank Matrix Module

local instance middleLinkPrime : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

private theorem rowValue_ofFn_filter {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    rowValue ((List.ofFn fun i => (i, f i)).filter (fun e => e.2 != 0)) j = f j := by
  have h (l : List (Fin n × ℕ)) :
      rowValue (l.filter fun e => e.2 != 0) j = rowValue l j := by
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [rowValue] at ih
      by_cases he : e.2 = 0 <;> simp [he, rowValue, ih]
  rw [h, rowValue, List.map_ofFn, List.sum_ofFn]
  simp

/-- The listed sparse rows are identified with the selected monomial products. -/
theorem actual_middle_matrix_eq
    (hn : ∀ i j, NormalLookupValid (c := 2) (m := 10) normalExponent (quarticExponent i) j (normalLookup i j))
    (ht : ∀ i j, TraceLookupValid (c := 2) (m := 10) traceExponent (quarticExponent i) j (traceLookup i j))
    (hRows : ∀ i, rawMiddleRow i = CertifiedRank.C2.originalRows i) :
    (middleMatrix normalExponent traceExponent quarticExponent normalKernel traceKernel) =
      (residueMatrix 1009 CertifiedRank.C2.originalRows).submatrix id columnChart := by
  ext i a
  change _ = ((rowValue (CertifiedRank.C2.originalRows i) (columnChart a) : ℕ) : ZMod 1009)
  rw [← hRows]
  change _ = ((rowValue
    ((List.ofFn fun j => (j, rawMiddleEntry i j)).filter (fun e => e.2 != 0))
    (columnChart a) : ℕ) : ZMod 1009)
  rw [rowValue_ofFn_filter]
  rcases a with ⟨j, k⟩ | ⟨j, k⟩
  · rw [middleMatrix_apply_inl_of_lookup (c := 2) (m := 10)
      normalExponent traceExponent quarticExponent normalKernel traceKernel i j k (normalLookup i j)
      (normalLookup_iff_of_valid (c := 2) (m := 10) normalExponent normalExponent_injective
        normalExponent_positive (quarticExponent i) j (normalLookup i j) (hn i j))]
    simp only [rawMiddleEntry, Equiv.symm_apply_apply, Sum.elim_inl]
    cases normalLookup i j <;> rfl
  · rw [middleMatrix_apply_inr_of_lookup (c := 2) (m := 10)
      normalExponent traceExponent quarticExponent normalKernel traceKernel i j k (traceLookup i j)
      (traceLookup_iff_of_valid (c := 2) (m := 10) traceExponent traceExponent_injective
        (quarticExponent i) j (traceLookup i j) (ht i j))]
    simp only [rawMiddleEntry, Equiv.symm_apply_apply, Sum.elim_inr]
    cases traceLookup i j <;> rfl

/-- Full column rank of the listed matrix gives injectivity in the actual
normal/trace kernel bases. -/
theorem middle_injective_of_rank
    (hn : ∀ i j, NormalLookupValid (c := 2) (m := 10) normalExponent (quarticExponent i) j (normalLookup i j))
    (ht : ∀ i j, TraceLookupValid (c := 2) (m := 10) traceExponent (quarticExponent i) j (traceLookup i j))
    (hRows : ∀ i, rawMiddleRow i = CertifiedRank.C2.originalRows i)
    (hRank : (residueMatrix 1009 CertifiedRank.C2.originalRows).rank = 542) :
    Function.Injective
      (middleMatrix normalExponent traceExponent quarticExponent normalKernel traceKernel).mulVec := by
  let A := residueMatrix 1009 CertifiedRank.C2.originalRows
  have hA : Function.Injective A.mulVec := by
    apply (LinearMap.ker_eq_bot (f := A.mulVecLin)).mp
    apply Submodule.finrank_eq_zero.mp
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    change A.rank + _ = _ at h
    have hdim : finrank (ZMod 1009) (Fin 542 → ZMod 1009) = 542 := by simp
    change A.rank = 542 at hRank
    rw [hRank, hdim] at h
    omega
  rw [actual_middle_matrix_eq hn ht hRows]
  intro u v huv
  have hu := Matrix.submatrix_mulVec_equiv A u id columnChart
  have hv := Matrix.submatrix_mulVec_equiv A v id columnChart
  have heq : A.mulVec (u ∘ columnChart.symm) = A.mulVec (v ∘ columnChart.symm) := by
    simpa only [Function.comp_id] using hu.symm.trans (huv.trans hv)
  exact (Equiv.surjective columnChart.symm).injective_comp_right (hA heq)

end IdealGeneration.CubicInitial
