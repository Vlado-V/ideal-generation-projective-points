module

public import IdealGeneration.TripleNormalInitialData
public import IdealGeneration.ConeMonomialChart
public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CertifiedPackedBounds
public import IdealGeneration.TripleNormalInitialBasisData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace IdealGeneration.TripleNormalInitial
open MvPolynomial ConeMonomialChart CertifiedRank
open scoped BigOperators

private theorem prod_two_powers {n : ℕ} (x : Fin n → ModField) (a b : Fin n) :
    (∏ k, x k ^ ((Finsupp.single a 1 + Finsupp.single b 1 : Fin n →₀ ℕ) k)) = x a * x b := by
  have hsingle (c : Fin n) : (∏ k, x k ^ (Finsupp.single c (1 : ℕ)) k) = x c := by
    rw [Finset.prod_eq_single c]
    · simp
    · intro k _ hk
      rw [Finsupp.single_eq_of_ne hk, pow_zero]
    · simp
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, hsingle]

def denseRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ModField)
    (i : Fin m) : SparseRow n ℕ :=
  List.ofFn fun j => (j, (A i j).val)

private theorem rowValue_denseRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ModField)
    (i : Fin m) (j : Fin n) : rowValue (denseRow A i) j = (A i j).val := by
  simp [denseRow, rowValue, List.sum_ofFn]

private theorem denseRow_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ModField)
    (i : Fin m) (e : Fin n × ℕ) (he : e ∈ denseRow A i) : e.2 ≤ 1009 := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
  exact (ZMod.val_lt (A i j)).le

def radix : ℕ := 4294967296
def quotientBound : ℕ := 1048576

def packDenseRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ModField) (i : Fin m) : ℕ :=
  Nat.ofDigits radix (List.ofFn fun j => (A i j).val)

private theorem packSparse_denseRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ModField)
    (i : Fin m) : packSparse radix (denseRow A i) = packDenseRow A i := by
  rw [packSparse_eq_packCoefficients, packCoefficients]
  exact congrArg (Nat.ofDigits radix)
    (congrArg (fun f : Fin n → ℕ => List.ofFn f) (funext (rowValue_denseRow A i)))

/-- Verify an entire modular product with exact packed row certificates. -/
theorem checkedDenseProduct {m n : ℕ} (hn : n ≤ 52)
    (A : Matrix (Fin m) (Fin n) ModField) (B : Matrix (Fin n) (Fin n) ModField)
    (C : Matrix (Fin m) (Fin n) ModField)
    (packedB : Fin n → ℕ) (quotients : Fin m → List ℕ)
    (hB : ∀ j, packedB j = packDenseRow B j)
    (hLength : ∀ i, (quotients i).length = n)
    (hBound : ∀ i, ((quotients i).all fun q => decide (q < quotientBound)) = true)
    (hCheck : ∀ i, packedProduct (denseRow A i) packedB =
      packDenseRow C i + 1009 * Nat.ofDigits radix (quotients i)) :
    A * B = C := by
  ext i j
  rw [Matrix.mul_apply]
  have hprod (k : Fin n) :
      rowValue (multiplyRow (denseRow A i) (denseRow B)) k < radix := by
    apply (rowValue_multiplyRow_le_length_mul (denseRow A i) (denseRow B) k 1009 1009
      (denseRow_bounded A i) (fun l => by rw [rowValue_denseRow]; exact (ZMod.val_lt _).le)).trans_lt
    simp only [denseRow, List.length_ofFn]
    exact (Nat.mul_le_mul_right _ hn).trans_lt (by decide)
  have htarget (k : Fin n) : rowValue (denseRow C i) k ≤ 1009 := by
    rw [rowValue_denseRow]
    exact (ZMod.val_lt _).le
  have h := checked_packed_product_row 1009 radix quotientBound 1009 (by decide) (by decide)
    (denseRow A i) (denseRow B) packedB (denseRow C i) (quotients i)
    (fun k => (hB k).trans (packSparse_denseRow B k).symm) hprod htarget
    (hLength i) (hBound i) (by rw [packSparse_denseRow]; exact hCheck i) j
  simpa only [rowValue_denseRow, ZMod.natCast_zmod_val] using h


set_option maxRecDepth 20000
set_option maxHeartbeats 0

attribute [local simp] Polynomial.eval₂_pow

local instance : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

@[local simp] private theorem omegaSq : (139876 : ModField) = (374 : ModField)^2 := by
  decide +kernel

/-- The actual cone evaluation in the selected pivot/free ordering. -/
noncomputable def normalEvaluationMod : Matrix (Fin 28) (Fin 28 ⊕ Fin 14) ModField :=
  evaluationMatrix (configuration (374 : ModField)).point normalExponent

/-- The actual trace evaluation in the selected pivot/free ordering. -/
noncomputable def traceEvaluationMod : Matrix (Fin 52) (Fin 52 ⊕ Fin 26) ModField :=
  evaluationMatrix (configuration (374 : ModField)).trace traceExponent

noncomputable def normalPivotMod : Matrix (Fin 28) (Fin 28) ModField :=
  normalEvaluationMod.submatrix id Sum.inl

noncomputable def tracePivotMod : Matrix (Fin 52) (Fin 52) ModField :=
  traceEvaluationMod.submatrix id Sum.inl

private def baseNormalFast (i : Fin 8) (branch : Fin 2) (j : Fin 3) : ModField :=
  let t : ModField := (i.val + 1 : ℕ)
  let w : ModField := 374
  if branch = 0 then
    -(w ^ 2) * (![w ^ 2 * t ^ 2, w * t, 1] : Fin 3 → ModField) j
  else
    w * (![w * t ^ 2, w ^ 2 * t, 1] : Fin 3 → ModField) j

private def normalFast (i : Fin 28) (j : Fin 3) : ModField :=
  Fin.addCases (fun k : Fin 16 =>
    let ib := (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin 16).symm k
    baseNormalFast ib.1 ib.2 j)
    (fun k : Fin 12 =>
      let ji := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).symm k
      (table2Normal ji.1 ji.2 j : ModField)) i

private theorem eval_baseNormal_eq_fast (i : Fin 8) (branch : Fin 2) (j : Fin 3) :
    (baseNormalPolynomial i branch j).eval₂ (Int.castRingHom ModField) 374 =
      baseNormalFast i branch j := by
  unfold baseNormalPolynomial baseNormalFast
  dsimp only
  split_ifs <;> fin_cases j <;> simp

private theorem eval_normal_eq_fast (i : Fin 28) (j : Fin 3) :
    (normalPolynomial i j).eval₂ (Int.castRingHom ModField) 374 = normalFast i j := by
  refine Fin.addCases (motive := fun i =>
    (normalPolynomial i j).eval₂ (Int.castRingHom ModField) 374 = normalFast i j)
    (fun k : Fin 16 => ?_) (fun k : Fin 12 => ?_) i
  · simp only [normalPolynomial, normalFast, Fin.addCases_left, eval_baseNormal_eq_fast]
  · simp [normalPolynomial, normalFast]

def pointFast (i : Fin 28) (j : Fin 15) : ModField :=
  Fin.addCases (normalFast i) (fun k => (traceIntegers (support i) k : ModField)) j

theorem point_eq_fast (i : Fin 28) (j : Fin 15) :
    (configuration (374 : ModField)).point i j = pointFast i j := by
  rw [configuration_point_eq_eval]
  refine Fin.addCases (motive := fun j =>
    (pointPolynomial i j).eval₂ (Int.castRingHom ModField) 374 = pointFast i j)
    (fun k : Fin 3 => ?_) (fun k : Fin 12 => ?_) j
  · simp only [pointPolynomial, pointFast, Fin.addCases_left, eval_normal_eq_fast]
  · simp [pointPolynomial, pointFast]

private def normalFastEval (i : Fin 28) (j : Fin 42) : ModField :=
  let k := normalQuadraticTuple j
  pointFast i (k.1.castAdd 12) * pointFast i k.2

private def traceFastEval (i : Fin 52) (j : Fin 78) : ModField :=
  let k := traceQuadraticTuple j
  (traceIntegers i k.1 : ModField) * (traceIntegers i k.2 : ModField)

private theorem normalEvaluationMod_apply_fast (i : Fin 28) (j : Fin 28 ⊕ Fin 14) :
    normalEvaluationMod i j = normalFastEval i (normalColumn j) := by
  unfold normalEvaluationMod evaluationMatrix normalExponent normalExponentLex normalFastEval
  rw [prod_two_powers, point_eq_fast, point_eq_fast]

private theorem traceEvaluationMod_apply_fast (i : Fin 52) (j : Fin 52 ⊕ Fin 26) :
    traceEvaluationMod i j = traceFastEval i (traceColumn j) := by
  unfold traceEvaluationMod evaluationMatrix traceExponent traceExponentLex traceFastEval
  rw [prod_two_powers]
  rfl

def normalPivotFast : Matrix (Fin 28) (Fin 28) ModField :=
  fun i j => normalFastEval i (normalPivots j)

def tracePivotFast : Matrix (Fin 52) (Fin 52) ModField :=
  fun i j => traceFastEval i (tracePivots j)

theorem normalPivot_eq_fast : normalPivotMod = normalPivotFast := by
  ext i j
  exact normalEvaluationMod_apply_fast i (.inl j)

theorem tracePivot_eq_fast : tracePivotMod = tracePivotFast := by
  ext i j
  exact traceEvaluationMod_apply_fast i (.inl j)

def padRight {m n s : ℕ} (A : Matrix (Fin m) (Fin s) ModField) :
    Matrix (Fin m) (Fin n) ModField :=
  fun i j => if h : j.val < s then A i ⟨j.val, h⟩ else 0

@[simp] private theorem padRight_castLE {m n s : ℕ} (A : Matrix (Fin m) (Fin s) ModField)
    (hs : s ≤ n) (i : Fin m) (j : Fin s) : padRight A i (j.castLE hs) = A i j := by
  simp [padRight, j.isLt]

/-- Add the identity free rows to a pivot-coordinate kernel block. -/
def normalizedBlock {n s : ℕ} (P : Matrix (Fin n) (Fin s) ModField) :
    Matrix (Fin n ⊕ Fin s) (Fin s) ModField :=
  fun i j => Sum.elim (fun k => P k j) (fun k => if k = j then 1 else 0) i

theorem kernel_zero_of_padded {m n s : ℕ} (hs : s ≤ n)
    (A : Matrix (Fin m) (Fin n ⊕ Fin s) ModField)
    (P : Matrix (Fin n) (Fin s) ModField)
    (h : A.submatrix id Sum.inl * padRight (n := n) P =
      padRight (n := n) (-(A.submatrix id Sum.inr))) :
    A * normalizedBlock P = 0 := by
  ext i j
  have hc := congrArg (fun M : Matrix (Fin m) (Fin n) ModField => M i (j.castLE hs)) h
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, padRight_castLE, Matrix.neg_apply] at hc
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [normalizedBlock, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.zero_apply]
  rw [hc, neg_add_cancel]

def normalKernelPivotFast : Matrix (Fin 28) (Fin 14) ModField :=
  fun i j => normalKernelPivotValues i j

def traceKernelPivotFast : Matrix (Fin 52) (Fin 26) ModField :=
  fun i j => traceKernelPivotValues i j

def normalFreeFast : Matrix (Fin 28) (Fin 14) ModField :=
  fun i j => normalFastEval i (normalFree j)

def traceFreeFast : Matrix (Fin 52) (Fin 26) ModField :=
  fun i j => traceFastEval i (traceFree j)

theorem normalFree_eq_fast : normalEvaluationMod.submatrix id Sum.inr = normalFreeFast := by
  ext i j
  exact normalEvaluationMod_apply_fast i (.inr j)

theorem traceFree_eq_fast : traceEvaluationMod.submatrix id Sum.inr = traceFreeFast := by
  ext i j
  exact traceEvaluationMod_apply_fast i (.inr j)

end IdealGeneration.TripleNormalInitial
