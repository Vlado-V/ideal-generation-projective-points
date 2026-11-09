module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A weighted leading matrix detects a nonsingular specialization. -/
namespace IdealGeneration.TripleNormal

open Matrix Polynomial

variable {K ι : Type*} [Field K] [Infinite K] [Fintype ι] [DecidableEq ι]

/-- Reverse the entries at a degree bound that is the sum of row and column weights.
The resulting constant matrix detects nonsingularity of the original polynomial matrix. -/
theorem exists_specialization_of_weightedLeading_det_ne_zero
    (A : Matrix ι ι (Polynomial K)) (r c : ι → ℕ)
    (hdeg : ∀ i j, (A i j).natDegree ≤ r i + c j)
    (hdet : (of fun i j => (A i j).coeff (r i + c j)).det ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ (A.map (evalRingHom x)).det ≠ 0 := by
  let B : Matrix ι ι (Polynomial K) := of fun i j => reflect (r i + c j) (A i j)
  have hB0 : B.map (evalRingHom 0) = of fun i j => (A i j).coeff (r i + c j) := by
    ext i j
    change (reflect (r i + c j) (A i j)).eval 0 = (A i j).coeff (r i + c j)
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]
  have hB : B.det ≠ 0 := by
    intro hz
    apply hdet
    have hmap := (evalRingHom (0 : K)).map_det B
    change evalRingHom (0 : K) B.det = (B.map (evalRingHom 0)).det at hmap
    rw [← hB0, ← hmap, hz, map_zero]
  obtain ⟨x, hx, hBx⟩ : ∃ x : K, x ≠ 0 ∧ (B.map (evalRingHom x)).det ≠ 0 := by
    by_contra! h
    have hzero : X * B.det = 0 := by
      apply Polynomial.funext
      intro x
      rw [eval_mul, eval_X, eval_zero]
      by_cases hx : x = 0
      · rw [hx, zero_mul]
      · have he : B.det.eval x = 0 := by
          change evalRingHom x B.det = 0
          rw [(evalRingHom x).map_det]
          exact h x hx
        rw [he, mul_zero]
    exact (mul_ne_zero X_ne_zero hB) hzero
  let dr : ι → K := fun i => x⁻¹ ^ r i
  let dc : ι → K := fun j => x⁻¹ ^ c j
  have hscale : A.map (evalRingHom x⁻¹) =
      (diagonal dr * B.map (evalRingHom x)) * diagonal dc := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    change (A i j).eval x⁻¹ = (x⁻¹ ^ r i * (reflect (r i + c j) (A i j)).eval x) * x⁻¹ ^ c j
    let : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
    have he := eval₂_reflect_mul_pow (RingHom.id K) x⁻¹ (r i + c j) (A i j) (hdeg i j)
    simp only [invOf_eq_inv, inv_inv, eval₂_id, pow_add] at he
    rw [← he]
    ring
  refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
  rw [hscale]
  simp only [det_mul, det_diagonal]
  exact mul_ne_zero (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (inv_ne_zero hx)) hBx)
    (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (inv_ne_zero hx))

/-- The weighted leading matrix of the monomial-curve evaluations has
entries only at rows that meet a column's maximal exponent. -/
theorem exists_interpolation_of_weightedLeading
    (f : ι → Fin 3 → Polynomial K) (rowBlock : ι → ℕ) (rowCoordinate : ι → Fin 3)
    (degree r c : ι → ℕ)
    (hdeg : ∀ j a, (f j a).natDegree ≤ degree j)
    (hweight : ∀ i j, (rowBlock i + 1) * degree j ≤ r i + c j)
    (hdet : (Matrix.of fun i j =>
      if r i + c j = (rowBlock i + 1) * degree j
      then (f j (rowCoordinate i)).coeff (degree j) else 0).det ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ (Matrix.of fun i j =>
      (f j (rowCoordinate i)).eval (x ^ (rowBlock i + 1))).det ≠ 0 := by
  let A : Matrix ι ι (Polynomial K) :=
    Matrix.of fun i j => expand K (rowBlock i + 1) (f j (rowCoordinate i))
  have hd (i j : ι) : (A i j).natDegree ≤ (rowBlock i + 1) * degree j := by
    change (expand K (rowBlock i + 1) (f j (rowCoordinate i))).natDegree ≤ _
    rw [natDegree_expand, Nat.mul_comm (rowBlock i + 1)]
    exact Nat.mul_le_mul_right _ (hdeg j (rowCoordinate i))
  have hc : (Matrix.of fun i j => (A i j).coeff (r i + c j)) =
      Matrix.of fun i j => if r i + c j = (rowBlock i + 1) * degree j
        then (f j (rowCoordinate i)).coeff (degree j) else 0 := by
    ext i j
    change (A i j).coeff (r i + c j) =
      if r i + c j = (rowBlock i + 1) * degree j then (f j (rowCoordinate i)).coeff (degree j) else 0
    split_ifs with he
    · rw [he]
      exact coeff_expand_mul' (Nat.succ_pos _) _ _
    · exact coeff_eq_zero_of_natDegree_lt
        ((hd i j).trans_lt (lt_of_le_of_ne (hweight i j) (Ne.symm he)))
  obtain ⟨x, hx, hA⟩ := exists_specialization_of_weightedLeading_det_ne_zero A r c
    (fun i j => (hd i j).trans (hweight i j)) (hc.symm ▸ hdet)
  have he : A.map (evalRingHom x) = Matrix.of fun i j =>
      (f j (rowCoordinate i)).eval (x ^ (rowBlock i + 1)) := by
    ext i j
    change (expand K (rowBlock i + 1) (f j (rowCoordinate i))).eval x =
      (f j (rowCoordinate i)).eval (x ^ (rowBlock i + 1))
    rw [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X]
  exact ⟨x, hx, he ▸ hA⟩

/-- Row weights for successive blocks separated by the indicated degree thresholds. -/
def blockThresholdWeight (threshold : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ k ∈ Finset.range i, threshold k

/-- The leading entries of a degree-`d` column occur in its assigned row
block and precisely in the adjacent blocks whose intervening thresholds equal `d`. -/
theorem exists_columnWeight_for_thresholds (threshold : ℕ → ℕ) (j d : ℕ)
    (hlo : ∀ k < j, threshold k ≤ d) (hhi : ∀ k, j ≤ k → d ≤ threshold k) :
    ∃ c : ℕ, ∀ i : ℕ,
      (i + 1) * d ≤ blockThresholdWeight threshold i + c ∧
      (blockThresholdWeight threshold i + c = (i + 1) * d ↔
        ∀ k ∈ Finset.Ico (min i j) (max i j), threshold k = d) := by
  let r := blockThresholdWeight threshold
  have hbound : r j ≤ (j + 1) * d := calc
    r j ≤ ∑ _ ∈ Finset.range j, d :=
      Finset.sum_le_sum fun k hk => hlo k (Finset.mem_range.mp hk)
    _ = j * d := by simp
    _ ≤ (j + 1) * d := Nat.mul_le_mul_right d (Nat.le_succ _)
  let c := (j + 1) * d - r j
  have hbase : r j + c = (j + 1) * d := by dsimp only [c]; omega
  refine ⟨c, fun i => ?_⟩
  change (i + 1) * d ≤ r i + c ∧
    (r i + c = (i + 1) * d ↔ ∀ k ∈ Finset.Ico (min i j) (max i j), threshold k = d)
  by_cases hij : i ≤ j
  · rw [min_eq_left hij, max_eq_right hij]
    have hp : r i + ∑ k ∈ Finset.Ico i j, threshold k = r j :=
      Finset.sum_range_add_sum_Ico _ hij
    have hd : (i + 1) * d + (j - i) * d = (j + 1) * d := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hl (k : ℕ) (hk : k ∈ Finset.Ico i j) : threshold k ≤ d :=
      hlo k (Finset.mem_Ico.mp hk).2
    have hc : (∑ _ ∈ Finset.Ico i j, d) = (j - i) * d := by simp
    have hle : (∑ k ∈ Finset.Ico i j, threshold k) ≤ (j - i) * d :=
      (Finset.sum_le_sum hl).trans_eq hc
    refine ⟨by omega, ?_, ?_⟩
    · intro he k hk
      by_contra hn
      have hlt := (Finset.sum_lt_sum hl ⟨k, hk, lt_of_le_of_ne (hl k hk) hn⟩).trans_eq hc
      omega
    · intro he
      have hs : (∑ k ∈ Finset.Ico i j, threshold k) = (j - i) * d :=
        (Finset.sum_congr rfl he).trans hc
      omega
  · have hji : j ≤ i := by omega
    rw [min_eq_right hji, max_eq_left hji]
    have hp : r j + ∑ k ∈ Finset.Ico j i, threshold k = r i :=
      Finset.sum_range_add_sum_Ico _ hji
    have hd : (j + 1) * d + (i - j) * d = (i + 1) * d := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hl (k : ℕ) (hk : k ∈ Finset.Ico j i) : d ≤ threshold k :=
      hhi k (Finset.mem_Ico.mp hk).1
    have hc : (∑ _ ∈ Finset.Ico j i, d) = (i - j) * d := by simp
    have hle : (i - j) * d ≤ ∑ k ∈ Finset.Ico j i, threshold k :=
      hc.symm.trans_le (Finset.sum_le_sum hl)
    refine ⟨by omega, ?_, ?_⟩
    · intro he k hk
      by_contra hn
      have hlt := hc.symm.trans_lt (Finset.sum_lt_sum hl
        ⟨k, hk, lt_of_le_of_ne (hl k hk) (Ne.symm hn)⟩)
      omega
    · intro he
      have hs : (∑ k ∈ Finset.Ico j i, threshold k) = (i - j) * d :=
        (Finset.sum_congr rfl he).trans hc
      omega

end IdealGeneration.TripleNormal
