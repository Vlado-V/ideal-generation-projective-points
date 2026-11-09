module

public import IdealGeneration.CertifiedSparseRow

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace CertifiedRank

variable {n : Nat}

/-- A coefficient in a sparse row is bounded by the sum of the entry bounds. -/
theorem rowValue_le_length_mul (r : SparseRow n Nat) (j : Fin n) (p : Nat)
    (h : ∀ e ∈ r, e.2 ≤ p) : rowValue r j ≤ r.length * p := by
  induction r with
  | nil => simp [rowValue]
  | cons e r ih =>
    have he : (if e.1 = j then e.2 else 0) ≤ p := by
      split
      · exact h e (by simp)
      · exact Nat.zero_le p
    have hr := ih (fun a ha => h a (List.mem_cons_of_mem e ha))
    change (if e.1 = j then e.2 else 0) + rowValue r j ≤ (r.length + 1) * p
    rw [Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add he hr).trans_eq (Nat.add_comm _ _)

/-- A row with at most `n` entries below `p` has coefficients at most `n * p`. -/
theorem rowValue_le_dimension_mul (r : SparseRow n Nat) (j : Fin n) (p : Nat)
    (hlen : r.length ≤ n) (hcoeff : ∀ e ∈ r, e.2 < p) :
    rowValue r j ≤ n * p :=
  (rowValue_le_length_mul r j p (fun e he => Nat.le_of_lt (hcoeff e he))).trans
    (Nat.mul_le_mul_right p hlen)

/-- Bound a product coefficient by the entry bounds of its sparse expansion. -/
theorem rowValue_multiplyRow_le_length_mul (r : SparseRow n Nat)
    (A : Fin n → SparseRow n Nat) (j : Fin n) (p q : Nat)
    (hr : ∀ e ∈ r, e.2 ≤ p) (hA : ∀ k, rowValue (A k) j ≤ q) :
    rowValue (multiplyRow r A) j ≤ r.length * (p * q) := by
  induction r with
  | nil => simp [multiplyRow, rowValue]
  | cons e r ih =>
    have he : e.2 * rowValue (A e.1) j ≤ p * q :=
      Nat.mul_le_mul (hr e (by simp)) (hA e.1)
    have ht := ih (fun a ha => hr a (List.mem_cons_of_mem e ha))
    calc
      rowValue (multiplyRow (e :: r) A) j =
          e.2 * rowValue (A e.1) j + rowValue (multiplyRow r A) j := by
        simp only [multiplyRow, List.flatMap_cons, rowValue_append, rowValue_scale]
      _ ≤ p * q + r.length * (p * q) := Nat.add_le_add he ht
      _ = (e :: r).length * (p * q) := by
        change _ = (r.length + 1) * (p * q)
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_comm _ _

/-- A uniform no-carry bound for multiplication of sparse natural rows. -/
theorem rowValue_multiplyRow_le_dimension_sq_mul (r : SparseRow n Nat)
    (A : Fin n → SparseRow n Nat) (j : Fin n) (p : Nat)
    (hrlen : r.length ≤ n) (hrcoeff : ∀ e ∈ r, e.2 < p)
    (hAlen : ∀ k, (A k).length ≤ n) (hAcoeff : ∀ k, ∀ e ∈ A k, e.2 < p) :
    rowValue (multiplyRow r A) j ≤ n ^ 2 * p ^ 2 := by
  calc
    rowValue (multiplyRow r A) j ≤ r.length * (p * (n * p)) :=
      rowValue_multiplyRow_le_length_mul r A j p (n * p)
        (fun e he => Nat.le_of_lt (hrcoeff e he))
        (fun k => rowValue_le_dimension_mul (A k) j p (hAlen k) (hAcoeff k))
    _ ≤ n * (p * (n * p)) := Nat.mul_le_mul_right _ hrlen
    _ = n ^ 2 * p ^ 2 := by
      simp only [pow_two]
      ac_rfl

end CertifiedRank
