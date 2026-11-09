module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


namespace CertifiedRank

variable {R : Type*} [Semiring R] {n : Nat}

abbrev SparseRow (n : Nat) (R : Type*) := List (Fin n × R)

/-- Repeated indices are permitted and their coefficients add. -/
def rowValue (r : SparseRow n R) (j : Fin n) : R :=
  (r.map fun e => if e.1 = j then e.2 else 0).sum

/-- Add one sparse entry to a dense, array-backed accumulator. -/
def addEntry (v : Vector R n) (e : Fin n × R) : Vector R n :=
  v.set e.1 (v[e.1] + e.2)

/-- Linear-time sparse accumulation, with one vector update per nonzero. -/
def accumulate (r : SparseRow n R) (v : Vector R n) : Vector R n :=
  r.foldl addEntry v

theorem addEntry_get (v : Vector R n) (e : Fin n × R) (j : Fin n) :
    (addEntry v e)[j] = v[j] + if e.1 = j then e.2 else 0 := by
  change (v.set e.1.val (v[e.1.val] + e.2) e.1.isLt)[j.val] =
    v[j.val] + if e.1 = j then e.2 else 0
  rw [Vector.getElem_set e.1.isLt j.isLt]
  by_cases h : e.1 = j
  · simp [h]
  · have hv : e.1.val ≠ j.val := fun hv => h (Fin.ext hv)
    simp [h, hv]

theorem accumulate_get (r : SparseRow n R) (v : Vector R n) (j : Fin n) :
    (accumulate r v)[j] = v[j] + rowValue r j := by
  induction r generalizing v with
  | nil => simp [accumulate, rowValue]
  | cons e r ih =>
    change (accumulate r (addEntry v e))[j] = v[j] + rowValue (e :: r) j
    rw [ih, addEntry_get]
    simp [rowValue, add_assoc]

def rowVector (r : SparseRow n R) : Vector R n :=
  accumulate r (Vector.replicate n 0)

theorem rowVector_get (r : SparseRow n R) (j : Fin n) :
    (rowVector r)[j] = rowValue r j := by
  rw [rowVector, accumulate_get]
  simp

/-- Sparse expansion of a row multiplied by a sparse-row matrix. -/
def multiplyRow (r : SparseRow n R) (A : Fin n → SparseRow n R) : SparseRow n R :=
  r.flatMap fun e => (A e.1).map fun f => (f.1, e.2 * f.2)

theorem rowValue_scale (a : R) (r : SparseRow n R) (j : Fin n) :
    rowValue (r.map fun e => (e.1, a * e.2)) j = a * rowValue r j := by
  induction r with
  | nil => simp [rowValue]
  | cons e r ih =>
    simp only [rowValue, List.map_cons, List.sum_cons] at *
    rw [ih, mul_add]
    split_ifs <;> simp_all

theorem rowValue_append (a b : SparseRow n R) (j : Fin n) :
    rowValue (a ++ b) j = rowValue a j + rowValue b j := by
  simp [rowValue]

theorem multiplyRow_get (r : SparseRow n R) (A : Fin n → SparseRow n R) (j : Fin n) :
    (rowVector (multiplyRow r A))[j] = ∑ k, rowValue r k * rowValue (A k) j := by
  rw [rowVector_get]
  induction r with
  | nil => simp [multiplyRow, rowValue]
  | cons e r ih =>
    simp only [multiplyRow, List.flatMap_cons, rowValue_append]
    rw [rowValue_scale]
    simp only [multiplyRow] at ih
    rw [ih]
    simp only [rowValue, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    simp

/-- Sparse natural rows interpreted over the desired residue ring. -/
def residueMatrix (p : Nat) {m n : Nat} (rows : Fin m → SparseRow n Nat) :
    Matrix (Fin m) (Fin n) (ZMod p) :=
  fun i j => ((rowValue (rows i) j : Nat) : ZMod p)

/-- Compute an entire product row over the naturals, then reduce every entry once. -/
def productRowResidues (p : Nat) (r : SparseRow n Nat)
    (A : Fin n → SparseRow n Nat) : Vector Nat n :=
  (rowVector (multiplyRow r A)).map (fun x => x % p)

def rowResidues (p : Nat) (r : SparseRow n Nat) : Vector Nat n :=
  (rowVector r).map (fun x => x % p)

theorem checked_product_row (p : Nat) (r : SparseRow n Nat)
    (A : Fin n → SparseRow n Nat) (target : SparseRow n Nat)
    (h : productRowResidues p r A = rowResidues p target) (j : Fin n) :
    (∑ k, ((rowValue r k : Nat) : ZMod p) * ((rowValue (A k) j : Nat) : ZMod p)) =
      ((rowValue target j : Nat) : ZMod p) := by
  have hj := congrArg (fun v : Vector Nat n => (v[j] : ZMod p)) h
  simp only [productRowResidues, rowResidues, Fin.getElem_fin,
    Vector.getElem_map (fun x : Nat => x % p) j.isLt, ZMod.natCast_mod] at hj
  have hm := congrArg (fun x : Nat => (x : ZMod p)) (multiplyRow_get r A j)
  simp only [Nat.cast_sum, Nat.cast_mul] at hm
  exact hm.symm.trans (hj.trans (congrArg (fun x : Nat => (x : ZMod p))
    (rowVector_get target j)))

/-- Whole-matrix consequence of the row checker. -/
theorem checked_product (p : Nat) (L U target : Fin n → SparseRow n Nat)
    (h : ∀ i, productRowResidues p (L i) U = rowResidues p (target i)) :
    residueMatrix p L * residueMatrix p U = residueMatrix p target := by
  ext i j
  exact checked_product_row p (L i) U (target i) (h i) j

theorem rowValue_eq_zero (r : SparseRow n Nat) (j : Fin n)
    (h : ∀ e ∈ r, e.1 ≠ j) : rowValue r j = 0 := by
  induction r with
  | nil => simp [rowValue]
  | cons e r ih =>
    have he : e.1 ≠ j := h e (by simp)
    have hr : ∀ a ∈ r, a.1 ≠ j := fun a ha => h a (by simp [ha])
    change (if e.1 = j then e.2 else 0) + rowValue r j = 0
    rw [ite_eq_right he, ih hr, zero_add]

theorem lower_of_support (p : Nat) (rows : Fin n → SparseRow n Nat)
    (h : ∀ i, (rows i).all (fun e => decide (e.1 ≤ i)) = true) :
    (residueMatrix p rows).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have he : ∀ e ∈ rows i, e.1 ≠ j := by
    intro e heq heval
    have hle : e.1 ≤ i := of_decide_eq_true ((List.all_eq_true.mp (h i)) e heq)
    exact (not_le_of_gt hij) (heval ▸ hle)
  simp only [residueMatrix, rowValue_eq_zero (rows i) j he, Nat.cast_zero]

theorem upper_of_support (p : Nat) (rows : Fin n → SparseRow n Nat)
    (h : ∀ i, (rows i).all (fun e => decide (i ≤ e.1)) = true) :
    (residueMatrix p rows).IsUpperTriangular := by
  intro i j hij
  have he : ∀ e ∈ rows i, e.1 ≠ j := by
    intro e heq heval
    have hle : i ≤ e.1 := of_decide_eq_true ((List.all_eq_true.mp (h i)) e heq)
    exact (not_le_of_gt hij) (heval ▸ hle)
  simp only [residueMatrix, rowValue_eq_zero (rows i) j he, Nat.cast_zero]

theorem diagonal_ne_zero (p : Nat) (rows : Fin n → SparseRow n Nat)
    (h : ∀ i, rowValue (rows i) i % p ≠ 0) :
    ∀ i, residueMatrix p rows i i ≠ 0 := by
  intro i hz
  have hd : p ∣ rowValue (rows i) i :=
    (ZMod.natCast_eq_zero_iff (rowValue (rows i) i) p).mp hz
  exact h i (Nat.dvd_iff_mod_eq_zero.mp hd)

/-- Reindexing sparse column labels computes the inverse column action. -/
theorem rowValue_reindex (sigma tau : Fin n → Fin n)
    (hleft : Function.LeftInverse sigma tau)
    (hright : Function.LeftInverse tau sigma)
    (r : SparseRow n Nat) (j : Fin n) :
    rowValue (r.map (fun e => (sigma e.1, e.2))) j = rowValue r (tau j) := by
  unfold rowValue
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  have he : sigma e.1 = j ↔ e.1 = tau j := by
    constructor
    · intro h
      exact (hright e.1).symm.trans (congrArg tau h)
    · intro h
      exact (congrArg sigma h).trans (hleft j)
  simp only [Function.comp_apply, he]

/-- Sparse reindexing agrees with the standard matrix submatrix operation. -/
theorem residueMatrix_reindex {m k : Nat} (p : Nat)
    (rows : Fin m → SparseRow n Nat) (selected : Fin k → Fin m)
    (sigma tau : Fin n → Fin n)
    (hleft : Function.LeftInverse sigma tau)
    (hright : Function.LeftInverse tau sigma) :
    residueMatrix p (fun i => (rows (selected i)).map (fun e => (sigma e.1, e.2))) =
      (residueMatrix p rows).submatrix selected tau := by
  ext i j
  exact congrArg (fun x : Nat => (x : ZMod p))
    (rowValue_reindex sigma tau hleft hright (rows (selected i)) j)

end CertifiedRank

#print axioms CertifiedRank.checked_product
#print axioms CertifiedRank.residueMatrix_reindex
