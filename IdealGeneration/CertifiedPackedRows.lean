module

public import IdealGeneration.CertifiedSparseRow
public import Mathlib.Data.Nat.Digits.Defs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Packed natural-number row certificates

A packed dot product computes an entire sparse product row. A list of
quotient digits certifies the modular result by one natural-number equality.
The bounds on both sides prevent carries between columns.
-/

namespace CertifiedRank

variable {n : Nat}

/-- Evaluate a sparse row as a little-endian radix expansion. -/
def packSparse (base : Nat) (row : SparseRow n Nat) : Nat :=
  (row.map fun entry => entry.2 * base ^ entry.1.val).sum

/-- Multiply one sparse row by a matrix of already packed rows. -/
def packedProduct (row : SparseRow n Nat) (packedUpper : Fin n → Nat) : Nat :=
  (row.map fun entry => entry.2 * packedUpper entry.1).sum

/-- The radix expansion of a dense row. -/
def packCoefficients (base : Nat) (coeff : Fin n → Nat) : Nat :=
  Nat.ofDigits base (List.ofFn coeff)

theorem packCoefficients_eq_sum (base : Nat) (coeff : Fin n → Nat) :
    packCoefficients base coeff = ∑ j, coeff j * base ^ j.val := by
  induction n with
  | zero => simp [packCoefficients]
  | succ n ih =>
    rw [packCoefficients, List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ]
    change coeff 0 + base * packCoefficients base (fun j : Fin n => coeff j.succ) = _
    rw [ih]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem packCoefficients_add (base : Nat) (f g : Fin n → Nat) :
    packCoefficients base (fun j => f j + g j) =
      packCoefficients base f + packCoefficients base g := by
  simp only [packCoefficients_eq_sum, add_mul, Finset.sum_add_distrib]

theorem packCoefficients_mul (base scalar : Nat) (f : Fin n → Nat) :
    packCoefficients base (fun j => scalar * f j) =
      scalar * packCoefficients base f := by
  simp only [packCoefficients_eq_sum, Finset.mul_sum, mul_assoc]

/-- Sparse and dense radix expansions represent the same row, including
when the sparse representation repeats a column. -/
theorem packSparse_eq_packCoefficients (base : Nat) (row : SparseRow n Nat) :
    packSparse base row = packCoefficients base (rowValue row) := by
  rw [packCoefficients_eq_sum]
  induction row with
  | nil => simp [packSparse, rowValue]
  | cons entry row ih =>
    change entry.2 * base ^ entry.1.val + packSparse base row = _
    rw [ih]
    simp only [rowValue, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single entry.1]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

theorem packSparse_append (base : Nat) (r s : SparseRow n Nat) :
    packSparse base (r ++ s) = packSparse base r + packSparse base s := by
  simp [packSparse]

theorem packSparse_scale (base scalar : Nat) (row : SparseRow n Nat) :
    packSparse base (row.map fun entry => (entry.1, scalar * entry.2)) =
      scalar * packSparse base row := by
  induction row with
  | nil => simp [packSparse]
  | cons entry row ih =>
    change scalar * entry.2 * base ^ entry.1.val +
      packSparse base (row.map fun e => (e.1, scalar * e.2)) =
        scalar * (entry.2 * base ^ entry.1.val + packSparse base row)
    rw [ih, mul_add, mul_assoc]

/-- The packed dot product is the radix expansion of the ordinary natural
product row. -/
theorem packedProduct_eq_packSparse (base : Nat) (row : SparseRow n Nat)
    (upper : Fin n → SparseRow n Nat) (packedUpper : Fin n → Nat)
    (hUpper : ∀ i, packedUpper i = packSparse base (upper i)) :
    packedProduct row packedUpper = packSparse base (multiplyRow row upper) := by
  induction row with
  | nil => simp [packedProduct, multiplyRow, packSparse]
  | cons entry row ih =>
    change entry.2 * packedUpper entry.1 + packedProduct row packedUpper =
      packSparse base ((upper entry.1).map (fun e => (e.1, entry.2 * e.2)) ++
        multiplyRow row upper)
    rw [hUpper, ih, packSparse_append, packSparse_scale]

/-- Read one digit from a packed natural number. -/
def packedDigit (base packed index : Nat) : Nat := packed / base ^ index % base

/-- A bounded coefficient row is recovered by reading the digits of its
radix expansion. -/
theorem packedDigit_packCoefficients (base : Nat) (hBase : 0 < base)
    (coeff : Fin n → Nat) (hCoeff : ∀ j, coeff j < base) (query : Fin n) :
    packedDigit base (packCoefficients base coeff) query.val = coeff query := by
  induction n with
  | zero => exact Fin.elim0 query
  | succ n ih =>
    rw [packCoefficients, List.ofFn_succ, Nat.ofDigits_cons]
    refine Fin.cases ?_ (fun j => ?_) query
    · simp [packedDigit, Nat.mod_eq_of_lt (hCoeff 0)]
    · let tail : Fin n → Nat := fun i => coeff i.succ
      have hDiv : (coeff 0 + base * packCoefficients base tail) / base =
          packCoefficients base tail := by
        rw [Nat.add_mul_div_left _ _ hBase, Nat.div_eq_of_lt (hCoeff 0), zero_add]
      change packedDigit base (coeff 0 + base * packCoefficients base tail) j.succ.val = _
      rw [packedDigit, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, hDiv]
      exact ih tail (fun i => hCoeff i.succ) j

/-- One exact packed equality and bounded quotient digits verify the product
row modulo `p`. The bounds ensure every column occupies exactly one digit. -/
theorem checked_packed_product_row (p base qBound targetBound : Nat)
    (hBase : 0 < base) (hBound : targetBound + p * qBound < base)
    (row : SparseRow n Nat) (upper : Fin n → SparseRow n Nat)
    (packedUpper : Fin n → Nat) (target : SparseRow n Nat) (quotient : List Nat)
    (hUpper : ∀ i, packedUpper i = packSparse base (upper i))
    (hProduct : ∀ j, rowValue (multiplyRow row upper) j < base)
    (hTarget : ∀ j, rowValue target j ≤ targetBound)
    (hLength : quotient.length = n)
    (hQuotient : (quotient.all fun q => decide (q < qBound)) = true)
    (hCheck : packedProduct row packedUpper =
      packSparse base target + p * Nat.ofDigits base quotient)
    (query : Fin n) :
    (∑ k, ((rowValue row k : Nat) : ZMod p) *
      ((rowValue (upper k) query : Nat) : ZMod p)) =
      ((rowValue target query : Nat) : ZMod p) := by
  subst n
  let q : Fin quotient.length → Nat := fun j => quotient[j.val]
  have hq (j : Fin quotient.length) : q j < qBound := by
    apply of_decide_eq_true
    exact (List.all_eq_true.mp hQuotient) (q j) (List.getElem_mem j.isLt)
  have hqPack : packCoefficients base q = Nat.ofDigits base quotient := by
    simp [packCoefficients, q]
  have hRight : packCoefficients base (fun j => rowValue target j + p * q j) =
      packSparse base target + p * Nat.ofDigits base quotient := by
    rw [packCoefficients_add, packCoefficients_mul, ← packSparse_eq_packCoefficients, hqPack]
  have hLeft : packedProduct row packedUpper =
      packCoefficients base (rowValue (multiplyRow row upper)) :=
    (packedProduct_eq_packSparse base row upper packedUpper hUpper).trans
      (packSparse_eq_packCoefficients base (multiplyRow row upper))
  have hDigits : packCoefficients base (rowValue (multiplyRow row upper)) =
      packCoefficients base (fun j => rowValue target j + p * q j) :=
    hLeft.symm.trans (hCheck.trans hRight.symm)
  have hRightBound (j : Fin quotient.length) : rowValue target j + p * q j < base :=
    (Nat.add_le_add (hTarget j) (Nat.mul_le_mul_left p (Nat.le_of_lt (hq j)))).trans_lt hBound
  have hCoeff := congrArg (fun value => packedDigit base value query.val) hDigits
  rw [packedDigit_packCoefficients base hBase _ hProduct query,
    packedDigit_packCoefficients base hBase _ hRightBound query] at hCoeff
  have hMod := congrArg (fun value : Nat => (value : ZMod p)) hCoeff
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hMod
  have hMul := congrArg (fun value : Nat => (value : ZMod p))
    (multiplyRow_get row upper query)
  simp only [rowVector_get, Nat.cast_sum, Nat.cast_mul] at hMul
  exact hMul.symm.trans hMod

/-- Applying the packed certificate row by row proves a matrix product. -/
theorem checked_packed_product (p base qBound targetBound : Nat)
    (hBase : 0 < base) (hBound : targetBound + p * qBound < base)
    (lower upper target : Fin n → SparseRow n Nat)
    (packedUpper : Fin n → Nat) (quotients : Fin n → List Nat)
    (hUpper : ∀ i, packedUpper i = packSparse base (upper i))
    (hProduct : ∀ i j, rowValue (multiplyRow (lower i) upper) j < base)
    (hTarget : ∀ i j, rowValue (target i) j ≤ targetBound)
    (hLength : ∀ i, (quotients i).length = n)
    (hQuotient : ∀ i, ((quotients i).all fun q => decide (q < qBound)) = true)
    (hCheck : ∀ i, packedProduct (lower i) packedUpper =
      packSparse base (target i) + p * Nat.ofDigits base (quotients i)) :
    residueMatrix p lower * residueMatrix p upper = residueMatrix p target := by
  ext i j
  exact checked_packed_product_row p base qBound targetBound hBase hBound
    (lower i) upper packedUpper (target i) (quotients i) hUpper (hProduct i)
    (hTarget i) (hLength i) (hQuotient i) (hCheck i) j

end CertifiedRank
