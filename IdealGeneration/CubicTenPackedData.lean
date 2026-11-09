module

public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CertifiedPackedBounds
public import Mathlib.Tactic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Packed arithmetic interface for the ten-variable cubic witness

The generated certificates use sparse rows and decimal natural numbers. This
module turns exact packed equalities into statements about matrices over
`ZMod 1009`. The geometric identification of those matrices is separate.
-/

namespace IdealGeneration.CubicTenPackedData
open CertifiedRank

abbrev modulus : ℕ := 1009
abbrev radix : ℕ := 2 ^ 40
abbrev quotientRadix : ℕ := 2 ^ 15

theorem modulus_prime : Nat.Prime modulus := by decide +kernel
local instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- A complete binary table. Low bits of the index choose branches. -/
@[reducible] def Table (A : Type*) : ℕ → Type _
  | 0 => A
  | depth + 1 => Table A depth × Table A depth

/-- A logarithmic lookup in the generated fixed table. -/
def tableGet {A : Type*} : (depth : ℕ) → Table A depth → ℕ → A
  | 0, value, _ => value
  | depth + 1, children, index =>
    if index % 2 = 0 then tableGet depth children.1 (index / 2)
    else tableGet depth children.2 (index / 2)

/-- Decode one sparse entry. The low residue is bounded by construction. -/
def decodeEntry (n : ℕ) [NeZero n] (code : ℕ) : Fin n × ℕ :=
  (⟨(code / modulus) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩,
    code % modulus)

/-- Sparse rows have at most `n` entries and use residues below `modulus`. -/
def decodeRow (n : ℕ) [NeZero n] (codes : List ℕ) : SparseRow n ℕ :=
  (codes.take n).map (decodeEntry n)

theorem decodeRow_length (n : ℕ) [NeZero n] (codes : List ℕ) :
    (decodeRow n codes).length ≤ n := by
  simp only [decodeRow, List.length_map, List.length_take]
  omega

theorem decodeRow_coeff (n : ℕ) [NeZero n] (codes : List ℕ) :
    ∀ e ∈ decodeRow n codes, e.2 < modulus := by
  intro e he
  obtain ⟨code, _, rfl⟩ := List.mem_map.mp he
  exact Nat.mod_lt _ (by decide)

/-- Decode a fixed number of quotient digits, including trailing zeros. -/
def decodeQuotient : ℕ → ℕ → List ℕ
  | 0, _ => []
  | count + 1, code => code % quotientRadix :: decodeQuotient count (code / quotientRadix)

theorem decodeQuotient_length (count code : ℕ) :
    (decodeQuotient count code).length = count := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih => simp [decodeQuotient, ih]

theorem decodeQuotient_all_lt (count code : ℕ) :
    ((decodeQuotient count code).all fun q => decide (q < quotientRadix)) = true := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
    simpa only [decodeQuotient, List.all_cons, ih, Bool.and_true, decide_eq_true_eq]
      using Nat.mod_lt code (by decide : 0 < quotientRadix)

/-- The data needed to certify a square product, with zero-padding when used
for a rectangular product. -/
structure Tables (n : ℕ) where
  lowerCode : Fin n → List ℕ
  upperCode : Fin n → List ℕ
  targetCode : Fin n → List ℕ
  packedUpper : Fin n → ℕ
  quotientCode : Fin n → ℕ

/-- One leaf of the generated table. -/
structure RawRow where
  lower : List ℕ
  upper : List ℕ
  target : List ℕ
  packed : ℕ
  quotient : ℕ

/-- Use one balanced lookup for each field of the sparse certificate. -/
def fromRawTable (n depth : ℕ) (table : Table RawRow depth) : Tables n where
  lowerCode i := (tableGet depth table i.val).lower
  upperCode i := (tableGet depth table i.val).upper
  targetCode i := (tableGet depth table i.val).target
  packedUpper i := (tableGet depth table i.val).packed
  quotientCode i := (tableGet depth table i.val).quotient

namespace Tables

variable {n : ℕ} [NeZero n] (T : Tables n)

def lower (i : Fin n) : SparseRow n ℕ := decodeRow n (T.lowerCode i)
def upper (i : Fin n) : SparseRow n ℕ := decodeRow n (T.upperCode i)
def target (i : Fin n) : SparseRow n ℕ := decodeRow n (T.targetCode i)
def quotient (i : Fin n) : List ℕ := decodeQuotient n (T.quotientCode i)

/-- The two closed packed identities checked at a single row. -/
def ValidAt (i : Fin n) : Prop :=
  T.packedUpper i = packSparse radix (T.upper i) ∧
    packedProduct (T.lower i) T.packedUpper =
      packSparse radix (T.target i) + modulus * Nat.ofDigits radix (T.quotient i)

/-- Closed support and diagonal conditions for a triangular factorization. -/
def TriangularAt (i : Fin n) : Prop :=
  (T.lower i).all (fun e => decide (e.1 ≤ i)) = true ∧
  (T.upper i).all (fun e => decide (i ≤ e.1)) = true ∧
  rowValue (T.lower i) i % modulus ≠ 0 ∧ rowValue (T.upper i) i % modulus ≠ 0

/-- Checked packed products are true matrix products modulo 1009. -/
theorem checked_product (hn : n ≤ 310) (h : ∀ i, T.ValidAt i) :
    residueMatrix modulus T.lower * residueMatrix modulus T.upper =
      residueMatrix modulus T.target := by
  have hbound : n * modulus + modulus * quotientRadix < radix := by
    have hmul := Nat.mul_le_mul_right modulus hn
    norm_num [modulus, quotientRadix, radix] at hmul ⊢
    omega
  have hproduct (i j : Fin n) : rowValue (multiplyRow (T.lower i) T.upper) j < radix := by
    have hrow := rowValue_multiplyRow_le_dimension_sq_mul (T.lower i) T.upper j modulus
      (decodeRow_length n (T.lowerCode i)) (decodeRow_coeff n (T.lowerCode i))
      (fun k => decodeRow_length n (T.upperCode k))
      (fun k => decodeRow_coeff n (T.upperCode k))
    have hsq : n ^ 2 ≤ 310 ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hn hn
    exact (hrow.trans (Nat.mul_le_mul_right _ hsq)).trans_lt (by decide)
  exact checked_packed_product modulus radix quotientRadix (n * modulus) (by decide) hbound
    T.lower T.upper T.target T.packedUpper T.quotient (fun i => (h i).1) hproduct
    (fun i j => rowValue_le_dimension_mul (T.target i) j modulus
      (decodeRow_length n (T.targetCode i)) (decodeRow_coeff n (T.targetCode i)))
    (fun i => decodeQuotient_length _ _) (fun i => decodeQuotient_all_lt _ _)
    (fun i => (h i).2)

/-- A verified triangular factorization proves that the target minor is nonsingular. -/
theorem target_det_ne_zero (hn : n ≤ 310) (h : ∀ i, T.ValidAt i)
    (htri : ∀ i, T.TriangularAt i) : (residueMatrix modulus T.target).det ≠ 0 := by
  have hl := lower_of_support modulus T.lower (fun i => (htri i).1)
  have hu := upper_of_support modulus T.upper (fun i => (htri i).2.1)
  have hld := diagonal_ne_zero modulus T.lower (fun i => (htri i).2.2.1)
  have hud := diagonal_ne_zero modulus T.upper (fun i => (htri i).2.2.2)
  rw [← T.checked_product hn h, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ hl, Matrix.det_of_isUpperTriangular hu]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hld i)
    (Finset.prod_ne_zero_iff.mpr fun i _ => hud i)

end Tables

/-- Assemble proofs for adjacent intervals without linear-depth case splitting. -/
theorem finSplit {l r : ℕ} {P : Fin (l + r) → Prop}
    (left : ∀ i : Fin l, P (Fin.castAdd r i))
    (right : ∀ i : Fin r, P (Fin.natAdd l i)) : ∀ i, P i :=
  Fin.addCases left right

/-- A proof at zero covers a one-element interval. -/
theorem finOne {P : Fin 1 → Prop} (h : P 0) : ∀ i, P i := by
  intro i
  exact (Subsingleton.elim (0 : Fin 1) i) ▸ h

end IdealGeneration.CubicTenPackedData
