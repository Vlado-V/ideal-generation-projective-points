module

public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CertifiedPackedBounds
public import Mathlib.Data.List.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.B7RootCertificate

open CertifiedRank Matrix

variable {n : Nat}

/-- Decode a fixed number of little-endian quotient digits. -/
def decodeQuotients : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, code => code % (2 ^ 30) :: decodeQuotients count (code / (2 ^ 30))

theorem decodeQuotients_length (count code : Nat) : (decodeQuotients count code).length = count := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih => simp [decodeQuotients, ih]

theorem decodeQuotients_all_lt (count code : Nat) :
    ((decodeQuotients count code).all fun q => decide (q < 2 ^ 30)) = true := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
    simpa only [decodeQuotients, List.all_cons, ih, Bool.and_true, decide_eq_true_eq]
      using (Nat.mod_lt code (by decide : 0 < 2 ^ 30))

def identityRows (i : Fin n) : SparseRow n Nat := [(i, 1)]

private theorem identityRows_value_le_one (i j : Fin n) : rowValue (identityRows i) j ≤ 1 := by
  by_cases h : i = j <;> simp [identityRows, rowValue, h]

private theorem identityRows_residue : residueMatrix 1009 (identityRows (n := n)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [identityRows, residueMatrix, rowValue, Matrix.one_apply, h]

abbrev BoundedRow (r : SparseRow n Nat) : Prop :=
  r.length ≤ n ∧ (r.all fun e => decide (e.2 < 1009)) = true

private theorem boundedRow_coeff {r : SparseRow n Nat} (h : BoundedRow r) :
    ∀ e ∈ r, e.2 < 1009 := fun e he => of_decide_eq_true ((List.all_eq_true.mp h.2) e he)

/-- One finite row certificate for a right inverse over the residue field. -/
structure InverseRowCertificate (A B : Fin n → SparseRow n Nat)
    (packed quotient : Fin n → Nat) (i : Fin n) : Prop where
  matrixBound : BoundedRow (A i)
  inverseBound : BoundedRow (B i)
  upperEncoding : packed i = packSparse (2 ^ 40) (B i)
  productIdentity : packedProduct (A i) packed =
    packSparse (2 ^ 40) (identityRows i) + 1009 * Nat.ofDigits (2 ^ 40) (decodeQuotients n (quotient i))

theorem forall_fin_of_rows [NeZero n] {P : Fin n → Prop}
    (h : List.Forall (fun j => P (Fin.ofNat n j)) (List.range n)) : ∀ i, P i := by
  intro i
  have hi : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hi ▸ (List.forall_iff_forall_mem.mp h i.val (List.mem_range.mpr i.isLt))

/-- Bounded packed row checks establish a matrix right inverse. -/
theorem checked_right_inverse (A B : Fin n → SparseRow n Nat)
    (packed quotient : Fin n → Nat) (hBound : n ^ 2 * 1009 ^ 2 < 2 ^ 40)
    (h : ∀ i, InverseRowCertificate A B packed quotient i) :
    residueMatrix 1009 A * residueMatrix 1009 B = 1 := by
  have hProduct (i j : Fin n) : rowValue (multiplyRow (A i) B) j < 2 ^ 40 :=
    (rowValue_multiplyRow_le_dimension_sq_mul (A i) B j 1009
      (h i).matrixBound.1 (boundedRow_coeff (h i).matrixBound)
      (fun k => (h k).inverseBound.1) (fun k => boundedRow_coeff (h k).inverseBound)).trans_lt hBound
  exact (checked_packed_product (n := n) 1009 (2 ^ 40) (2 ^ 30) 1
    (by decide +kernel) (by decide +kernel) A B identityRows packed (fun i => decodeQuotients n (quotient i))
    (fun i => (h i).upperEncoding) hProduct identityRows_value_le_one
    (fun i => decodeQuotients_length n (quotient i))
    (fun i => decodeQuotients_all_lt n (quotient i)) (fun i => (h i).productIdentity)).trans identityRows_residue

end IdealGeneration.CubicSupported.B7RootCertificate
