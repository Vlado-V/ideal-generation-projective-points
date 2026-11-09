module

public import IdealGeneration.CertifiedPackedRows
public import IdealGeneration.CertifiedPackedBounds
public import IdealGeneration.GenericMatrixDescent

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Compact left-inverse certificates for the integer Euler minors. -/

namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank

variable {r : ℕ}

/-- A digit of a packed nonnegative integer. -/
def certificateDigit (base value index : ℕ) : ℕ := value / base ^ index % base

/-- An integer row interpreted by its least nonnegative residues. -/
def denseResidueRow (A : Matrix (Fin r) (Fin r) ℤ) (p : ℕ) (i : Fin r) :
    SparseRow r ℕ := List.ofFn fun j => (j, (A i j % (p : ℤ)).toNat)

theorem denseResidueRow_value (A : Matrix (Fin r) (Fin r) ℤ) (p : ℕ) (i j : Fin r) :
    rowValue (denseResidueRow A p i) j = (A i j % (p : ℤ)).toNat := by
  rw [rowValue, denseResidueRow, List.map_ofFn, List.sum_ofFn]
  simp

private theorem denseResidueCoefficient_lt (A : Matrix (Fin r) (Fin r) ℤ)
    (p : ℕ) (hp : 0 < p) (i j : Fin r) : (A i j % (p : ℤ)).toNat < p := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hz := Int.emod_nonneg (A i j) (ne_of_gt hpz)
  have hlt : ((A i j % (p : ℤ)).toNat : ℤ) < p := by
    rw [Int.toNat_of_nonneg hz]
    exact Int.emod_lt_of_pos _ hpz
  exact_mod_cast hlt

/-- The computational residue rows agree with ring-homomorphic reduction. -/
theorem residueMatrix_denseResidueRow (A : Matrix (Fin r) (Fin r) ℤ)
    (p : ℕ) (hp : 0 < p) : residueMatrix p (denseResidueRow A p) =
      A.map (Int.castRingHom (ZMod p)) := by
  ext i j
  change ((rowValue (denseResidueRow A p i) j : ℕ) : ZMod p) = (A i j : ZMod p)
  rw [denseResidueRow_value, ← Int.cast_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hp))), ZMod.intCast_mod]

/-- The actual integer row packed in the checking radix after modular reduction. -/
def packedMinorResidueRow (A : Matrix (Fin r) (Fin r) ℤ) (p base : ℕ) (i : Fin r) : ℕ :=
  packCoefficients base (fun j => (A i j % (p : ℤ)).toNat)

theorem packSparse_denseResidueRow (A : Matrix (Fin r) (Fin r) ℤ)
    (p base : ℕ) (i : Fin r) :
    packSparse base (denseResidueRow A p i) = packedMinorResidueRow A p base i := by
  rw [packSparse_eq_packCoefficients, packedMinorResidueRow]
  congr 1
  funext j
  exact denseResidueRow_value A p i j

/-- Decode a row of the proposed inverse from base-`p` digits, omitting zeros. -/
def inverseSparseRow (p : ℕ) (packed : Fin r → ℕ) (i : Fin r) : SparseRow r ℕ :=
  (List.ofFn fun j : Fin r => (j, certificateDigit p (packed i) j.val)).filter
    (fun e => e.2 != 0)

/-- Decode a quotient row in its own small radix before checking it in the
larger no-carry radix. -/
def inverseQuotientRow (qBound : ℕ) (packed : Fin r → ℕ) (i : Fin r) : List ℕ :=
  List.ofFn fun j : Fin r => certificateDigit qBound (packed i) j.val

private def identitySparseRow (i : Fin r) : SparseRow r ℕ := [(i, 1)]

private theorem residueMatrix_identitySparseRow (p : ℕ) :
    residueMatrix p (identitySparseRow (r := r)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [residueMatrix, identitySparseRow, rowValue, Matrix.one_apply, h]

/-- A packed left-inverse certificate for the actual integer matrix gives
its modular nonsingularity. The only checked arithmetic is the packed row
expansion and a packed dot product for each row. -/
theorem determinant_ne_zero_of_packed_left_inverse
    (A : Matrix (Fin r) (Fin r) ℤ) (p base qBound : ℕ) [Nontrivial (ZMod p)]
    (hp : 0 < p) (hq : 0 < qBound)
    (hCarry : r * (p - 1) * (p - 1) < base)
    (hQuotientCarry : 1 + p * qBound < base)
    (packedInverse packedRows packedQuotients : Fin r → ℕ)
    (hPack : ∀ i, packedRows i = packedMinorResidueRow A p base i)
    (hCheck : ∀ i, packedProduct (inverseSparseRow p packedInverse i) packedRows =
      base ^ i.val + p * Nat.ofDigits base (inverseQuotientRow qBound packedQuotients i)) :
    (A.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
  let L := inverseSparseRow p packedInverse
  let U := denseResidueRow A p
  let Q := inverseQuotientRow qBound packedQuotients
  have hbase : 0 < base := by omega
  have hUpper (i : Fin r) : packedRows i = packSparse base (U i) :=
    (hPack i).trans (packSparse_denseResidueRow A p base i).symm
  have hProduct (i j : Fin r) : rowValue (multiplyRow (L i) U) j < base := by
    have hLLength : (L i).length ≤ r := by
      unfold L inverseSparseRow
      simpa only [List.length_ofFn] using List.length_filter_le
        (p := fun e : Fin r × ℕ => e.2 != 0)
        (List.ofFn fun j : Fin r => (j, certificateDigit p (packedInverse i) j.val))
    have hLCoeff : ∀ e ∈ L i, e.2 ≤ p - 1 := by
      intro e he
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
      have hb := Nat.mod_lt (packedInverse i / p ^ k.val) hp
      change packedInverse i / p ^ k.val % p ≤ p - 1
      omega
    have hUCoeff (k : Fin r) : rowValue (U k) j ≤ p - 1 := by
      change rowValue (denseResidueRow A p k) j ≤ p - 1
      rw [denseResidueRow_value]
      have hb := denseResidueCoefficient_lt A p hp k j
      omega
    calc
      rowValue (multiplyRow (L i) U) j ≤ (L i).length * ((p - 1) * (p - 1)) :=
        rowValue_multiplyRow_le_length_mul (L i) U j (p - 1) (p - 1) hLCoeff hUCoeff
      _ ≤ r * ((p - 1) * (p - 1)) := Nat.mul_le_mul_right _ hLLength
      _ < base := by simpa only [Nat.mul_assoc] using hCarry
  have hTarget (i j : Fin r) : rowValue (identitySparseRow i) j ≤ 1 := by
    by_cases h : i = j <;> simp [identitySparseRow, rowValue, h]
  have hLength (i : Fin r) : (Q i).length = r := by simp [Q, inverseQuotientRow]
  have hQuotient (i : Fin r) : ((Q i).all fun q => decide (q < qBound)) = true := by
    apply List.all_eq_true.mpr
    intro q hqmem
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hqmem
    exact decide_eq_true (Nat.mod_lt _ hq)
  have hCheck' (i : Fin r) : packedProduct (L i) packedRows =
      packSparse base (identitySparseRow i) + p * Nat.ofDigits base (Q i) := by
    simpa [identitySparseRow, packSparse] using hCheck i
  have hmul := checked_packed_product p base qBound 1 hbase hQuotientCarry
    L U identitySparseRow packedRows Q hUpper hProduct hTarget hLength hQuotient hCheck'
  change residueMatrix p L * residueMatrix p (denseResidueRow A p) =
    residueMatrix p identitySparseRow at hmul
  rw [residueMatrix_denseResidueRow A p hp, residueMatrix_identitySparseRow] at hmul
  intro hz
  have hd := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one, hz, mul_zero] at hd
  exact zero_ne_one hd

end IdealGeneration.QuadraticLowDimension
