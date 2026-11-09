module

public import IdealGeneration.CertifiedPackedRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Packed certificates for rectangular products of natural residue matrices. -/

namespace CertifiedRank

variable {m n k : ℕ}

/-- Dot product of a dense natural row with the packed rows of its right factor. -/
def densePackedProduct (row packed : Fin n → ℕ) : ℕ :=
  (List.ofFn fun j => row j * packed j).sum

theorem densePackedProduct_eq_pack (base : ℕ) (row : Fin n → ℕ)
    (B : Matrix (Fin n) (Fin k) ℕ) (packed : Fin n → ℕ)
    (hPacked : ∀ j, packed j = packCoefficients base (B j)) :
    densePackedProduct row packed =
      packCoefficients base (fun j => ∑ l, row l * B l j) := by
  simp only [densePackedProduct, List.sum_ofFn, hPacked, packCoefficients_eq_sum,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Bounded digits and a single exact integer equality certify each modular
product row. The quotient digits are read in a separate, smaller radix. -/
theorem checked_dense_product (p base qBound : ℕ)
    (hp : 0 < p) (hb : 0 < base) (hq : 0 < qBound)
    (hLeft : n * ((p - 1) * (p - 1)) < base)
    (hRight : (p - 1) + p * qBound < base)
    (A : Matrix (Fin m) (Fin n) ℕ) (B : Matrix (Fin n) (Fin k) ℕ)
    (T : Matrix (Fin m) (Fin k) ℕ)
    (ha : ∀ i j, A i j < p) (hb' : ∀ i j, B i j < p) (ht : ∀ i j, T i j < p)
    (packed : Fin n → ℕ) (quotient : Fin m → ℕ)
    (hPacked : ∀ j, packed j = packCoefficients base (B j))
    (hProduct : ∀ i, densePackedProduct (A i) packed =
      packCoefficients base (T i) + p *
        packCoefficients base (fun j : Fin k => packedDigit qBound (quotient i) j.val)) :
    A.map (Nat.castRingHom (ZMod p)) * B.map (Nat.castRingHom (ZMod p)) =
      T.map (Nat.castRingHom (ZMod p)) := by
  ext i j
  let q : Fin k → ℕ := fun l => packedDigit qBound (quotient i) l.val
  have hq' (l : Fin k) : q l < qBound := Nat.mod_lt _ hq
  have hA (l : Fin n) : A i l ≤ p - 1 := by have := ha i l; omega
  have hB (l : Fin n) (v : Fin k) : B l v ≤ p - 1 := by have := hb' l v; omega
  have hT (v : Fin k) : T i v ≤ p - 1 := by have := ht i v; omega
  have hL (v : Fin k) : (∑ l, A i l * B l v) < base := by
    calc
      (∑ l, A i l * B l v) ≤ ∑ _l : Fin n, (p - 1) * (p - 1) :=
        Finset.sum_le_sum fun l _ => Nat.mul_le_mul (hA l) (hB l v)
      _ < base := by simpa using hLeft
  have hR (v : Fin k) : T i v + p * q v < base :=
    (Nat.add_le_add (hT v) (Nat.mul_le_mul_left p (Nat.le_of_lt (hq' v)))).trans_lt hRight
  have hd := hProduct i
  change _ = packCoefficients base (T i) + p * packCoefficients base q at hd
  rw [densePackedProduct_eq_pack base _ _ _ hPacked, ← packCoefficients_mul,
    ← packCoefficients_add] at hd
  have hc := congrArg (fun value => packedDigit base value j.val) hd
  rw [packedDigit_packCoefficients base hb _ hL j,
    packedDigit_packCoefficients base hb _ hR j] at hc
  have hz := congrArg (fun x : ℕ => (x : ZMod p)) hc
  change (∑ l, (A i l : ZMod p) * (B l j : ZMod p)) = (T i j : ZMod p)
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_mul, add_zero] using hz

end CertifiedRank
