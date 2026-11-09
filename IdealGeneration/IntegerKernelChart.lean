module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Determinant-cleared matrix kernel charts

The adjugate clears the common determinant denominator in the free-coordinate
kernel chart. This construction commutes with entrywise coefficient maps.
-/

noncomputable section
namespace IdealGeneration.IntegerKernelChart
open Matrix
set_option maxHeartbeats 800000

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The determinant-cleared columns of the kernel of `[P Q]`. -/
def clearedKernelMatrix (P : Matrix ι ι R) (Q : Matrix ι κ R) : Matrix (ι ⊕ κ) κ R :=
  Matrix.fromRows (-(P.adjugate * Q)) (P.det • (1 : Matrix κ κ R))

/-- The free-coordinate chart computed from a verified pivot inverse. -/
def normalizedKernelMatrix (B : Matrix ι ι R) (Q : Matrix ι κ R) : Matrix (ι ⊕ κ) κ R :=
  Matrix.fromRows (-(B * Q)) (1 : Matrix κ κ R)

@[simp] theorem clearedKernelMatrix_apply_inl (P : Matrix ι ι R) (Q : Matrix ι κ R)
    (i : ι) (j : κ) : clearedKernelMatrix P Q (Sum.inl i) j = -(P.adjugate * Q) i j := rfl

@[simp] theorem clearedKernelMatrix_apply_inr (P : Matrix ι ι R) (Q : Matrix ι κ R)
    (i j : κ) : clearedKernelMatrix P Q (Sum.inr i) j = (P.det • (1 : Matrix κ κ R)) i j := rfl

/-- Every lifted column satisfies the original pivot and free equations. -/
theorem fromCols_mul_clearedKernelMatrix [Fintype κ] (P : Matrix ι ι R) (Q : Matrix ι κ R) :
    Matrix.fromCols P Q * clearedKernelMatrix P Q = 0 := by
  rw [clearedKernelMatrix, Matrix.fromCols_mul_fromRows, Matrix.mul_neg,
    ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, neg_add_cancel]

/-- The determinant-cleared construction commutes with any entrywise coefficient map. -/
theorem clearedKernelMatrix_map (f : R →+* S) (P : Matrix ι ι R) (Q : Matrix ι κ R) :
    (clearedKernelMatrix P Q).map f = clearedKernelMatrix (P.map f) (Q.map f) := by
  have hadj : P.adjugate.map f = (P.map f).adjugate := f.map_adjugate P
  have hdet : f P.det = (P.map f).det := f.map_det P
  have hprod : (P.adjugate * Q).map f = (P.map f).adjugate * Q.map f := by
    rw [Matrix.map_mul, hadj]
  have hone : (1 : Matrix κ κ R).map f = (1 : Matrix κ κ S) :=
    Matrix.map_one f (map_zero f) (map_one f)
  ext i j
  cases i with
  | inl i =>
    change f (-((P.adjugate * Q) i j)) = -(((P.map f).adjugate * Q.map f) i j)
    rw [map_neg]
    exact congrArg Neg.neg (congrArg (fun M : Matrix ι κ S => M i j) hprod)
  | inr i =>
    change f (P.det * (1 : Matrix κ κ R) i j) =
      (P.map f).det * (1 : Matrix κ κ S) i j
    have hentry : f ((1 : Matrix κ κ R) i j) = (1 : Matrix κ κ S) i j :=
      congrArg (fun M : Matrix κ κ S => M i j) hone
    rw [map_mul, hdet, hentry]

/-- A left pivot inverse identifies the adjugate with the determinant times that inverse. -/
theorem adjugate_eq_det_smul_of_leftInverse (P B : Matrix ι ι R) (hB : B * P = 1) :
    P.adjugate = P.det • B := by
  calc
    P.adjugate = (B * P) * P.adjugate := by rw [hB, Matrix.one_mul]
    _ = B * (P * P.adjugate) := Matrix.mul_assoc B P P.adjugate
    _ = P.det • B := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

/-- The cleared chart is the determinant multiple of the normalized chart. -/
theorem clearedKernelMatrix_eq_det_smul_normalized (P : Matrix ι ι R)
    (Q : Matrix ι κ R) (B : Matrix ι ι R) (hB : B * P = 1) :
    clearedKernelMatrix P Q = P.det • normalizedKernelMatrix B Q := by
  rw [clearedKernelMatrix, normalizedKernelMatrix, adjugate_eq_det_smul_of_leftInverse P B hB,
    Matrix.smul_mul, ← smul_neg]
  ext i j
  cases i <;> rfl

/-- A verified inverse after coefficient reduction identifies the reduced lift. -/
theorem map_clearedKernelMatrix_eq_det_smul (f : R →+* S)
    (P : Matrix ι ι R) (Q : Matrix ι κ R) (B : Matrix ι ι S) (hB : B * P.map f = 1) :
    (clearedKernelMatrix P Q).map f = (P.map f).det • normalizedKernelMatrix B (Q.map f) := by
  rw [clearedKernelMatrix_map]
  exact clearedKernelMatrix_eq_det_smul_normalized (P.map f) (Q.map f) B hB

/-- Kernel columns with identity free coordinates are the normalized chart. -/
theorem normalizedKernelMatrix_eq_of_verified [Fintype κ]
    (P B : Matrix ι ι R) (Q : Matrix ι κ R) (M : Matrix (ι ⊕ κ) κ R)
    (hB : B * P = 1) (hM : Matrix.fromCols P Q * M = 0)
    (hfree : M.submatrix Sum.inr id = 1) : normalizedKernelMatrix B Q = M := by
  let A : Matrix ι κ R := M.submatrix Sum.inl id
  let D : Matrix κ κ R := M.submatrix Sum.inr id
  have hsplit : Matrix.fromRows A D = M := by
    ext i j
    cases i <;> rfl
  have hD : D = 1 := hfree
  have hzero : P * A + Q * D = 0 := by
    rw [← Matrix.fromCols_mul_fromRows, hsplit]
    exact hM
  rw [hD, Matrix.mul_one] at hzero
  have hA : A = -(B * Q) := by
    have h := congrArg (fun N : Matrix ι κ R => B * N) hzero
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hB, Matrix.one_mul, Matrix.mul_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [normalizedKernelMatrix, ← hA, ← hD, hsplit]

/-- The determinant of a matrix with a verified left inverse is nonzero. -/
theorem det_ne_zero_of_leftInverse [Nontrivial R] (P B : Matrix ι ι R) (hB : B * P = 1) :
    P.det ≠ 0 := by
  have h := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

end Ring

section Field
variable {K : Type*} [Field K] [Fintype κ]

/-- The free coordinates of a lifted vector are scaled by the pivot determinant. -/
@[simp] theorem clearedKernelMatrix_mulVec_inr (P : Matrix ι ι K) (Q : Matrix ι κ K)
    (v : κ → K) (j : κ) : (clearedKernelMatrix P Q *ᵥ v) (Sum.inr j) = P.det * v j := by
  simp [clearedKernelMatrix, Matrix.smul_mulVec, smul_eq_mul]

/-- A nonzero pivot determinant makes the lifted free-coordinate map injective. -/
theorem clearedKernelMatrix_mulVec_injective (P : Matrix ι ι K) (Q : Matrix ι κ K)
    (hdet : P.det ≠ 0) : Function.Injective (clearedKernelMatrix P Q).mulVec := by
  intro x y hxy
  funext j
  apply mul_left_cancel₀ hdet
  simpa only [clearedKernelMatrix_mulVec_inr] using congrFun hxy (Sum.inr j)

/-- With a nonzero pivot determinant, the lifted columns span the actual kernel. -/
theorem clearedKernelMatrix_range_eq_ker (P : Matrix ι ι K) (Q : Matrix ι κ K)
    (hdet : P.det ≠ 0) : (clearedKernelMatrix P Q).mulVecLin.range =
      (Matrix.fromCols P Q).mulVecLin.ker := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change Matrix.fromCols P Q *ᵥ (clearedKernelMatrix P Q *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, fromCols_mul_clearedKernelMatrix, Matrix.zero_mulVec]
  · intro hx
    let v : κ → K := x ∘ Sum.inr
    let w : κ → K := P.det⁻¹ • v
    let y := clearedKernelMatrix P Q *ᵥ w
    have hy : Matrix.fromCols P Q *ᵥ y = 0 := by
      dsimp [y]
      rw [Matrix.mulVec_mulVec, fromCols_mul_clearedKernelMatrix, Matrix.zero_mulVec]
    have hfree : y ∘ Sum.inr = x ∘ Sum.inr := by
      funext j
      change y (Sum.inr j) = x (Sum.inr j)
      dsimp [y, w, v]
      rw [clearedKernelMatrix_mulVec_inr]
      change P.det * (P.det⁻¹ * x (Sum.inr j)) = x (Sum.inr j)
      rw [← mul_assoc, mul_inv_cancel₀ hdet, one_mul]
    have hx' : P *ᵥ (x ∘ Sum.inl) + Q *ᵥ (x ∘ Sum.inr) = 0 := by
      change Matrix.fromCols P Q *ᵥ x = 0 at hx
      simpa only [Matrix.fromCols_mulVec] using hx
    have hy' : P *ᵥ (y ∘ Sum.inl) + Q *ᵥ (x ∘ Sum.inr) = 0 := by
      rw [← hfree]
      simpa only [Matrix.fromCols_mulVec] using hy
    have hleft : y ∘ Sum.inl = x ∘ Sum.inl :=
      (Matrix.mulVec_injective_of_det_ne_zero hdet) (add_right_cancel (hy'.trans hx'.symm))
    refine ⟨w, ?_⟩
    change y = x
    funext i
    cases i with
    | inl i => exact congrFun hleft i
    | inr i => exact congrFun hfree i

end Field

end IdealGeneration.IntegerKernelChart
