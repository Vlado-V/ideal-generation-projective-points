module

public import IdealGeneration.GenericMatrixDescent
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Rectangular integer certificates descend through a modular left inverse. -/

noncomputable section
namespace IdealGeneration

private def zmodIntegerLift {m n : Type*} {p : ℕ} (B : Matrix m n (ZMod p)) :
    Matrix m n ℤ :=
  B.map (ZMod.cast : ZMod p → ℤ)

private theorem zmodIntegerLift_reduction {m n : Type*} {p : ℕ}
    (B : Matrix m n (ZMod p)) :
    (zmodIntegerLift B).map (Int.castRingHom (ZMod p)) = B := by
  ext i j
  exact ZMod.intCast_zmod_cast (B i j)

/-- An injective rectangular matrix modulo a prime stays injective over any
characteristic-zero field. -/
theorem integer_matrix_mulVec_injective_of_mod {m n K : Type*}
    [Fintype m] [Fintype n] [Field K] [CharZero K]
    (A : Matrix m n ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hmod : Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Injective (A.map (Int.castRingHom K)).mulVec := by
  classical
  let Aₚ := A.map (Int.castRingHom (ZMod p))
  let F := Aₚ.mulVecLin
  have hF : Function.Injective F := hmod
  obtain ⟨L, hL⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  let B : Matrix n m (ZMod p) := LinearMap.toMatrix' L
  have hleft : B * Aₚ = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp F = LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  let Bℤ := zmodIntegerLift B
  have hBℤ : Bℤ.map (Int.castRingHom (ZMod p)) = B := zmodIntegerLift_reduction B
  have hprod : (Bℤ * A).map (Int.castRingHom (ZMod p)) = 1 := by
    rw [Matrix.map_mul, hBℤ]
    exact hleft
  have hdet : ((Bℤ * A).map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    rw [hprod, Matrix.det_one]
    exact one_ne_zero
  have hinj := (integer_matrix_mulVec_bijective_of_mod (K := K) (Bℤ * A) p hdet).1
  intro x y hxy
  apply hinj
  have h := congrArg (Bℤ.map (Int.castRingHom K)).mulVec hxy
  simpa only [Matrix.mulVec_mulVec, ← Matrix.map_mul] using h

/-- A surjective rectangular matrix modulo a prime stays surjective over any
characteristic-zero field. -/
theorem integer_matrix_mulVec_surjective_of_mod {m n K : Type*}
    [Fintype m] [Fintype n] [Field K] [CharZero K]
    (A : Matrix m n ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hmod : Function.Surjective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Surjective (A.map (Int.castRingHom K)).mulVec := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hmod
  let Bℤ := zmodIntegerLift B
  have hBℤ : Bℤ.map (Int.castRingHom (ZMod p)) = B := zmodIntegerLift_reduction B
  have hprod : (A * Bℤ).map (Int.castRingHom (ZMod p)) = 1 := by
    rw [Matrix.map_mul, hBℤ, hB]
  have hdet : ((A * Bℤ).map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    rw [hprod, Matrix.det_one]
    exact one_ne_zero
  have hsurj := (integer_matrix_mulVec_bijective_of_mod (K := K) (A * Bℤ) p hdet).2
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨(Bℤ.map (Int.castRingHom K)).mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hv

end IdealGeneration
