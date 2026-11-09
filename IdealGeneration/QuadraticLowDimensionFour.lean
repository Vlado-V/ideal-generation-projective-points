module

public import IdealGeneration.QuadraticLowDimensionCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact critical quadratic witnesses in four homogeneous variables. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

local instance fourPrimeCertificate : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩

/-- Integer chart points for the surjective endpoint in 4 variables. -/
private def fourSPoints : Fin 6 × Fin 3 → ℤ :=
  fun ij => (![![0, 1, 1], ![1, 1, 1], ![1, 1, 0], ![0, 0, 0], ![0, 1, 0], ![1, 0, 1]] : Fin 6 → Fin 3 → ℤ) ij.1 ij.2

private def fourSRows : Fin 18 → Fin 6 × Fin 3 :=
  ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2)]

private def fourSCols : Fin 18 → Fin 4 × Fin 4 × Fin 4 :=
  ![(0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 0, 1), (1, 2, 1), (1, 3, 1), (2, 0, 2), (2, 1, 2), (2, 3, 2), (3, 0, 3), (3, 1, 3), (3, 2, 3), (0, 1, 2), (0, 2, 1), (0, 1, 3), (0, 3, 1), (0, 2, 3), (0, 3, 2)]

private def fourSMinor : Matrix (Fin 18) (Fin 18) ℤ :=
  quadraticMinorMatrix fourSPoints fourSRows fourSCols

private def fourSInverse : Matrix (Fin 18) (Fin 18) (ZMod 2) :=
  ![![0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1],
    ![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1],
    ![0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]

private theorem fourS_inverse_row_0 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 0 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 0 j := by decide +kernel

private theorem fourS_inverse_row_1 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 1 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 1 j := by decide +kernel

private theorem fourS_inverse_row_2 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 2 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 2 j := by decide +kernel

private theorem fourS_inverse_row_3 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 3 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 3 j := by decide +kernel

private theorem fourS_inverse_row_4 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 4 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 4 j := by decide +kernel

private theorem fourS_inverse_row_5 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 5 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 5 j := by decide +kernel

private theorem fourS_inverse_row_6 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 6 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 6 j := by decide +kernel

private theorem fourS_inverse_row_7 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 7 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 7 j := by decide +kernel

private theorem fourS_inverse_row_8 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 8 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 8 j := by decide +kernel

private theorem fourS_inverse_row_9 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 9 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 9 j := by decide +kernel

private theorem fourS_inverse_row_10 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 10 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 10 j := by decide +kernel

private theorem fourS_inverse_row_11 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 11 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 11 j := by decide +kernel

private theorem fourS_inverse_row_12 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 12 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 12 j := by decide +kernel

private theorem fourS_inverse_row_13 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 13 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 13 j := by decide +kernel

private theorem fourS_inverse_row_14 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 14 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 14 j := by decide +kernel

private theorem fourS_inverse_row_15 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 15 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 15 j := by decide +kernel

private theorem fourS_inverse_row_16 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 16 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 16 j := by decide +kernel

private theorem fourS_inverse_row_17 :
    ∀ j, (fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2)))) 17 j =
      (1 : Matrix (Fin 18) (Fin 18) (ZMod 2)) 17 j := by decide +kernel

private theorem fourS_inverse_mul : fourSInverse * (fourSMinor.map (Int.castRingHom (ZMod 2))) = 1 := by
  ext i j
  fin_cases i
  · exact fourS_inverse_row_0 j
  · exact fourS_inverse_row_1 j
  · exact fourS_inverse_row_2 j
  · exact fourS_inverse_row_3 j
  · exact fourS_inverse_row_4 j
  · exact fourS_inverse_row_5 j
  · exact fourS_inverse_row_6 j
  · exact fourS_inverse_row_7 j
  · exact fourS_inverse_row_8 j
  · exact fourS_inverse_row_9 j
  · exact fourS_inverse_row_10 j
  · exact fourS_inverse_row_11 j
  · exact fourS_inverse_row_12 j
  · exact fourS_inverse_row_13 j
  · exact fourS_inverse_row_14 j
  · exact fourS_inverse_row_15 j
  · exact fourS_inverse_row_16 j
  · exact fourS_inverse_row_17 j

private theorem fourS_det_ne_zero :
    (fourSMinor.map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
  intro hz
  have hd := congrArg Matrix.det fourS_inverse_mul
  rw [Matrix.det_mul, Matrix.det_one, hz, mul_zero] at hd
  exact zero_ne_one hd

/-- The surjective critical point count in 4 variables. -/
theorem fourS_idealGenerationAt {K : Type*} [Field K] [CharZero K] :
    IdealGenerationAt K 3 2 6 :=
  idealGenerationAt_of_quadratic_minor_surjective (by decide)
    fourSPoints fourSRows fourSCols 2 fourS_det_ne_zero (by decide)

/-- Integer chart points for the injective endpoint in 4 variables. -/
private def fourIPoints : Fin 7 × Fin 3 → ℤ :=
  fun ij => (![![0, 1, 1], ![1, 1, 1], ![1, 1, 0], ![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 0, 0]] : Fin 7 → Fin 3 → ℤ) ij.1 ij.2

private def fourIRows : Fin 20 → Fin 7 × Fin 3 :=
  ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1)]

private def fourICols : Fin 20 → Fin 4 × Fin 4 × Fin 4 :=
  ![(0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 0, 1), (1, 2, 1), (1, 3, 1), (2, 0, 2), (2, 1, 2), (2, 3, 2), (3, 0, 3), (3, 1, 3), (3, 2, 3), (0, 1, 2), (0, 2, 1), (0, 1, 3), (0, 3, 1), (0, 2, 3), (0, 3, 2), (1, 2, 3), (1, 3, 2)]

private def fourIMinor : Matrix (Fin 20) (Fin 20) ℤ :=
  quadraticMinorMatrix fourIPoints fourIRows fourICols

private def fourIInverse : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    ![1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0]]

private theorem fourI_inverse_row_0 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 0 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 0 j := by decide +kernel

private theorem fourI_inverse_row_1 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 1 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 1 j := by decide +kernel

private theorem fourI_inverse_row_2 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 2 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 2 j := by decide +kernel

private theorem fourI_inverse_row_3 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 3 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 3 j := by decide +kernel

private theorem fourI_inverse_row_4 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 4 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 4 j := by decide +kernel

private theorem fourI_inverse_row_5 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 5 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 5 j := by decide +kernel

private theorem fourI_inverse_row_6 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 6 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 6 j := by decide +kernel

private theorem fourI_inverse_row_7 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 7 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 7 j := by decide +kernel

private theorem fourI_inverse_row_8 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 8 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 8 j := by decide +kernel

private theorem fourI_inverse_row_9 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 9 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 9 j := by decide +kernel

private theorem fourI_inverse_row_10 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 10 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 10 j := by decide +kernel

private theorem fourI_inverse_row_11 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 11 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 11 j := by decide +kernel

private theorem fourI_inverse_row_12 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 12 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 12 j := by decide +kernel

private theorem fourI_inverse_row_13 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 13 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 13 j := by decide +kernel

private theorem fourI_inverse_row_14 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 14 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 14 j := by decide +kernel

private theorem fourI_inverse_row_15 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 15 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 15 j := by decide +kernel

private theorem fourI_inverse_row_16 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 16 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 16 j := by decide +kernel

private theorem fourI_inverse_row_17 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 17 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 17 j := by decide +kernel

private theorem fourI_inverse_row_18 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 18 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 18 j := by decide +kernel

private theorem fourI_inverse_row_19 :
    ∀ j, (fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2)))) 19 j =
      (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) 19 j := by decide +kernel

private theorem fourI_inverse_mul : fourIInverse * (fourIMinor.map (Int.castRingHom (ZMod 2))) = 1 := by
  ext i j
  fin_cases i
  · exact fourI_inverse_row_0 j
  · exact fourI_inverse_row_1 j
  · exact fourI_inverse_row_2 j
  · exact fourI_inverse_row_3 j
  · exact fourI_inverse_row_4 j
  · exact fourI_inverse_row_5 j
  · exact fourI_inverse_row_6 j
  · exact fourI_inverse_row_7 j
  · exact fourI_inverse_row_8 j
  · exact fourI_inverse_row_9 j
  · exact fourI_inverse_row_10 j
  · exact fourI_inverse_row_11 j
  · exact fourI_inverse_row_12 j
  · exact fourI_inverse_row_13 j
  · exact fourI_inverse_row_14 j
  · exact fourI_inverse_row_15 j
  · exact fourI_inverse_row_16 j
  · exact fourI_inverse_row_17 j
  · exact fourI_inverse_row_18 j
  · exact fourI_inverse_row_19 j

private theorem fourI_det_ne_zero :
    (fourIMinor.map (Int.castRingHom (ZMod 2))).det ≠ 0 := by
  intro hz
  have hd := congrArg Matrix.det fourI_inverse_mul
  rw [Matrix.det_mul, Matrix.det_one, hz, mul_zero] at hd
  exact zero_ne_one hd

/-- The injective critical point count in 4 variables. -/
theorem fourI_idealGenerationAt {K : Type*} [Field K] [CharZero K] :
    IdealGenerationAt K 3 2 7 :=
  idealGenerationAt_of_quadratic_minor_injective (by decide)
    fourIPoints fourIRows fourICols 2 fourI_det_ne_zero (by decide)

/-- General quadrics in four homogeneous variables have the required rank. -/
theorem quadratic_four_all {K : Type*} [Field K] [CharZero K] :
    ∀ p, IdealGenerationAt K 3 2 p := by
  have hl : lowerCritical 4 2 = 3 := by
    unfold lowerCritical
    apply (Nat.floor_eq_iff (by norm_num [E, N, Nat.choose])).2
    norm_num [E, N, Nat.choose]
  have hu : upperCritical 4 2 = 4 := by
    unfold upperCritical
    apply (Nat.ceil_eq_iff (by decide : 4 ≠ 0)).2
    norm_num [E, N, Nat.choose]
  apply idealGenerationAt_all_of_critical (by decide : 1 ≤ 3) (by decide : 1 ≤ 2)
  · change IdealGenerationAt K 3 2 (N 4 2 - lowerCritical 4 2)
    rw [hl, show N 4 2 = 10 by decide]
    exact fourI_idealGenerationAt
  · change IdealGenerationAt K 3 2 (N 4 2 - upperCritical 4 2)
    rw [hu, show N 4 2 = 10 by decide]
    exact fourS_idealGenerationAt

end IdealGeneration.QuadraticLowDimension
