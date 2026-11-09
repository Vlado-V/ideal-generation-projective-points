module

public import IdealGeneration.CyclotomicMatrixDescent
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Conic directions and the root-edge coordinates used in the three-variable enlargement. -/
namespace IdealGeneration.TripleNormal
open Matrix
open scoped Matrix

variable {K : Type*} [Field K]

/-- The mixed direction at the base coordinate with parameter `t`. -/
def conicVector (t : K) : Fin 3 → K := ![1, t, t ^ 2]

def sigmaPlus (ω t : K) : Fin 3 → K := ![ω ^ 2 * t ^ 2, ω * t, 1]

def sigmaMinus (ω t : K) : Fin 3 → K := ![ω * t ^ 2, ω ^ 2 * t, 1]

def thetaPlus (ω : K) : K := -(ω ^ 2)

def thetaMinus (ω : K) : K := ω

def rootVector (t : K) : Fin 3 → K := ![t ^ 2, -2 * t, 1]

def chordFactor (t u : K) : K := (t - u) ^ 2 * (t ^ 2 + t * u + u ^ 2)

def crossScale (ω t : K) : K := (ω - ω ^ 2) * t

private theorem cube_sum {ω : K} (hω : IsPrimitiveRoot ω 3) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := calc
    _ = ω ^ 3 - 1 := by ring
    _ = 0 := sub_eq_zero.mpr hω.pow_eq_one
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hω.ne_one (by decide)))

private theorem cube_fourth {ω : K} (hω : IsPrimitiveRoot ω 3) : ω ^ 4 = ω := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hω.pow_eq_one, one_mul]

/-- The two scalar equations in (A.9) follow from the primitive cube-root identity. -/
theorem conic_normal_difference (ω t : K) (hω : IsPrimitiveRoot ω 3) :
    thetaPlus ω • sigmaPlus ω t - thetaMinus ω • sigmaMinus ω t = rootVector t := by
  funext i
  fin_cases i
  · simp [thetaPlus, thetaMinus, sigmaPlus, sigmaMinus, rootVector]
    linear_combination -t ^ 2 * (cube_sum hω + cube_fourth hω)
  · simp [thetaPlus, thetaMinus, sigmaPlus, sigmaMinus, rootVector]
    linear_combination -2 * t * hω.pow_eq_one
  · simp [thetaPlus, thetaMinus, sigmaPlus, sigmaMinus, rootVector]
    linear_combination -(cube_sum hω)

theorem conic_normal_product (ω t u : K) (hω : IsPrimitiveRoot ω 3) :
    (sigmaPlus ω t ⬝ᵥ conicVector u) * (sigmaMinus ω t ⬝ᵥ conicVector u) =
      chordFactor t u := by
  simp [sigmaPlus, sigmaMinus, conicVector, chordFactor]
  linear_combination (t ^ 4 + t ^ 2 * u ^ 2) * hω.pow_eq_one +
    (t ^ 3 * u + t ^ 2 * u ^ 2 + t * u ^ 3) * cube_sum hω +
    t ^ 3 * u * cube_fourth hω

theorem conic_plus_annihilates (ω t : K) (hω : IsPrimitiveRoot ω 3) :
    sigmaPlus ω t ⬝ᵥ conicVector t = 0 := by
  simp [sigmaPlus, conicVector]
  linear_combination t ^ 2 * cube_sum hω

theorem conic_minus_annihilates (ω t : K) (hω : IsPrimitiveRoot ω 3) :
    sigmaMinus ω t ⬝ᵥ conicVector t = 0 := by
  simp [sigmaMinus, conicVector]
  linear_combination t ^ 2 * cube_sum hω

/-- The cross product of the two normals gives the indicated mixed direction. -/
theorem conic_normal_cross (ω t : K) (hω : IsPrimitiveRoot ω 3) :
    sigmaPlus ω t ⨯₃ sigmaMinus ω t = crossScale ω t • conicVector t := by
  funext i
  fin_cases i
  · simp [cross_apply, sigmaPlus, sigmaMinus, crossScale, conicVector]
    ring
  · simp [cross_apply, sigmaPlus, sigmaMinus, crossScale, conicVector]
    ring
  · simp [cross_apply, sigmaPlus, sigmaMinus, crossScale, conicVector]
    linear_combination t ^ 3 * cube_fourth hω

theorem crossScale_ne_zero (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0) :
    crossScale ω t ≠ 0 := by
  unfold crossScale
  apply mul_ne_zero _ ht
  intro h
  have hω₀ : ω ≠ 0 := by
    intro hz
    have hp := hω.pow_eq_one
    simp [hz] at hp
  have hmul : ω * (1 - ω) = 0 := by
    rw [show ω * (1 - ω) = ω - ω ^ 2 by ring, h]
  exact (hω.ne_one (by decide)) (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hω₀)).symm

/-- Evaluation of a mixed coefficient at the two normal directions above one base point. -/
def baseNormalMatrix (ω t : K) : Matrix (Fin 2) (Fin 3) K :=
  ![sigmaPlus ω t, sigmaMinus ω t]

/-- A right inverse with first coefficient zero. Its formula depends only on
the local base parameter, so it is preserved when further base indices are added. -/
def baseLiftMatrix (ω t : K) : Matrix (Fin 3) (Fin 2) K :=
  let a := (crossScale ω t)⁻¹
  ![![0, 0], ![a, -a], ![1 - ω * t * a, ω * t * a]]

theorem baseNormalMatrix_mul_lift (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0) :
    baseNormalMatrix ω t * baseLiftMatrix ω t = 1 := by
  let a := (crossScale ω t)⁻¹
  have hinv : (ω - ω ^ 2) * t * a = 1 :=
    mul_inv_cancel₀ (crossScale_ne_zero ω t hω ht)
  have hlift : baseLiftMatrix ω t = ![![0, 0], ![a, -a], ![1 - ω * t * a, ω * t * a]] := rfl
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, hlift]
  fin_cases i <;> fin_cases j <;> simp [baseNormalMatrix, sigmaPlus, sigmaMinus]
  · linear_combination -hinv
  · linear_combination hinv

theorem baseNormalMatrix_mulVec_surjective (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0) :
    Function.Surjective (baseNormalMatrix ω t).mulVec := by
  intro b
  refine ⟨(baseLiftMatrix ω t).mulVec b, ?_⟩
  rw [Matrix.mulVec_mulVec, baseNormalMatrix_mul_lift ω t hω ht, Matrix.one_mulVec]

/-- The only mixed directions invisible at both cone points are multiples
of the conic vector. -/
theorem baseNormalMatrix_ker_iff (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (x : Fin 3 → K) :
    (baseNormalMatrix ω t).mulVec x = 0 ↔ ∃ a : K, x = a • conicVector t := by
  constructor
  · intro hx
    let y := x - x 0 • conicVector t
    have hy₀ : y 0 = 0 := by
      change x 0 - x 0 * 1 = 0
      simp
    have hy : (baseNormalMatrix ω t).mulVec y = 0 := by
      change (baseNormalMatrix ω t).mulVecLin (x - x 0 • conicVector t) = 0
      rw [map_sub, map_smul]
      change (baseNormalMatrix ω t).mulVec x -
        x 0 • (baseNormalMatrix ω t).mulVec (conicVector t) = 0
      have hconic : (baseNormalMatrix ω t).mulVec (conicVector t) = 0 := by
        funext i
        fin_cases i
        · exact conic_plus_annihilates ω t hω
        · exact conic_minus_annihilates ω t hω
      simp [hx, hconic]
    have hplus := congrFun hy 0
    have hminus := congrFun hy 1
    change sigmaPlus ω t ⬝ᵥ y = 0 at hplus
    change sigmaMinus ω t ⬝ᵥ y = 0 at hminus
    rw [vec3_dotProduct] at hplus hminus
    simp [sigmaPlus, sigmaMinus, hy₀] at hplus hminus
    have hprod : crossScale ω t * y 1 = 0 := by
      unfold crossScale
      linear_combination hplus - hminus
    have hy₁ := (mul_eq_zero.mp hprod).resolve_left (crossScale_ne_zero ω t hω ht)
    have hy₂ : y 2 = 0 := by simpa [hy₁] using hplus
    have hyzero : y = 0 := by
      funext i
      fin_cases i
      · exact hy₀
      · exact hy₁
      · exact hy₂
    exact ⟨x 0, sub_eq_zero.mp hyzero⟩
  · rintro ⟨a, rfl⟩
    funext i
    fin_cases i
    · change sigmaPlus ω t ⬝ᵥ (a • conicVector t) = 0
      rw [dotProduct_smul, conic_plus_annihilates ω t hω, smul_zero]
    · change sigmaMinus ω t ⬝ᵥ (a • conicVector t) = 0
      rw [dotProduct_smul, conic_minus_annihilates ω t hω, smul_zero]

private theorem cross_triple (a b c : Fin 3 → K) :
    a ⨯₃ (b ⨯₃ c) = (c ⬝ᵥ a) • b - (b ⬝ᵥ a) • c := by
  funext i
  fin_cases i <;> simp [cross_apply, vec3_dotProduct] <;> ring

/-- Express a chord normal in the two attached normal directions at one endpoint. -/
theorem conic_chord_relation (ω t u : K) (hω : IsPrimitiveRoot ω 3) :
    crossScale ω u • (conicVector t ⨯₃ conicVector u) =
      (sigmaMinus ω u ⬝ᵥ conicVector t) • sigmaPlus ω u -
        (sigmaPlus ω u ⬝ᵥ conicVector t) • sigmaMinus ω u := by
  rw [← (crossProduct (conicVector t)).map_smul,
    ← conic_normal_cross ω u hω, cross_triple]

/-- Evaluate the edge coordinate of a lift satisfying the two base equations (A.10). -/
theorem conic_edge_lift (ω t u : K) (hω : IsPrimitiveRoot ω 3)
    (w A : Fin 3 → K)
    (hplus : sigmaPlus ω u ⬝ᵥ A =
      -thetaPlus ω * ((sigmaPlus ω u ⬝ᵥ w) * (sigmaPlus ω u ⬝ᵥ conicVector t)))
    (hminus : sigmaMinus ω u ⬝ᵥ A =
      -thetaMinus ω * ((sigmaMinus ω u ⬝ᵥ w) * (sigmaMinus ω u ⬝ᵥ conicVector t))) :
    crossScale ω u * ((conicVector t ⨯₃ conicVector u) ⬝ᵥ A) =
      -(chordFactor u t) * (rootVector u ⬝ᵥ w) := by
  have he := congrArg (fun v => v ⬝ᵥ A) (conic_chord_relation ω t u hω)
  simp only [smul_dotProduct, sub_dotProduct, smul_eq_mul, hplus, hminus] at he
  rw [he, ← conic_normal_product ω u t hω, ← conic_normal_difference ω u hω]
  simp only [smul_dotProduct, sub_dotProduct, smul_eq_mul]
  ring

theorem chordFactor_comm (t u : K) : chordFactor t u = chordFactor u t := by
  unfold chordFactor
  ring

/-- The cleared edge coefficient is (A.12) after the two local rescalings. -/
theorem conic_scaled_edge_equation (ω t u : K) (A B v w : Fin 3 → K)
    (hA : crossScale ω u * ((conicVector t ⨯₃ conicVector u) ⬝ᵥ A) =
      -(chordFactor u t) * (rootVector u ⬝ᵥ v))
    (hB : crossScale ω t * ((conicVector u ⨯₃ conicVector t) ⬝ᵥ B) =
      -(chordFactor t u) * (rootVector t ⬝ᵥ w)) :
    crossScale ω t * crossScale ω u * ((conicVector t ⨯₃ conicVector u) ⬝ᵥ (A + B)) =
      chordFactor t u *
        (rootVector t ⬝ᵥ (crossScale ω u • w) - rootVector u ⬝ᵥ (crossScale ω t • v)) := by
  rw [chordFactor_comm u t] at hA
  rw [← cross_anticomm (conicVector t) (conicVector u), neg_dotProduct] at hB
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  linear_combination crossScale ω t * hA - crossScale ω u * hB

/-- Distinct root parameters give an invertible root probe matrix. -/
theorem rootProbe_det_ne_zero [CharZero K] (a b c : K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Matrix.det (Matrix.of ![rootVector a, rootVector b, rootVector c])) ≠ 0 := by
  have hdet : (Matrix.det (Matrix.of ![rootVector a, rootVector b, rootVector c])) =
      2 * (b - a) * (c - a) * (c - b) := by
    rw [Matrix.det_fin_three]
    simp [rootVector]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr hab.symm)) (sub_ne_zero.mpr hac.symm)) (sub_ne_zero.mpr hbc.symm)

/-- The chord normal after removing the endpoint difference. -/
def chordNormal (t u : K) : Fin 3 → K := ![t * u, -(t + u), 1]

theorem conic_chord_coefficients (t u : K) :
    conicVector t ⨯₃ conicVector u = (u - t) • chordNormal t u := by
  funext i
  fin_cases i <;> simp [cross_apply, conicVector, chordNormal] <;> ring

/-- Distinct conic parameters give independent pairs of mixed directions. -/
theorem conicVector_pair_independent (a b : K) (hab : a ≠ b) :
    LinearIndependent K ![conicVector a, conicVector b] := by
  apply crossProduct_ne_zero_iff_linearIndependent.mp
  rw [conic_chord_coefficients]
  intro hz
  have he := congrFun hz (2 : Fin 3)
  change (b - a) * 1 = 0 at he
  exact (sub_ne_zero.mpr hab.symm) (by simpa only [mul_one] using he)

/-- Distinct conic parameters give the nonsingular Vandermonde layer block. -/
theorem conicVector_triple_det_ne_zero (a b c : K) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (Matrix.det (Matrix.of ![conicVector a, conicVector b, conicVector c])) ≠ 0 := by
  have hdet : Matrix.det (Matrix.of ![conicVector a, conicVector b, conicVector c]) =
      (b - a) * (c - a) * (c - b) := by
    rw [Matrix.det_fin_three]
    simp [conicVector]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hac.symm))
    (sub_ne_zero.mpr hbc.symm)

/-- A pair of chords meeting at one endpoint has independent normals together
with any chord avoiding that endpoint. -/
theorem chordNormal_sharedEndpoint_det (a b c d e : K) :
    (Matrix.det (Matrix.of ![chordNormal a b, chordNormal a c, chordNormal d e])) =
      (c - b) * (a - d) * (a - e) := by
  rw [Matrix.det_fin_three]
  simp [chordNormal]
  ring

/-- The leading two-point block for three chord planes has trivial kernel
when their three normals are independent. -/
theorem chordPlane_leadingBlock_kernel (n₁ n₂ n₃ A B C : Fin 3 → K)
    (hdet : (Matrix.det (Matrix.of ![n₁, n₂, n₃])) ≠ 0)
    (hA : n₁ ⬝ᵥ A = 0) (hB : n₂ ⬝ᵥ B = 0) (hC : n₃ ⬝ᵥ C = 0)
    (hAB : A + B = 0) (hBC : B + C = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have h₁ := congrArg (fun v => n₁ ⬝ᵥ v) hAB
  have h₃ := congrArg (fun v => n₃ ⬝ᵥ v) hBC
  simp only [dotProduct_add, hA, hC, zero_add, add_zero, dotProduct_zero] at h₁ h₃
  have hker : Matrix.mulVec (Matrix.of ![n₁, n₂, n₃]) B = 0 := by
    funext i
    fin_cases i
    · exact h₁
    · exact hB
    · exact h₃
  have hzero : B = 0 := (Matrix.mulVec_injective_of_det_ne_zero hdet)
    (hker.trans (Matrix.mulVec_zero _).symm)
  exact ⟨by simpa [hzero] using hAB, hzero, by simpa [hzero] using hBC⟩

end IdealGeneration.TripleNormal
