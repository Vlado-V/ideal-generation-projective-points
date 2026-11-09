module

public import IdealGeneration.GenericRectangularDescent
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Modular rank certificates for matrices with denominators prime to the certificate prime. -/

namespace IdealGeneration.PrimeLocalInteger

/-- The integer denominators whose images are units in the residue ring. -/
def denominators (p : ℕ) : Submonoid ℤ :=
  (IsUnit.submonoid (ZMod p)).comap (Int.castRingHom (ZMod p)).toMonoidHom

/-- The localization of the integers away from the certificate prime. -/
abbrev LocalInteger (p : ℕ) := Localization (denominators p)

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Reduction sends any denominator to its inverse modulo the prime. -/
noncomputable def reduce : LocalInteger p →+* ZMod p :=
  IsLocalization.lift (M := denominators p) (g := Int.castRingHom (ZMod p))
    (fun b => b.property)

@[simp] theorem reduce_algebraMap (a : ℤ) :
    reduce p (algebraMap ℤ (LocalInteger p) a) = (a : ZMod p) :=
  IsLocalization.lift_eq _ a

theorem reduce_surjective : Function.Surjective (reduce p) := by
  intro a
  refine ⟨algebraMap ℤ (LocalInteger p) (ZMod.cast a), ?_⟩
  rw [reduce_algebraMap]
  exact ZMod.intCast_zmod_cast a

private theorem denominator_ne_zero (b : denominators p) : (b : ℤ) ≠ 0 := by
  have hb : IsUnit ((b : ℤ) : ZMod p) := b.property
  intro hz
  exact hb.ne_zero (by rw [hz, Int.cast_zero])

variable (K : Type*) [Field K] [CharZero K]

/-- The canonical realization of the localized coefficients in characteristic zero. -/
noncomputable def cast : LocalInteger p →+* K :=
  IsLocalization.lift (M := denominators p) (g := Int.castRingHom K)
    (fun b => isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (denominator_ne_zero p b)))

@[simp] theorem cast_algebraMap (a : ℤ) :
    cast p K (algebraMap ℤ (LocalInteger p) a) = (a : K) :=
  IsLocalization.lift_eq _ a

theorem cast_injective : Function.Injective (cast p K) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := denominators p)
  intro z hz
  rw [cast_algebraMap, Int.cast_eq_zero] at hz
  rw [hz, map_zero]

/-- The same fraction has the usual quotient value in the residue field. -/
@[simp] theorem reduce_mk' (a : ℤ) (b : denominators p) :
    reduce p (IsLocalization.mk' (LocalInteger p) a b) = (a : ZMod p) / (b : ℤ) := by
  apply (IsLocalization.lift_mk'_spec _ a _ b).mpr
  have hb : IsUnit ((b : ℤ) : ZMod p) := b.property
  change (a : ZMod p) = (b : ℤ) * ((a : ZMod p) / (b : ℤ))
  rw [mul_div_cancel₀ _ hb.ne_zero]

/-- The same fraction has the usual quotient value in characteristic zero. -/
@[simp] theorem cast_mk' (a : ℤ) (b : denominators p) :
    cast p K (IsLocalization.mk' (LocalInteger p) a b) = (a : K) / (b : ℤ) := by
  apply (IsLocalization.lift_mk'_spec _ a _ b).mpr
  change (a : K) = (b : ℤ) * ((a : K) / (b : ℤ))
  rw [mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (denominator_ne_zero p b))]

/-- Nonzero reduction certifies that the localized coefficient is a unit. -/
theorem isUnit_of_reduce_ne_zero (a : LocalInteger p) (ha : reduce p a ≠ 0) : IsUnit a := by
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (M := denominators p) a
  have hx : (x : ZMod p) ≠ 0 := by
    intro hz
    exact ha (by rw [reduce_mk', hz, zero_div])
  have hmem : x ∈ denominators p := isUnit_iff_ne_zero.mpr hx
  exact isUnit_iff_exists_inv.mpr ⟨_, IsLocalization.mk'_mul_mk'_eq_one' x y hmem⟩

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Nonzero reduction of a square determinant certifies the determinant over any
characteristic-zero field. -/
theorem matrix_det_ne_zero_of_reduce [DecidableEq n] (A : Matrix n n (LocalInteger p))
    (h : (A.map (reduce p)).det ≠ 0) : (A.map (cast p K)).det ≠ 0 := by
  have hu := isUnit_of_reduce_ne_zero p A.det (by rwa [(reduce p).map_det])
  change ((cast p K).mapMatrix A).det ≠ 0
  rw [← (cast p K).map_det]
  exact (hu.map (cast p K)).ne_zero

omit [Fintype m] [Fintype n] in
private theorem liftMatrix (B : Matrix m n (ZMod p)) :
    ∃ B' : Matrix m n (LocalInteger p), B'.map (reduce p) = B := by
  choose x hx using fun i j => reduce_surjective p (B i j)
  exact ⟨Matrix.of x, Matrix.ext hx⟩

/-- A full-column-rank modular certificate transfers to any characteristic-zero field. -/
theorem matrix_mulVec_injective_of_reduce (A : Matrix m n (LocalInteger p))
    (h : Function.Injective (A.map (reduce p)).mulVec) :
    Function.Injective (A.map (cast p K)).mulVec := by
  classical
  let F := (A.map (reduce p)).mulVecLin
  have hF : Function.Injective F := h
  obtain ⟨L, hL⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  let B : Matrix n m (ZMod p) := LinearMap.toMatrix' L
  have hB : B * A.map (reduce p) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp F = LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  obtain ⟨D, hD⟩ := liftMatrix p B
  have hdet : ((D * A).map (reduce p)).det ≠ 0 := by
    rw [Matrix.map_mul, hD, hB, Matrix.det_one]
    exact one_ne_zero
  have hinj := Matrix.mulVec_injective_of_det_ne_zero (matrix_det_ne_zero_of_reduce p K _ hdet)
  intro x y hxy
  apply hinj
  have hh := congrArg (D.map (cast p K)).mulVec hxy
  simpa only [Matrix.mulVec_mulVec, ← Matrix.map_mul] using hh

/-- A full-row-rank modular certificate transfers to any characteristic-zero field. -/
theorem matrix_mulVec_surjective_of_reduce (A : Matrix m n (LocalInteger p))
    (h : Function.Surjective (A.map (reduce p)).mulVec) :
    Function.Surjective (A.map (cast p K)).mulVec := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  obtain ⟨D, hD⟩ := liftMatrix p B
  have hdet : ((A * D).map (reduce p)).det ≠ 0 := by
    rw [Matrix.map_mul, hD, hB, Matrix.det_one]
    exact one_ne_zero
  let C := (A * D).map (cast p K)
  have hinj : Function.Injective C.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (matrix_det_ne_zero_of_reduce p K _ hdet)
  have hsurj := LinearMap.surjective_of_injective (f := C.mulVecLin) hinj
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨(D.map (cast p K)).mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
  exact hv

end IdealGeneration.PrimeLocalInteger
