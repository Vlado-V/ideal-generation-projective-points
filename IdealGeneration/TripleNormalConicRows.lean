module

public import IdealGeneration.TripleNormalNormalExtension
public import IdealGeneration.TripleNormalSupportedQuadrics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The conic rows at a new coordinate

The scaled pair of conic normal vectors gives two independent constraints.
Its one-dimensional kernel is parametrized by the actual conic vector.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix
open scoped Matrix

variable {K : Type*} [Field K]

private def branchScale (ω : K) : Fin 2 → K := ![thetaPlus ω, thetaMinus ω]

private theorem branchScale_ne_zero (ω : K) (hω : IsPrimitiveRoot ω 3) (k : Fin 2) :
    branchScale ω k ≠ 0 := by
  have hw : ω ≠ 0 := by
    intro hz
    simpa [hz] using hω.pow_eq_one
  fin_cases k <;> simp [branchScale, thetaPlus, thetaMinus, hw]

private theorem newNormalRowMap_conic_apply (ω : K) (t : Fin 3 → K)
    (b : Fin 3) (v : Fin 3 → K) (k : Fin 2) :
    newNormalRowMap (fun j => SupportedQuadrics.baseNormal ω (t j)) b v k =
      branchScale ω k * (baseNormalMatrix ω (t b)).mulVec v k := by
  fin_cases k <;> simp [SupportedQuadrics.baseNormal, branchScale, baseNormalMatrix,
    Matrix.mulVec, smul_dotProduct]

/-- The actual scaled conic pair gives full row rank at each new coordinate. -/
theorem newNormalRowMap_conic_surjective (ω : K) (t : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (b : Fin 3) (ht : t b ≠ 0) :
    Function.Surjective (newNormalRowMap (fun j => SupportedQuadrics.baseNormal ω (t j)) b) := by
  intro target
  obtain ⟨v, hv⟩ := baseNormalMatrix_mulVec_surjective ω (t b) hω ht
    (fun k => (branchScale ω k)⁻¹ * target k)
  refine ⟨v, ?_⟩
  funext k
  rw [newNormalRowMap_conic_apply, congrFun hv k, ← mul_assoc,
    mul_inv_cancel₀ (branchScale_ne_zero ω hω k), one_mul]

/-- A vector satisfies the two scaled conic equations exactly when it is
a multiple of the prescribed conic direction. -/
theorem newNormalRowMap_conic_ker_iff (ω : K) (t : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (b : Fin 3) (ht : t b ≠ 0) (v : Fin 3 → K) :
    newNormalRowMap (fun j => SupportedQuadrics.baseNormal ω (t j)) b v = 0 ↔
      ∃ a : K, v = a • conicVector (t b) := by
  rw [← baseNormalMatrix_ker_iff ω (t b) hω ht]
  constructor
  · intro hv
    funext k
    have hk := congrFun hv k
    rw [newNormalRowMap_conic_apply, Pi.zero_apply] at hk
    exact (mul_eq_zero.mp hk).resolve_left (branchScale_ne_zero ω hω k)
  · intro hv
    funext k
    rw [newNormalRowMap_conic_apply, congrFun hv k, Pi.zero_apply, mul_zero]

/-- The allowed column at a new conic coordinate has one scalar coordinate. -/
def newNormalRowMap_conic_kerEquiv (ω : K) (t : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (b : Fin 3) (ht : t b ≠ 0) :
    (newNormalRowMap (fun j => SupportedQuadrics.baseNormal ω (t j)) b).ker ≃ₗ[K] K where
  toFun v := v.val 0
  invFun a := ⟨a • conicVector (t b), LinearMap.mem_ker.mpr
    ((newNormalRowMap_conic_ker_iff ω t hω b ht _).mpr ⟨a, rfl⟩)⟩
  left_inv v := by
    obtain ⟨a, ha⟩ := (newNormalRowMap_conic_ker_iff ω t hω b ht _).mp
      (LinearMap.mem_ker.mp v.property)
    have h₀ : v.val 0 = a := by simp [ha, conicVector]
    apply Subtype.ext
    change v.val 0 • conicVector (t b) = v.val
    rw [h₀, ← ha]
  right_inv a := by simp [conicVector]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end IdealGeneration.TripleNormal
