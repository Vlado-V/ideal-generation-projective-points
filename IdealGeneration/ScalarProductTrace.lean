module

public import IdealGeneration.HyperplaneAlgebra

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Tangential products on a hyperplane

Injectivity of multiplication on the residual ideal makes the tangential
trace product injective. Its image is the full restricted product space.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {m p d : ℕ}

/-- The scalar trace of a tuple of residual equations. -/
def tangentPointProduct (a : PointCoordinates K m p) (d : ℕ) :
    (Fin m → pointPolynomialPiece a d) →ₗ[K] Poly K m where
  toFun g := ∑ i, X i * hyperplaneRestrict K m (g i).val
  map_add' g h := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c g := by simp [Finset.smul_sum]

@[simp] theorem tangentPointProduct_apply (a : PointCoordinates K m p)
    (g : Fin m → pointPolynomialPiece a d) :
    tangentPointProduct a d g = ∑ i, X i * hyperplaneRestrict K m (g i).val := rfl

/-- A tuple with zero normal coefficient has precisely the tangential trace product. -/
theorem tangentPointProduct_eq_restrict (a : PointCoordinates K m p)
    (g : Fin m → pointPolynomialPiece a d) :
    tangentPointProduct a d g = hyperplaneRestrict K m
      (coordinateProduct (pointPolynomialPiece a d) (Fin.cons 0 g)) := by
  simp [tangentPointProduct, coordinateProduct, Fin.sum_univ_succ]

/-- The normal coefficient contributes nothing after restriction. -/
theorem restrict_coordinateProduct_eq_tangent (a : PointCoordinates K m p)
    (g : Fin (m + 1) → pointPolynomialPiece a d) :
    hyperplaneRestrict K m (coordinateProduct (pointPolynomialPiece a d) g) =
      tangentPointProduct a d (fun i => g i.succ) := by
  simp [tangentPointProduct, coordinateProduct, Fin.sum_univ_succ]

/-- The tangential products exhaust the restricted residual product image. -/
theorem tangentPointProduct_range_eq (a : PointCoordinates K m p) :
    (tangentPointProduct a d).range =
      (coordinateProduct (pointPolynomialPiece a d)).range.map
        (hyperplaneRestrict K m).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨coordinateProduct (pointPolynomialPiece a d) (Fin.cons 0 g),
      ⟨Fin.cons 0 g, rfl⟩, (tangentPointProduct_eq_restrict a g).symm⟩
  · rintro ⟨f, ⟨g, rfl⟩, rfl⟩
    exact ⟨fun i => g i.succ, (restrict_coordinateProduct_eq_tangent a g).symm⟩

/-- Multiplication injectivity leaves no nonzero tangential tuple with zero trace. -/
theorem tangentPointProduct_injective (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (h : Function.Injective (pointMultiplication a d)) :
    Function.Injective (tangentPointProduct a d) := by
  have hker := restricted_coordinateProduct_ker (hyperplaneRestrict K m)
    (hyperplaneRestrict_X_zero K m) (pointPolynomialPiece a d)
    ((coordinateProduct_pointPolynomialPiece_injective_iff a).mpr h)
    (pointProducts_normal_division a ha)
  have hzero : ∀ g, tangentPointProduct a d g = 0 → g = 0 := by
    intro g hg
    have hgker : Fin.cons 0 g ∈
        ((hyperplaneRestrict K m).toLinearMap.comp
          (coordinateProduct (pointPolynomialPiece a d))).ker := by
      change hyperplaneRestrict K m
        (coordinateProduct (pointPolynomialPiece a d) (Fin.cons 0 g)) = 0
      rw [← tangentPointProduct_eq_restrict]
      exact hg
    rw [hker] at hgker
    obtain ⟨w, hw⟩ := hgker
    have hwzero : w = 0 := by
      simpa [normalCoefficient] using congrFun hw 0
    funext i
    have hi := congrFun hw i.succ
    simpa [normalCoefficient, hwzero] using hi.symm
  intro g h hgh
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hgh, sub_self]

/-- These scalar traces have the expected homogeneous degree. -/
theorem tangentPointProduct_range_le_forms (a : PointCoordinates K m p) :
    (tangentPointProduct a d).range ≤ Forms K m (d + 1) := by
  rw [tangentPointProduct_range_eq]
  exact restricted_pointProducts_le_forms a

/-- The scalar trace space has one copy of the residual ideal for each tangential coordinate. -/
theorem finrank_tangentPointProduct_range (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (h : Function.Injective (pointMultiplication a d)) :
    finrank K (tangentPointProduct a d).range =
      m * finrank K (pointDegreePiece K a d) := by
  rw [tangentPointProduct_range_eq]
  exact finrank_restricted_pointProducts a ha h

/-- The scalar trace regarded as a homogeneous form. -/
def tangentPointProductForm (a : PointCoordinates K m p) (d : ℕ) :
    (Fin m → pointPolynomialPiece a d) →ₗ[K] Forms K m (d + 1) :=
  (tangentPointProduct a d).codRestrict _
    (fun g => tangentPointProduct_range_le_forms a ⟨g, rfl⟩)

@[simp] theorem tangentPointProductForm_val (a : PointCoordinates K m p)
    (g : Fin m → pointPolynomialPiece a d) :
    (tangentPointProductForm a d g).val = tangentPointProduct a d g := rfl

/-- Forgetting the homogeneous subtype preserves trace-product injectivity. -/
theorem tangentPointProductForm_injective (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (h : Function.Injective (pointMultiplication a d)) :
    Function.Injective (tangentPointProductForm a d) := by
  intro g h' hgh
  apply tangentPointProduct_injective a ha h
  exact congrArg Subtype.val hgh

/-- The homogeneous trace-product image has the same dimension. -/
theorem finrank_tangentPointProductForm_range (a : PointCoordinates K m p)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (h : Function.Injective (pointMultiplication a d)) :
    finrank K (tangentPointProductForm a d).range =
      m * finrank K (pointDegreePiece K a d) := by
  rw [LinearMap.finrank_range_of_inj (tangentPointProductForm_injective a ha h)]
  simp [Module.finrank_pi_fintype, pointPolynomialPiece_finrank]

end IdealGeneration
