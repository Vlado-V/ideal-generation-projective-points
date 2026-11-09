module

public import IdealGeneration.Points
public import IdealGeneration.Multiplication
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Homogeneous equations and multiplication for arbitrary point representatives. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable (K : Type*) [Field K]

/-- Equations of a family of homogeneous point representatives. -/
def representativePiece {n p : ℕ} (z : Fin p → Fin n → K) (d : ℕ) :
    Submodule K (Forms K n d) :=
  ⨅ i, LinearMap.ker (evaluationLinear K n d (z i))

@[simp] theorem mem_representativePiece {n p d : ℕ}
    (z : Fin p → Fin n → K) (f : Forms K n d) :
    f ∈ representativePiece K z d ↔ ∀ i, eval (z i) f.val = 0 := by
  simp [representativePiece, evaluationLinear]

/-- Multiplication of equations by the coordinate linear forms. -/
def representativeMultiplication {n p : ℕ} (z : Fin p → Fin n → K) (d : ℕ) :
    (Fin n → representativePiece K z d) →ₗ[K] representativePiece K z (d + 1) where
  toFun f := ⟨formMultiplication K n d (fun j => (f j).val), by
    apply (mem_representativePiece K z _).mpr
    intro i
    simp only [formMultiplication_val, map_sum, map_mul, eval_X]
    apply Finset.sum_eq_zero
    intro j _
    rw [(mem_representativePiece K z _).mp (f j).property i, mul_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    exact (formMultiplication K n d).map_add _ _
  map_smul' a f := by
    apply Subtype.ext
    exact (formMultiplication K n d).map_smul a _

@[simp] theorem representativeMultiplication_val {n p d : ℕ}
    (z : Fin p → Fin n → K) (f : Fin n → representativePiece K z d) :
    (representativeMultiplication K z d f).val =
      formMultiplication K n d (fun j => (f j).val) := rfl

/-- In a normalized affine chart these are the existing point-ideal degree pieces. -/
theorem representativePiece_chart {n p d : ℕ} (a : PointCoordinates K n p) :
    representativePiece K (chartPoint K a) d = pointDegreePiece K a d := by
  ext f
  simp only [mem_representativePiece, mem_pointDegreePiece]

/-- Identify normalized representative equations with the point-ideal kernel. -/
def chartRepresentativeEquiv {n p : ℕ} (a : PointCoordinates K n p) (d : ℕ) :
    pointDegreePiece K a d ≃ₗ[K] representativePiece K (chartPoint K a) d :=
  LinearEquiv.ofEq _ _ (representativePiece_chart K a).symm

/-- The representative multiplication is the existing point-ideal
multiplication after the canonical chart identification. -/
theorem chartRepresentativeEquiv_multiplication {n p d : ℕ}
    (a : PointCoordinates K n p) (f : Fin (n + 1) → pointDegreePiece K a d) :
    representativeMultiplication K (chartPoint K a) d
      (fun i => chartRepresentativeEquiv K a d (f i)) =
        chartRepresentativeEquiv K a (d + 1) (pointMultiplication a d f) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl


end IdealGeneration
