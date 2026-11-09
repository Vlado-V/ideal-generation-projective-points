module

public import IdealGeneration.QuadraticMiddleRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Coordinate changes between the explicit lifts and the actual residual multiplication. -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleEndpoint
open QuadraticElimination QuadraticConeResidual QuadraticMiddleRank

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable {m p q : ℕ} (D : QuadraticLiftParameters K P J)
variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q) (h : Compatible D e r C)

local notation "L" => ResidualCoordinates (K := K) (P := P)
local notation "Nμ" => QuadraticElimination.middleMultiplication D.firstLift D.secondLift
  (QuadraticFlag.firstKernelMap D.firstCorrection)
  (QuadraticFlag.secondKernelMap D.slope D.secondCorrection)
local notation "f" => residualProduct D e r C h
local notation "f₀" => C.residualMultiplication 2

/-- Identify the explicit coordinate tuple with the actual residual equation tuple. -/
def residualCoordinatesEquiv (hi : Function.Injective (representedQuadric D)) :
    (Fin (2 + m) → L) ≃ₗ[K] (Fin (2 + m) → C.residualPiece 2) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.ofBijective (representedToResidual D e r C h)
    ⟨representedToResidual_injective D e r C h hi, representedToResidual_surjective D e r C h hi⟩

theorem residualProduct_eq (hi : Function.Injective (representedQuadric D))
    (x : Fin (2 + m) → L) :
    f x = f₀ (residualCoordinatesEquiv D e r C h hi x) := rfl

theorem range_residualProduct_eq (hi : Function.Injective (representedQuadric D)) :
    (LinearMap.range f) = (LinearMap.range f₀) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (residualProduct_eq D e r C h hi x).symm⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨y,rfl⟩ := (residualCoordinatesEquiv D e r C h hi).surjective x
    exact ⟨y,residualProduct_eq D e r C h hi y⟩

include h in
/-- Faithfulness of represented multiplication gives faithfulness on actual quadrics. -/
theorem actualResidualProduct_injective (hi : Function.Injective Nμ) :
    Function.Injective f₀ := by
  have hQ := normalPolynomialMap_injective_of_middle _ _ _ _ hi
  let s := residualCoordinatesEquiv D e r C h hQ
  intro x y he
  obtain ⟨a,rfl⟩ := s.surjective x
  obtain ⟨b,rfl⟩ := s.surjective y
  exact congrArg s (residualProduct_injective D e r C h hi (by
    rw [residualProduct_eq D e r C h hQ, residualProduct_eq D e r C h hQ]
    exact he))

end IdealGeneration.QuadraticMiddleEndpoint
