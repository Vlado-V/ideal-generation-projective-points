module

public import IdealGeneration.QuadraticTraceRepresentation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Kernel and cokernel transport for the two-normal cone middle map. -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleKernelCokernel
open MvPolynomial QuadraticElimination QuadraticVariableTransport QuadraticTracePostulation
  QuadraticTraceRepresentation QuadraticAugmentedEvaluation

variable {K P J E : Type*} [Field K] {m p q : ℕ}
  (e : ((P × Bool) ⊕ J) ≃ Fin m) (C : ConeConfiguration K 2 m p q)
  (k : TraceLabel P J E ≃ Fin q) (extra : E → (P × Bool) ⊕ J → K)
  (htrace : ∀ t, C.trace (k t) = traceLabelPoint extra t ∘ e.symm)

local notation "B" => FlagQuadricPairs K P J
local notation "f" => C.residualMultiplication 2
local notation "μ" => C.middleMultiplication 2
local notation "ev" => extraPairEvaluation extra

local instance residualCubicGroup : AddCommGroup (C.residualPiece (2 + 1)) :=
  Module.addCommMonoidToAddCommGroup K

local instance flagPairGroup : AddCommGroup B := Module.addCommMonoidToAddCommGroup K

/-- Change from pairs vanishing at the extra points to the actual trace equation coordinates. -/
def middleSourceEquiv :
    ((Fin (2 + m) → C.residualPiece 2) × (ev).ker) ≃ₗ[K]
      ((Fin (2 + m) → C.residualPiece 2) × (Fin 2 → C.tracePiece 2)) :=
  (LinearEquiv.refl K _).prodCongr (traceEquationEquiv e C k extra htrace)

/-- The raw polynomial of a lifted flag-quadric pair. -/
def FlagProductFormula (g : B →ₗ[K] C.residualPiece (2 + 1)) : Prop :=
  ∀ b, (g b).val.val = flatten e (normalPairMap (b.val.1.val, b.val.2.val))

/-- The actual middle kernel is the kernel of evaluation on the lifted product coefficients. -/
def middleKernelEquiv (g : B →ₗ[K] C.residualPiece (2 + 1))
    (hg : FlagProductFormula e C g) (hf : Function.Injective f) :
    (μ).ker ≃ₗ[K] (restrictedEvaluation f g ev).ker := by
  let l := middleSourceEquiv e C k extra htrace
  have hmap : (μ).comp l.toLinearMap = augmented f g ev :=
    middleMultiplication_comp_traceEquationEquiv e C k extra htrace g hg
  have hker : (μ).ker.comap l.toLinearMap = (augmented f g ev).ker :=
    (LinearMap.ker_comp l.toLinearMap μ).symm.trans (congrArg LinearMap.ker hmap)
  exact (l.ofSubmodule' (μ).ker).symm.trans
    ((LinearEquiv.ofEq _ _ hker).trans (kernelEquiv f g ev hf))

include htrace in
/-- Changing the coordinates of the source preserves the actual multiplication image. -/
theorem middleRange_eq_augmentedRange (g : B →ₗ[K] C.residualPiece (2 + 1))
    (hg : FlagProductFormula e C g) :
    (μ).range = LinearMap.range (augmented f g ev :
      ((Fin (2 + m) → C.residualPiece 2) × (ev).ker) →ₗ[K] C.residualPiece (2 + 1)) := by
  let l := middleSourceEquiv e C k extra htrace
  have hmap : (μ).comp l.toLinearMap = augmented f g ev :=
    middleMultiplication_comp_traceEquationEquiv e C k extra htrace g hg
  exact (LinearMap.range_comp_of_range_eq_top μ l.range).symm.trans (congrArg LinearMap.range hmap)

/-- The actual middle cokernel is the cokernel of the remaining evaluation. -/
def middleCokernelEquiv (g : B →ₗ[K] C.residualPiece (2 + 1))
    (hg : FlagProductFormula e C g) (hspan : (f).range ⊔ g.range = ⊤)
    (he : Function.Surjective ev) :
    (C.residualPiece (2 + 1) ⧸ (μ).range) ≃ₗ[K]
      ((E → K × K) ⧸ (restrictedEvaluation f g ev).range) :=
  (Submodule.quotEquivOfEq _ _
    (middleRange_eq_augmentedRange e C k extra htrace g hg)).trans
      (cokernelEquiv f g ev hspan he)

end IdealGeneration.QuadraticMiddleKernelCokernel
