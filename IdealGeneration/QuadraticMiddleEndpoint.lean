module

public import IdealGeneration.QuadraticResidualCoordinates
public import IdealGeneration.QuadraticTraceRepresentation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual two-normal middle multiplication reduces to selected probe evaluation. -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleEndpoint
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticVariableTransport
open QuadraticConeResidual QuadraticMiddleRank QuadraticAugmentedEvaluation
open QuadraticCoreRestriction QuadraticTracePostulation QuadraticTraceRepresentation
open QuadraticFlagFamily QuadraticFlagProbeScalar

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable {m p q : ℕ} (D : QuadraticLiftParameters K P J)
variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q) (h : Compatible D e r C)

local notation "B" => FlagQuadricPairs K P J
local notation "f" => residualProduct D e r C h
local notation "g" => flagProduct D e r C h
local notation "f₀" => C.residualMultiplication 2

local instance residualCubicGroup : AddCommGroup (C.residualPiece 3) :=
  Module.addCommMonoidToAddCommGroup K
local instance flagPairGroup : AddCommGroup B := Module.addCommMonoidToAddCommGroup K

set_option maxHeartbeats 800000 in
/-- The actual residual product coefficients identify with the projected space. -/
def actualProductCoefficientsEquiv (hc : Function.Injective D.slope)
    (hi : Function.Injective (representedQuadric D)) :
    Submodule.comap g (LinearMap.range f₀) ≃ₗ[K] D.projectedPairSpace hc := by
  have he := congrArg (Submodule.comap g) (range_residualProduct_eq D e r C h hi).symm
  exact (LinearEquiv.ofEq _ _ he).trans (productCoefficientsEquiv D e r C h hc)

set_option maxHeartbeats 800000 in
@[simp] theorem actualProductCoefficientsEquiv_val (hc : Function.Injective D.slope)
    (hi : Function.Injective (representedQuadric D)) (z : Submodule.comap g (LinearMap.range f₀)) :
    (actualProductCoefficientsEquiv D e r C h hc hi z).val = z.val.val := rfl

section Selected

variable [CharZero K] [DecidableEq J]
variable (p₀ : P) (layers : Bool → J) {s : ℕ} (select : Fin s ↪ ProbeIndex p₀)

local notation "D₀" => parameters K p₀ layers
local notation "hc₀" => parameters_slope_injective K p₀ layers
local notation "extra" => (fun i => probePoint (K := K) p₀ layers (select i))
local notation "evalExtra" => extraPairEvaluation extra
local notation "g₀" => flagProduct D₀ e r C

set_option maxHeartbeats 800000 in
/-- The canonical normal-coefficient evaluation is onto at any selected probes. -/
theorem canonical_restrictedEvaluation_surjective
    (h : Compatible D₀ e r C) (hne : layers false ≠ layers true) :
    Function.Surjective (restrictedEvaluation f₀ (g₀ h) evalExtra) := by
  have hQ := (D₀).actualNormalPolynomialMap_injective hc₀
    (canonicalActualProjectedMap_injective K p₀ layers hne)
  let E := actualProductCoefficientsEquiv D₀ e r C h hc₀ hQ
  have he := canonicalSelectedEvaluation_surjective K p₀ layers hne select
  intro v
  obtain ⟨x,hx⟩ := he v
  refine ⟨E.symm x, ?_⟩
  have hvalue (z : Submodule.comap (g₀ h) (LinearMap.range f₀)) :
      restrictedEvaluation f₀ (g₀ h) evalExtra z = canonicalSelectedEvaluation K p₀ layers select (E z) := by
    funext i
    change evalExtra z.val i = canonicalSelectedEvaluation K p₀ layers select (E z) i
    rw [extraPairEvaluation_apply]
    have hv : (E z).val = z.val.val := actualProductCoefficientsEquiv_val D₀ e r C h hc₀ hQ z
    simp only [canonicalSelectedEvaluation, LinearMap.pi_apply,
      QuadraticLiftParameters.projectedEvaluation_apply, hv]
  rw [hvalue, E.apply_symm_apply, hx]

/-- With the ordinary trace coordinates, selected probe evaluation controls
surjectivity of the actual cone middle map. -/
theorem canonical_middleMultiplication_surjective
    (hne : layers false ≠ layers true)
    (h : Compatible D₀ e r C)
    (k : TraceLabel P J (Fin s) ≃ Fin q)
    (htrace : ∀ t, C.trace (k t) = traceLabelPoint extra t ∘ e.symm)
    (hs : ∀ i, C.point i (normalIndex (m := m) false) ≠ 0) :
    Function.Surjective (C.middleMultiplication 2) := by
  have hΩ := canonicalActualProjectedMap_injective K p₀ layers hne
  have hi := (D₀).actualMiddleMultiplication_injective hc₀ hΩ
  have hQ := (D₀).actualNormalPolynomialMap_injective hc₀ hΩ
  have hspan := residualProduct_sup_flagProduct D₀ e r C h hc₀ hi
    (finrank_canonicalProjectedPairSpace K p₀ layers hne) hs
  rw [range_residualProduct_eq D₀ e r C h hQ] at hspan
  have he := extraPairEvaluation_surjective extra
    (selectedScalarEvaluation_surjective K p₀ layers hne select)
  have haug := (augmented_surjective_iff f₀ (g₀ h) evalExtra hspan he).mpr
    (canonical_restrictedEvaluation_surjective e r C p₀ layers select h hne)
  rw [← middleMultiplication_comp_traceEquationEquiv e C k extra htrace (g₀ h) (fun _ => rfl)] at haug
  intro v
  obtain ⟨z,hz⟩ := haug v
  exact ⟨_,hz⟩

end Selected
end IdealGeneration.QuadraticMiddleEndpoint
