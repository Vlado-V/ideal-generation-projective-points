module

public import IdealGeneration.QuadraticMiddleExtendedProbes
public import IdealGeneration.QuadraticExtendedScalarProbes
public import IdealGeneration.QuadraticCanonicalConeConfiguration

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Actual witnesses for the larger-probe case of (A.6). -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleExtendedWitness
open Module QuadraticFlag QuadraticElimination QuadraticVariableTransport
open QuadraticConeResidual QuadraticFlagFamily QuadraticFlagProbeScalar
open QuadraticTracePostulation QuadraticCoreRestriction QuadraticCanonicalConeConfiguration
open QuadraticExtendedScalarProbes QuadraticMiddleExtendedProbes
open scoped Classical

variable {K P J : Type*} [Field K] [CharZero K] [Fintype P] [Fintype J] [DecidableEq J]
variable {m p q s : ℕ} (p₀ : P) (layers : Bool → J)
variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (k : TraceLabel P J (ProbeIndex p₀ ⊕ Fin s) ≃ Fin q)

local instance residualCubicGroup (C : ConeConfiguration K 2 m p q) :
    AddCommGroup (C.residualPiece (2 + 1)) := Module.addCommMonoidToAddCommGroup K

/-- Appending any admissible number of scalar points to all the native probes
gives an actual witness with zero middle kernel and two cokernel dimensions
for each appended point. -/
theorem exists_extendedMiddleWitness (hne : layers false ≠ layers true)
    (hsize : Fintype.card (ProbeIndex p₀) + s ≤ finrank K
      (quadraticFlagVanishing (K := K) (P := P) (J := J))) :
    ∃ y : Fin s → (P × Bool) ⊕ J → K,
      let x := extendedProbePoints p₀ layers y
      let C := configuration (parameters K p₀ layers) e r k x
      Function.Surjective (scalarEvaluation quadraticFlagVanishing x) ∧
        finrank K (C.middleMultiplication 2).ker = 0 ∧
        finrank K (C.residualPiece (2 + 1) ⧸ (C.middleMultiplication 2).range) = 2 * s := by
  obtain ⟨y,hy⟩ := exists_extendedProbePoints_scalar_surjective (K := K) p₀ layers hne s hsize
  let x := extendedProbePoints p₀ layers y
  let D := parameters K p₀ layers
  let C := configuration D e r k x
  refine ⟨y, hy, ?_⟩
  have hm := finrank_extendedMiddle e r C p₀ layers
    (configuration_compatible D e r k x) x hne Sum.inl (fun _ => rfl) k
    (configuration_trace D e r k x) (canonical_configuration_s_ne_zero e r k x p₀ layers) hy
  rw [Fintype.card_sum, Fintype.card_fin, card_probeIndex] at hm
  have hcount : 2 * (Fintype.card (P × Bool) + 1 + s) -
      (2 * Fintype.card (P × Bool) + 2) = 2 * s := by omega
  rw [hcount] at hm
  exact hm

end IdealGeneration.QuadraticMiddleExtendedWitness
