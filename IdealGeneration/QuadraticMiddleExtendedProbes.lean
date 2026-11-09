module

public import IdealGeneration.QuadraticMiddleEndpoint
public import IdealGeneration.QuadraticMiddleKernelCokernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The other branch of (A.6), after including every probe in (A.4). -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleExtendedProbes
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticVariableTransport
open QuadraticConeResidual QuadraticMiddleRank QuadraticMiddleEndpoint QuadraticAugmentedEvaluation
open QuadraticCoreRestriction QuadraticTracePostulation QuadraticTraceRepresentation
open QuadraticFlagFamily QuadraticFlagProbeScalar QuadraticMiddleKernelCokernel

variable {K P J E : Type*} [Field K] [CharZero K] [Fintype P] [Fintype J] [DecidableEq J]
variable {m p q : ℕ} (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q)
variable (p₀ : P) (layers : Bool → J)
variable (h : Compatible (parameters K p₀ layers) e r C)
variable (extra : E → (P × Bool) ⊕ J → K)

local notation "D" => parameters K p₀ layers
local notation "hc" => parameters_slope_injective K p₀ layers
local notation "g" => flagProduct D e r C
local notation "f" => C.residualMultiplication 2
local notation "ev" => extraPairEvaluation extra

local instance residualCubicGroup : AddCommGroup (C.residualPiece (2 + 1)) :=
  Module.addCommMonoidToAddCommGroup K
local instance flagPairGroup : AddCommGroup (FlagQuadricPairs K P J) :=
  Module.addCommMonoidToAddCommGroup K

/-- Evaluation stays injective on the projected space after adjoining any points. -/
theorem restrictedEvaluation_injective_of_contains_probes
    (hne : layers false ≠ layers true) (select : ProbeIndex p₀ → E)
    (hselect : ∀ i, extra (select i) = probePoint p₀ layers i) :
    Function.Injective (restrictedEvaluation f (g h) ev) := by
  have hΩ := canonicalActualProjectedMap_injective K p₀ layers hne
  have hQ : Function.Injective (representedQuadric D) := (D).actualNormalPolynomialMap_injective hc hΩ
  let l := actualProductCoefficientsEquiv D e r C h hc hQ
  intro a b hab
  apply l.injective
  apply (canonicalJointEvaluation_bijective K p₀ layers hne).1
  have ha : (l a).val = a.val.val := actualProductCoefficientsEquiv_val D e r C h hc hQ a
  have hb : (l b).val = b.val.val := actualProductCoefficientsEquiv_val D e r C h hc hQ b
  have he (i : ProbeIndex p₀) :
      (D).projectedEvaluation hc (probePoint p₀ layers i) (l a) =
        (D).projectedEvaluation hc (probePoint p₀ layers i) (l b) := by
    have hv := congrFun hab (select i)
    change ev a.val (select i) = ev b.val (select i) at hv
    simp only [extraPairEvaluation_apply, hselect] at hv
    simpa only [QuadraticLiftParameters.projectedEvaluation_apply, ha, hb] using hv
  apply Prod.ext
  · funext i
    exact he (.inl i)
  · funext a b
    exact he (.inr (a,b))

variable [Fintype E]

include h in
/-- Once all native probes occur, the middle map is injective and its
cokernel has the remaining evaluation dimension. -/
theorem finrank_extendedMiddle (hne : layers false ≠ layers true)
    (select : ProbeIndex p₀ → E)
    (hselect : ∀ i, extra (select i) = probePoint p₀ layers i)
    (k : TraceLabel P J E ≃ Fin q)
    (htrace : ∀ t, C.trace (k t) = traceLabelPoint extra t ∘ e.symm)
    (hs : ∀ i, C.point i (normalIndex (m := m) false) ≠ 0)
    (hscalar : Function.Surjective ((quadraticEvaluation extra).comp
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).subtype)) :
    finrank K (C.middleMultiplication 2).ker = 0 ∧
      finrank K (C.residualPiece (2 + 1) ⧸ (C.middleMultiplication 2).range) =
        2 * Fintype.card E - (2 * Fintype.card (P × Bool) + 2) := by
  have hΩ := canonicalActualProjectedMap_injective K p₀ layers hne
  have hi := (D).actualMiddleMultiplication_injective hc hΩ
  have hQ : Function.Injective (representedQuadric D) := (D).actualNormalPolynomialMap_injective hc hΩ
  have hf := actualResidualProduct_injective D e r C h hi
  have hd := finrank_canonicalProjectedPairSpace K p₀ layers hne
  have hspan := residualProduct_sup_flagProduct D e r C h hc hi hd hs
  rw [range_residualProduct_eq D e r C h hQ] at hspan
  have he := extraPairEvaluation_surjective extra hscalar
  have hiev := restrictedEvaluation_injective_of_contains_probes e r C p₀ layers h extra hne select hselect
  have hZ : finrank K (Submodule.comap (g h) (LinearMap.range f)) = 2 * Fintype.card (P × Bool) + 2 :=
    (actualProductCoefficientsEquiv D e r C h hc hQ).finrank_eq.trans hd
  have ht : finrank K (E → K × K) = 2 * Fintype.card E := by
    simp [Module.finrank_pi_fintype, Nat.mul_comm]
  constructor
  · rw [(middleKernelEquiv e C k extra htrace (g h) (fun _ => rfl) hf).finrank_eq,
      LinearMap.ker_eq_bot_of_injective hiev, finrank_bot]
  · rw [(middleCokernelEquiv e C k extra htrace (g h) (fun _ => rfl) hspan he).finrank_eq]
    have hdim := (LinearMap.range (restrictedEvaluation f (g h) ev)).finrank_quotient_add_finrank
    have hr : finrank K (LinearMap.range (restrictedEvaluation f (g h) ev)) =
        2 * Fintype.card (P × Bool) + 2 := (LinearMap.finrank_range_of_inj hiev).trans hZ
    rw [hr, ht] at hdim
    omega

end IdealGeneration.QuadraticMiddleExtendedProbes
