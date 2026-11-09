module

public import IdealGeneration.QuadraticCoreRestriction
public import IdealGeneration.QuadraticFlagRestriction
public import IdealGeneration.QuadraticProjectionNaturality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Projection and probe evaluation commute with restriction to the six-point core. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreRestriction
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticCoreMiddle
open QuadraticTraceRestriction

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

abbrev FullOmega (K P : Type*) [Field K] :=
  Omega (K := K) (E := (Fin 3 → K) × (P × Bool → K))
    (LinearMap.fst K (Fin 3 → K) (P × Bool → K))

abbrev FlagPairSpace (K P J : Type*) [Field K] :
    Submodule K (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
    (quadraticFlagVanishing (K := K) (P := P) (J := J))

/-- Select one base-pair label. -/
def baseLabelEmbedding (p : P) : Unit ↪ P :=
  ⟨fun _ => p, fun _ _ _ => Subsingleton.elim _ _⟩

variable (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)

local notation "E" => traceEmbedding D.distinguishedPair e
local notation "D₀" => restrictParameters D e

omit [Fintype P] [Fintype J] in
/-- Restriction of a full flag pair belongs to the core flag pair. -/
theorem restrictPair_flagImage : (FlagPairSpace K P J).map (restrictPair K E) ≤
    FlagPairSpace K Unit (Fin 2) := by
  rintro _ ⟨f, hf, rfl⟩
  exact QuadraticFlagRestriction.restrictPair_mem_flagPairs K (baseLabelEmbedding D.distinguishedPair) e hf

omit [Fintype P] [Fintype J] in
theorem normal₀_ne (j : J) : D.normal₀ j ≠ 0 := by
  intro hz
  have h := D.determinant_ne j
  simp [hz] at h

omit [Fintype P] [Fintype J] in
theorem normal₁_ne (j : J) : D.normal₁ j ≠ 0 := by
  intro hz
  have h := D.determinant_ne j
  simp [hz] at h

/-- The eliminated pair from the canonical mixed corrections and normal lifts. -/
def actualQuadraticPhi : FullOmega K P →ₗ[K]
    (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  quadraticPhi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
    (secondKernelMap D.slope D.secondCorrection) D.firstLift_homogeneous D.secondLift_homogeneous
    (firstKernelMap_homogeneous D.firstCorrection) (secondKernelMap_homogeneous D.slope D.secondCorrection)

/-- The actual projected elimination map of the flag with parameters `D`. -/
def actualProjectedMap (hc : Function.Injective D.slope) : FullOmega K P →ₗ[K]
    (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  projectedEliminatedMap D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ hc (normal₀_ne D) (normal₁_ne D)
    D.first_normal_equation D.second_normal_equation D.firstLift D.secondLift
    D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing

theorem actualProjectedMap_spec (hc : Function.Injective D.slope) (x : FullOmega K P) :
    actualProjectedMap D hc x ∈ FlagPairSpace K P J ∧
      actualQuadraticPhi D x - actualProjectedMap D hc x ∈
        quadraticMixedImage D.slope D.firstCorrection D.secondCorrection :=
  projectedEliminatedMap_spec D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ hc (normal₀_ne D) (normal₁_ne D) D.first_normal_equation
    D.second_normal_equation D.firstLift D.secondLift D.firstLift_homogeneous
    D.secondLift_homogeneous D.actualNormalLiftVanishing x

/-- Restriction commutes with the actual projected elimination map. -/
theorem restrict_actualProjectedMap (hc : Function.Injective D.slope) (x : FullOmega K P) :
    restrictPair K E (actualProjectedMap D hc x) =
      actualProjectedMap D₀ (restrictParameters_slope_injective D e hc) (restrictOmega D x) := by
  have hcore := restrictParameters_slope_injective D e hc
  have hfull := actualProjectedMap_spec D hc x
  have hsmall := actualProjectedMap_spec D₀ hcore (restrictOmega D x)
  have hdis : Disjoint (quadraticMixedImage (D₀).slope (D₀).firstCorrection (D₀).secondCorrection)
      (FlagPairSpace K Unit (Fin 2)) :=
    (quadratic_flag_direct_sum (D₀).slope (D₀).firstCorrection (D₀).secondCorrection (D₀).distinguishedPair
      (D₀).normal₀ (D₀).normal₁ hcore (normal₀_ne D₀) (normal₁_ne D₀)
      (D₀).first_normal_equation (D₀).second_normal_equation).2
  have hphi : restrictPair K E (actualQuadraticPhi D x) =
      actualQuadraticPhi D₀ (restrictOmega D x) := restrict_quadraticPhi D e x
  exact projected_value_natural (restrictPair K E) _ _ _ _
    (restrictPair_mixedImage D e) (restrictPair_flagImage D e) hdis hfull.2 hfull.1
    (by rw [hphi]; exact hsmall.2) hsmall.1

/-- Parameter equality identifies the actual projected maps. -/
theorem actualProjectedMap_congr {D' : QuadraticLiftParameters K P J}
    (h : D = D') (hc : Function.Injective D.slope) (hc' : Function.Injective D'.slope) :
    actualProjectedMap D hc = actualProjectedMap D' hc' := by
  subst D'
  rfl

section FixedCore
variable [CharZero K]

/-- Zero extension of `Ω` gives an actual full preimage of each core projected value. -/
theorem restrict_fixedCore_projectedMap (hc : Function.Injective D.slope)
    (hD : D₀ = coreParameters K) (x : FullOmega K Unit) :
    restrictPair K E (actualProjectedMap D hc (extendOmega D x)) = coreProjectedMap K x := by
  rw [restrict_actualProjectedMap D e hc, restrictOmega_extendOmega]
  have hmap := actualProjectedMap_congr D₀ hD
    (restrictParameters_slope_injective D e hc) (coreSlope_injective K)
  exact congrArg (fun f => f x) hmap

/-- Evaluation of a full trace quadric at the three embedded core probes. -/
def embeddedProbeEvaluation : Quadrics K ((P × Bool) ⊕ J) →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i =>
    { toFun := fun f => eval (extendPoint K E (coreProbePoint K i)) f.val
      map_add' f g := by simp
      map_smul' a f := by simp }

/-- Evaluation of the full projected map at the three core probes. -/
def fullCoreProbeEvaluation (hc : Function.Injective D.slope) :
    FullOmega K P →ₗ[K] ((Fin 3 → K) × (Fin 3 → K)) :=
  ((embeddedProbeEvaluation D e).prodMap (embeddedProbeEvaluation D e)).comp (actualProjectedMap D hc)

omit [CharZero K] in
@[simp] theorem fullCoreProbeEvaluation_apply (hc : Function.Injective D.slope) (x : FullOmega K P) :
    fullCoreProbeEvaluation D e hc x =
      (fun i => eval (extendPoint K E (coreProbePoint K i)) (actualProjectedMap D hc x).1.val,
       fun i => eval (extendPoint K E (coreProbePoint K i)) (actualProjectedMap D hc x).2.val) := rfl

theorem fullCoreProbeEvaluation_extendOmega (hc : Function.Injective D.slope)
    (hD : D₀ = coreParameters K) (x : FullOmega K Unit) :
    fullCoreProbeEvaluation D e hc (extendOmega D x) = coreProjectedProbeEquiv K x := by
  rw [coreProjectedProbeEquiv_apply, fullCoreProbeEvaluation_apply]
  have h := restrict_fixedCore_projectedMap D e hc hD x
  apply Prod.ext
  · funext i
    have hi := congrArg (fun f => eval (coreProbePoint K i) f.1.val) h
    simpa only [restrictPair_fst, eval_restrict] using hi
  · funext i
    have hi := congrArg (fun f => eval (coreProbePoint K i) f.2.val) h
    simpa only [restrictPair_snd, eval_restrict] using hi

/-- The full projected image attains all six values at the three core probes. -/
theorem fullCoreProbeEvaluation_surjective (hc : Function.Injective D.slope)
    (hD : D₀ = coreParameters K) : Function.Surjective (fullCoreProbeEvaluation D e hc) := by
  intro v
  obtain ⟨x, hx⟩ := (coreProjectedProbeEquiv K).surjective v
  exact ⟨extendOmega D x, (fullCoreProbeEvaluation_extendOmega D e hc hD x).trans hx⟩

theorem finrank_fullCoreProbeEvaluation_range (hc : Function.Injective D.slope)
    (hD : D₀ = coreParameters K) : finrank K (fullCoreProbeEvaluation D e hc).range = 6 := by
  rw [LinearMap.range_eq_top.mpr (fullCoreProbeEvaluation_surjective D e hc hD), finrank_top,
    Module.finrank_prod, Module.finrank_fin_fun]

end FixedCore
end IdealGeneration.QuadraticCoreRestriction
