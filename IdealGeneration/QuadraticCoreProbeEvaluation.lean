module

public import IdealGeneration.QuadraticCoreMiddle

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The six core coordinates of the projected elimination image are detected by the three probes. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreMiddle
open MvPolynomial Module QuadraticFlag QuadraticElimination

local notation "y₁" => (Sum.inl ((), false) : TraceIndex)
local notation "y₂" => (Sum.inl ((), true) : TraceIndex)
local notation "z₁" => (Sum.inr (0 : Fin 2) : TraceIndex)
local notation "z₂" => (Sum.inr (1 : Fin 2) : TraceIndex)

variable (K : Type*) [Field K]

/-- The first three trace probes in (A.4), in the four actual trace variables. -/
def coreProbePoint (i : Fin 3) : TraceIndex → K :=
  ![coordinatePoint y₁ + coordinatePoint z₁,
    coordinatePoint y₁ + coordinatePoint z₂,
    coordinatePoint z₁ + coordinatePoint z₂] i

/-- The three explicit core scalar flag equations. -/
def coreFlagBasisPolynomial (i : Fin 3) : MvPolynomial TraceIndex K :=
  ![(X y₁ - X y₂) * X z₁, (X y₁ - X y₂) * X z₂, X z₁ * X z₂] i

theorem coreFlagBasisPolynomial_homogeneous (i : Fin 3) :
    (coreFlagBasisPolynomial K i).IsHomogeneous 2 := by
  fin_cases i
  · exact ((isHomogeneous_X K y₁).sub (isHomogeneous_X K y₂)).mul (isHomogeneous_X K z₁)
  · exact ((isHomogeneous_X K y₁).sub (isHomogeneous_X K y₂)).mul (isHomogeneous_X K z₂)
  · exact (isHomogeneous_X K z₁).mul (isHomogeneous_X K z₂)

theorem coreFlagBasisPolynomial_vanish (i : Fin 3) (t : FlagIndex Unit (Fin 2)) :
    eval (flagPoint t) (coreFlagBasisPolynomial K i) = 0 := by
  classical
  cases t with
  | base j => fin_cases i <;> simp [coreFlagBasisPolynomial, flagPoint, coordinatePoint]
  | basePair j k => fin_cases i <;> simp [coreFlagBasisPolynomial, flagPoint, coordinatePoint]
  | layer j => fin_cases i <;> fin_cases j <;> norm_num [coreFlagBasisPolynomial, flagPoint, coordinatePoint]
  | layerPair p j =>
    cases p
    fin_cases i <;> fin_cases j <;> norm_num [coreFlagBasisPolynomial, flagPoint, coordinatePoint]

@[simp] theorem coreFlagBasisPolynomial_probe (i j : Fin 3) :
    eval (coreProbePoint K i) (coreFlagBasisPolynomial K j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [coreProbePoint, coreFlagBasisPolynomial, coordinatePoint]

/-- The explicit polynomials are members of the genuine scalar flag ideal. -/
def coreFlagBasis (i : Fin 3) : coreFlagIdeal K :=
  ⟨⟨coreFlagBasisPolynomial K i, coreFlagBasisPolynomial_homogeneous K i⟩,
    coreFlagBasisPolynomial_vanish K i⟩

/-- Scalar evaluation at the three core probes. -/
def coreScalarProbeEvaluation : coreFlagIdeal K →ₗ[K] (Fin 3 → K) where
  toFun f i := eval (coreProbePoint K i) f.val.val
  map_add' f g := by funext i; simp
  map_smul' a f := by funext i; simp

theorem coreScalarProbeEvaluation_surjective : Function.Surjective (coreScalarProbeEvaluation K) := by
  intro v
  refine ⟨∑ i, v i • coreFlagBasis K i, ?_⟩
  funext j
  change eval (coreProbePoint K j) (∑ i, v i • coreFlagBasis K i : coreFlagIdeal K).val.val = v j
  simp [coreFlagBasis]

variable [CharZero K]

theorem coreScalarProbeEvaluation_injective : Function.Injective (coreScalarProbeEvaluation K) := by
  let : AddCommGroup (coreFlagIdeal K) := Module.addCommMonoidToAddCommGroup K
  have h := (coreScalarProbeEvaluation K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (coreScalarProbeEvaluation_surjective K), finrank_top,
    Module.finrank_fin_fun, finrank_coreFlagIdeal] at h
  have hk : finrank K (coreScalarProbeEvaluation K).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The three scalar probes are dual coordinates for the actual core flag ideal. -/
def coreScalarProbeEquiv : coreFlagIdeal K ≃ₗ[K] (Fin 3 → K) :=
  LinearEquiv.ofBijective (coreScalarProbeEvaluation K)
    ⟨coreScalarProbeEvaluation_injective K, coreScalarProbeEvaluation_surjective K⟩

/-- Evaluating both components gives the six core probe coordinates. -/
def coreFlagPairProbeEquiv : coreFlagPairs K ≃ₗ[K] ((Fin 3 → K) × (Fin 3 → K)) :=
  (Submodule.prodEquiv (coreFlagIdeal K) (coreFlagIdeal K)).trans
    (LinearEquiv.prodCongr (coreScalarProbeEquiv K) (coreScalarProbeEquiv K))

theorem coreProjectedMap_injective : Function.Injective (coreProjectedMap K) := by
  let : AddCommGroup (Quadrics K TraceIndex × Quadrics K TraceIndex) :=
    Module.addCommMonoidToAddCommGroup K
  have hdim : finrank K (Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K))) = 6 := by
    rw [finrank_explicitOmega]
    norm_num [KernelCoefficients, Fintype.card_prod]
  have h := (coreProjectedMap K).finrank_range_add_finrank_ker
  rw [finrank_coreProjectedMap_range, hdim] at h
  have hk : finrank K (coreProjectedMap K).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The core projected elimination map, with its exact flag-pair range. -/
def coreProjectedEquiv : Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K)) ≃ₗ[K]
    coreFlagPairs K :=
  (LinearEquiv.ofInjective (coreProjectedMap K) (coreProjectedMap_injective K)).trans
    (LinearEquiv.ofEq _ _ (coreProjectedMap_range K))

/-- Evaluation of the actual projected elimination map at the three core probes is an isomorphism. -/
def coreProjectedProbeEquiv :
    Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K)) ≃ₗ[K]
      ((Fin 3 → K) × (Fin 3 → K)) :=
  (coreProjectedEquiv K).trans (coreFlagPairProbeEquiv K)

@[simp] theorem coreProjectedProbeEquiv_apply
    (x : Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K))) :
    coreProjectedProbeEquiv K x =
      (fun i => eval (coreProbePoint K i) (coreProjectedMap K x).1.val,
       fun i => eval (coreProbePoint K i) (coreProjectedMap K x).2.val) := rfl

end IdealGeneration.QuadraticCoreMiddle
