module

public import IdealGeneration.QuadraticInjectiveAssembly
public import IdealGeneration.QuadraticCoreProjectionRestriction
public import IdealGeneration.QuadraticProjectionNaturality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The actual core responses for the injective endpoint

The mixed corrections are computed in all four core trace variables.
Their residuals are combinations of the three checked core flag equations.
-/

noncomputable section
namespace IdealGeneration.QuadraticInjectiveCoreBridge
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticLiftParameters
open QuadraticCoreMiddle QuadraticCoreRestriction QuadraticInjectiveAssembly Untouched

section Core

variable (K : Type*) [Field K] [CharZero K]

local notation "y₁" => (Sum.inl ((), false) : TraceIndex)
local notation "y₂" => (Sum.inl ((), true) : TraceIndex)
local notation "z₁" => (Sum.inr (0 : Fin 2) : TraceIndex)
local notation "z₂" => (Sum.inr (1 : Fin 2) : TraceIndex)
local notation "D" => coreParameters K

private def coreLinear (a b c d : K) : MvPolynomial TraceIndex K :=
  C a * X y₁ + C b * X y₂ + C c * X z₁ + C d * X z₂

omit [CharZero K] in
private theorem coreLinear_homogeneous (a b c d : K) :
    (coreLinear K a b c d).IsHomogeneous 1 :=
  (((isHomogeneous_C_mul_X a y₁).add (isHomogeneous_C_mul_X b y₂)).add
    (isHomogeneous_C_mul_X c z₁)).add (isHomogeneous_C_mul_X d z₂)

private theorem coreCorrectionValues (b : Bool) (j : Fin 2) :
    ((D).firstCorrection ((), b) j, (D).secondCorrection ((), b) j) =
      if b then ![(5, -5), (27, -9)] j else ![(3, -3), (15, -5)] j := by
  classical
  cases b <;> fin_cases j <;>
    norm_num [firstCorrection, secondCorrection, layerCorrection, normalCorrection,
      coreParameters, pairPoint, coordinatePoint]

private theorem coreLayerValues₁ (j : Fin 2) :
    (D).layerCoefficients (1 : Fin 3) j = ![(-4, 3), (-12, 3)] j := by
  fin_cases j <;>
    norm_num [layerCoefficients, pairedBaseValue_eq, baseCoefficient, normalBasisValue,
      coreParameters, solveLayerNormal]

theorem coreLayerValues₂ (j : Fin 2) :
    (D).layerCoefficients (2 : Fin 3) j = ![(10, -11), (132, -47)] j := by
  fin_cases j <;>
    norm_num [layerCoefficients, pairedBaseValue_eq, baseCoefficient, normalBasisValue,
      coreParameters, solveLayerNormal]

private theorem coreFirstGenerator (b : Bool) :
    firstGenerator (D).firstCorrection ((), b) =
      if b then coreLinear K 0 1 5 27 else coreLinear K 1 0 3 15 := by
  have h₀ := congrArg Prod.fst (coreCorrectionValues K b 0)
  have h₁ := congrArg Prod.fst (coreCorrectionValues K b 1)
  change (D).firstCorrection ((), b) 0 = _ at h₀
  change (D).firstCorrection ((), b) 1 = _ at h₁
  rw [firstGenerator, Fin.sum_univ_two, h₀, h₁]
  cases b <;> norm_num [coreLinear] <;> ring

private theorem coreSecondGenerator (b : Bool) :
    secondGenerator (D).slope (D).secondCorrection ((), b) =
      if b then coreLinear K 0 2 (-5) (-9) else coreLinear K 1 0 (-3) (-5) := by
  have h₀ := congrArg Prod.snd (coreCorrectionValues K b 0)
  have h₁ := congrArg Prod.snd (coreCorrectionValues K b 1)
  change (D).secondCorrection ((), b) 0 = _ at h₀
  change (D).secondCorrection ((), b) 1 = _ at h₁
  rw [secondGenerator, Fin.sum_univ_two, h₀, h₁]
  cases b <;> norm_num [coreLinear, coreParameters] <;> ring

private theorem coreFirstLift₁ : (D).firstLift (1 : Fin 3) = coreLinear K 0 0 (-4) (-12) := by
  rw [firstLift_eq_layerForm, layerForm_apply, Fin.sum_univ_two]
  norm_num [coreLayerValues₁, coreLinear]

private theorem coreFirstLift₂ : (D).firstLift (2 : Fin 3) = coreLinear K 0 0 10 132 := by
  rw [firstLift_eq_layerForm, layerForm_apply, Fin.sum_univ_two]
  norm_num [coreLayerValues₂, coreLinear]

private theorem coreSecondLift₁ : (D).secondLift (1 : Fin 3) = coreLinear K (-1) (-2) 3 3 := by
  rw [secondLift_eq_forms, baseForm_apply, layerForm_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    coreLayerValues₁ K 0, coreLayerValues₁ K 1]
  norm_num [Fintype.univ_bool, coreLinear, baseCoefficient, normalBasisValue, coreParameters]
  ring

private theorem coreSecondLift₂ : (D).secondLift (2 : Fin 3) = coreLinear K 1 1 (-11) (-47) := by
  rw [secondLift_eq_forms, baseForm_apply, layerForm_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    coreLayerValues₂ K 0, coreLayerValues₂ K 1]
  norm_num [Fintype.univ_bool, coreLinear, baseCoefficient, normalBasisValue, coreParameters]
  ring

/-- The actual core t-input, on either of the two distinguished generators. -/
abbrev coreTInput (b : Bool) : ParameterOmega K Unit :=
  untouchedOmega ((), b) (1 : Fin 2)

private theorem coreRawTFormula (b : Bool) :
    phi (D).firstLift (D).secondLift (firstKernelMap (D).firstCorrection)
        (secondKernelMap (D).slope (D).secondCorrection) (coreTInput K b) =
      (-firstGenerator (D).firstCorrection ((), b) * (D).firstLift 1 -
          secondGenerator (D).slope (D).secondCorrection ((), b) * (D).firstLift 2,
       -firstGenerator (D).firstCorrection ((), b) * (D).secondLift 1 -
          secondGenerator (D).slope (D).secondCorrection ((), b) * (D).secondLift 2) := by
  classical
  apply Prod.ext <;>
    simp [coreTInput, phi, prePhi, untouchedOmega, lowerPart, firstKernelMap, secondKernelMap] <;>
    ring

private def coreCorrectionForm (b i : Bool) : MvPolynomial TraceIndex K :=
  match b, i with
  | false, false => coreLinear K 0 (-1) (-41) (-367)
  | false, true => coreLinear K 1 0 33 235
  | true, false => coreLinear K 0 1 (-70) (-666)
  | true, true => coreLinear K (-1) 0 56 426

omit [CharZero K] in
private theorem coreCorrectionForm_homogeneous (b i : Bool) :
    (coreCorrectionForm K b i).IsHomogeneous 1 := by
  cases b <;> cases i <;> exact coreLinear_homogeneous K _ _ _ _

private def coreFlagCombination (a b c : K) : MvPolynomial TraceIndex K :=
  a • coreFlagBasisPolynomial K 0 + b • coreFlagBasisPolynomial K 1 + c • coreFlagBasisPolynomial K 2

omit [CharZero K] in
private theorem coreFlagCombination_mem (a b c : K) :
    coreFlagCombination K a b c ∈ (flagVanishing (K := K) (P := Unit) (J := Fin 2)) := by
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ a (coreFlagBasisPolynomial_vanish K 0))
      (Submodule.smul_mem _ b (coreFlagBasisPolynomial_vanish K 1)))
    (Submodule.smul_mem _ c (coreFlagBasisPolynomial_vanish K 2))

private def coreTResidual (b : Bool) : MvPolynomial TraceIndex K × MvPolynomial TraceIndex K :=
  if b then (coreFlagCombination K 75 693 324, coreFlagCombination K 75 693 (-144))
  else (coreFlagCombination K 30 220 192, coreFlagCombination K 60 440 (-84))

omit [CharZero K] in
private theorem coreTResidual_mem (b : Bool) :
    coreTResidual K b ∈ (flagVanishing (K := K) (P := Unit) (J := Fin 2)).prod
      (flagVanishing (K := K) (P := Unit) (J := Fin 2)) := by
  cases b <;> exact ⟨coreFlagCombination_mem K _ _ _, coreFlagCombination_mem K _ _ _⟩

private theorem coreRawT_sub_residual (b : Bool) :
    phi (D).firstLift (D).secondLift (firstKernelMap (D).firstCorrection)
        (secondKernelMap (D).slope (D).secondCorrection) (coreTInput K b) - coreTResidual K b =
      generatorProduct (D).slope (D).firstCorrection (D).secondCorrection ((), false) (coreCorrectionForm K b false) +
        generatorProduct (D).slope (D).firstCorrection (D).secondCorrection ((), true) (coreCorrectionForm K b true) := by
  rw [coreRawTFormula K]
  cases b <;> apply Prod.ext <;>
    norm_num [generatorProduct, coreFirstGenerator, coreSecondGenerator, coreFirstLift₁, coreFirstLift₂,
      coreSecondLift₁, coreSecondLift₂, coreCorrectionForm, coreTResidual, coreFlagCombination,
      coreFlagBasisPolynomial, coreLinear, Algebra.smul_def, map_ofNat] <;> ring

/-- The projected core t-input equals the explicit residual pair. -/
theorem coreProjectedT_polynomials (b : Bool) :
    quadraticPairInclusion (coreProjectedMap K (coreTInput K b)) = coreTResidual K b := by
  let x := coreTInput K b
  let p := coreProjectedMap K x
  let f := quadraticPhi (D).firstLift (D).secondLift (firstKernelMap (D).firstCorrection)
    (secondKernelMap (D).slope (D).secondCorrection) (D).firstLift_homogeneous (D).secondLift_homogeneous
    (firstKernelMap_homogeneous (D).firstCorrection) (secondKernelMap_homogeneous (D).slope (D).secondCorrection) x
  have hs := projectedEliminatedMap_spec (D).slope (D).firstCorrection (D).secondCorrection
    (D).distinguishedPair (D).normal₀ (D).normal₁ (coreSlope_injective K) (coreNormal₀_ne K)
    (coreNormal₁_ne K) (D).first_normal_equation (D).second_normal_equation (D).firstLift (D).secondLift
    (D).firstLift_homogeneous (D).secondLift_homogeneous (D).actualNormalLiftVanishing x
  change p ∈ coreFlagPairs K ∧ f - p ∈ quadraticMixedImage (D).slope (D).firstCorrection (D).secondCorrection at hs
  have hp : quadraticPairInclusion p ∈ (flagVanishing (K := K) (P := Unit) (J := Fin 2)).prod
      (flagVanishing (K := K) (P := Unit) (J := Fin 2)) := hs.1
  have hm : quadraticPairInclusion f - quadraticPairInclusion p ∈
      mixedImage (D).slope (D).firstCorrection (D).secondCorrection := by
    rw [← map_sub, ← map_quadraticMixedImage]
    exact ⟨f - p, hs.2, rfl⟩
  have hr : quadraticPairInclusion f - coreTResidual K b ∈
      mixedImage (D).slope (D).firstCorrection (D).secondCorrection := by
    change phi (D).firstLift (D).secondLift (firstKernelMap (D).firstCorrection)
      (secondKernelMap (D).slope (D).secondCorrection) (coreTInput K b) - coreTResidual K b ∈ _
    rw [coreRawT_sub_residual K b]
    exact Submodule.add_mem _
      (generatorProduct_mem_mixedImage _ _ _ _ _ (coreCorrectionForm_homogeneous K b false))
      (generatorProduct_mem_mixedImage _ _ _ _ _ (coreCorrectionForm_homogeneous K b true))
  have hd : quadraticPairInclusion p - coreTResidual K b ∈
      mixedImage (D).slope (D).firstCorrection (D).secondCorrection := by
    rw [show quadraticPairInclusion p - coreTResidual K b =
      (quadraticPairInclusion f - coreTResidual K b) -
        (quadraticPairInclusion f - quadraticPairInclusion p) by abel]
    exact Submodule.sub_mem _ hr hm
  have hW := Submodule.sub_mem _ hp (coreTResidual_mem K b)
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp
    (mixedImage_disjoint_flagVanishing (D).slope (D).firstCorrection (D).secondCorrection (coreSlope_injective K)))
    _ hd hW)

/-- The two actual t-inputs have the two columns of the injective core matrix. -/
theorem coreProjectedT_probe (b : Bool) :
    let w := coreProjectedMap K (coreTInput K b)
    (eval (coreProbePoint K 0) w.1.val, eval (coreProbePoint K 0) w.2.val) =
      if b then (75, 75) else (30, 60) := by
  change (eval (coreProbePoint K 0) (quadraticPairInclusion (coreProjectedMap K (coreTInput K b))).1,
      eval (coreProbePoint K 0) (quadraticPairInclusion (coreProjectedMap K (coreTInput K b))).2) = _
  rw [coreProjectedT_polynomials K b]
  cases b <;>
    norm_num [coreTResidual, coreFlagCombination, Algebra.smul_def, coreFlagBasisPolynomial_probe]

end Core

section Transport

open QuadraticTraceRestriction

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

/-- The first core probe, extended by zero on the unselected variables. -/
def embeddedCoreTProbe (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J) : (P × Bool) ⊕ J → K :=
  extendPoint K (traceEmbedding D.distinguishedPair e) (coreProbePoint K 0)

omit [Fintype P] [Fintype J] in
/-- An untouched pair has equal coordinates at this embedded probe. -/
theorem embeddedCoreTProbe_equal (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (i : P × Bool) (hi : i.1 ≠ D.distinguishedPair) :
    embeddedCoreTProbe D e (.inl i) = embeddedCoreTProbe D e (.inl (partner i)) := by
  have h₀ : Sum.inl i ∉ Set.range (traceEmbedding D.distinguishedPair e) :=
    fun h => hi ((inl_mem_range_traceEmbedding D.distinguishedPair e i).mp h)
  have h₁ : Sum.inl (partner i) ∉ Set.range (traceEmbedding D.distinguishedPair e) :=
    fun h => hi ((inl_mem_range_traceEmbedding D.distinguishedPair e (partner i)).mp h)
  exact (extendPoint_off K _ _ h₀).trans (extendPoint_off K _ _ h₁).symm

omit [Fintype P] [Fintype J] in
/-- Extending the core t-input retains the one distinguished mixed coefficient. -/
theorem extendOmega_coreTInput (D : QuadraticLiftParameters K P J) (b : Bool) :
    extendOmega D (coreTInput K b) = untouchedOmega (D.distinguishedPair, b) (1 : Fin 2) := by
  classical
  have hzero : extendKernel D (0 : KernelCoefficients K) = 0 := by
    funext i
    simp [extendKernel]
  apply Subtype.ext
  simp [extendOmega, coreTInput, untouchedOmega, hzero]
  funext i
  rcases i with ⟨p, k⟩
  by_cases hp : p = D.distinguishedPair
  · subst p
    simp [extendKernel, Pi.single_apply]
  · simp [extendKernel, hp]

variable [CharZero K]

omit [Fintype J] in
/-- The canonical first layer has nonzero first component in the third lift. -/
theorem fixedCore_thirdLift_firstLayer_ne (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (hD : restrictParameters D e = coreParameters K) :
    (D.layerCoefficients (2 : Fin 3) (e 0)).1 ≠ 0 := by
  have hv := congrArg (fun d : QuadraticLiftParameters K Unit (Fin 2) => d.layerCoefficients (2 : Fin 3) 0) hD
  rw [restrictParameters_layerCoefficients, coreLayerValues₂] at hv
  have h : (D.layerCoefficients (2 : Fin 3) (e 0)).1 = 10 := congrArg Prod.fst hv
  rw [h]
  norm_num

/-- Restriction gives the two actual core responses in every fixed-core extension. -/
theorem fixedCore_projectedT_probe (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (hc : Function.Injective D.slope) (hD : restrictParameters D e = coreParameters K) (b : Bool) :
    projectedProbe D hc (embeddedCoreTProbe D e) (untouchedOmega (D.distinguishedPair, b) (1 : Fin 2)) =
      if b then (75, 75) else (30, 60) := by
  have h := restrict_fixedCore_projectedMap D e hc hD (coreTInput K b)
  change restrictPair K (traceEmbedding D.distinguishedPair e)
    (D.actualProjectedPairMap hc (extendOmega D (coreTInput K b))) =
      coreProjectedMap K (coreTInput K b) at h
  rw [extendOmega_coreTInput] at h
  have he := congrArg (fun f : Quadrics K TraceIndex × Quadrics K TraceIndex =>
    (eval (coreProbePoint K 0) f.1.val, eval (coreProbePoint K 0) f.2.val)) h
  simpa only [projectedProbe_apply, restrictPair_fst, restrictPair_snd, eval_restrict, embeddedCoreTProbe] using
    he.trans (coreProjectedT_probe K b)

/-- The missing-generator test and exactly one probe per pair. The distinguished
pair uses the embedded core probe and every other pair uses the first layer. -/
def fixedFirstLayerConstraintProbeMap (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (hc : Function.Injective D.slope) : ParameterOmega K P →ₗ[K]
      ((MvPolynomial ((P × Bool) ⊕ J) K × K) × ((K × K) × ({p : P // p ≠ D.distinguishedPair} → K × K))) :=
  (missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)).prod
    ((projectedProbe D hc (embeddedCoreTProbe D e)).prod
      (LinearMap.pi fun p : {p : P // p ≠ D.distinguishedPair} => projectedProbe D hc (pairProbe p.val (e 0))))

/-- The actual fixed-core configuration gives an injective map using one probe per pair. -/
theorem fixedFirstLayerConstraintProbe_injective (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (hc : Function.Injective D.slope) (hD : restrictParameters D e = coreParameters K)
    (hγ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → D.pairGamma i (1 : Fin 2) (e 0) ≠ 0) :
    Function.Injective (fixedFirstLayerConstraintProbeMap D e hc) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hC := congrArg Prod.fst hx
  have hP := congrArg Prod.snd hx
  have hCore := congrArg Prod.fst hP
  have hPairs := congrArg Prod.snd hP
  let α := x.val.1.2
  let β := x.val.2.2
  let a := x.val.1.1 1
  let b := x.val.1.1 2
  have hparam : omegaFromParameters α β a b = x := omegaFromParameters_represents x
  have hC' : missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)
      (omegaFromParameters α β a b) = 0 := by rw [hparam]; exact hC
  obtain ⟨hα, ha, hb⟩ := first_parameters_eq_zero D α β a b (e 0)
    (fixedCore_thirdLift_firstLayer_ne D e hD) hC'
  have hβx : omegaBeta β = x := by simpa only [hα, ha, hb, omegaFromParameters_beta] using hparam
  have hzero : projectedProbe D hc (embeddedCoreTProbe D e) (omegaBeta β) = 0 := by
    rw [hβx]
    exact hCore
  have hcore := beta_core_eq_zero D hc (embeddedCoreTProbe D e) β
    (embeddedCoreTProbe_equal D e) (by simpa using fixedCore_projectedT_probe D e hc hD false)
    (by simpa using fixedCore_projectedT_probe D e hc hD true) hzero
  have hβ : β = 0 := by
    funext i
    rcases i with ⟨p, k⟩
    change β (p, k) = 0
    by_cases hp : p = D.distinguishedPair
    · subst p
      cases k
      · exact hcore.1
      · exact hcore.2
    · have hz : projectedProbe D hc (pairProbe p (e 0)) (omegaBeta β) = 0 := by
        rw [hβx]
        exact congrFun hPairs ⟨p, hp⟩
      have hp' := beta_pair_products_eq_zero D hc β hcore p hp (e 0) hz
      cases k
      · exact (mul_eq_zero.mp hp'.1).resolve_right (hγ (p, false) hp)
      · exact (mul_eq_zero.mp hp'.2).resolve_right (hγ (p, true) hp)
  rw [← hβx, hβ, map_zero]

end Transport

end IdealGeneration.QuadraticInjectiveCoreBridge
