module

public import IdealGeneration.QuadraticCoreMultiplication
public import IdealGeneration.QuadraticFlagLiftWitness
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The six-point residual multiplication in the nested two-normal model. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreMiddle
open MvPolynomial Module QuadraticFlag QuadraticElimination
open QuadraticCoreMultiplication

abbrev TraceIndex := (Unit × Bool) ⊕ Fin 2
abbrev KernelCoefficients (K : Type*) := Unit × Bool → K
abbrev CoreLift (K : Type*) := LiftSpace (K := K) (H := KernelCoefficients K)

/-- The paper's order `s,t,y₁,y₂,z₁,z₂`. -/
def variableEquiv : Bool ⊕ TraceIndex ≃ Fin 6 where
  toFun
    | .inl false => 0
    | .inl true => 1
    | .inr (.inl (_, false)) => 2
    | .inr (.inl (_, true)) => 3
    | .inr (.inr j) => j.natAdd 4
  invFun k := ![Sum.inl false, Sum.inl true,
    Sum.inr (Sum.inl ((), false)), Sum.inr (Sum.inl ((), true)),
    Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)] k
  left_inv x := by
    rcases x with b | (⟨u, b⟩ | j)
    · cases b <;> rfl
    · cases u
      cases b <;> rfl
    · fin_cases j <;> rfl
  right_inv k := by
    fin_cases k <;> rfl

/-- The inclusion of the four trace variable indices. -/
def traceIndex (j : TraceIndex) : Fin 6 := variableEquiv (.inr j)

variable (K : Type*) [Field K]

/-- Flatten the nested normal/trace polynomial ring and put its variables in the core order. -/
def flatten : MvPolynomial Bool (MvPolynomial TraceIndex K) ≃ₐ[K] Poly K 6 :=
  (MvPolynomial.sumAlgEquiv K Bool TraceIndex).symm.trans (renameEquiv K variableEquiv)

@[simp] theorem flatten_X_false : flatten K (X false) = X 0 := by
  simp [flatten, variableEquiv]

@[simp] theorem flatten_X_true : flatten K (X true) = X 1 := by
  simp [flatten, variableEquiv]

@[simp] theorem flatten_C (f : MvPolynomial TraceIndex K) :
    flatten K (C f) = rename traceIndex f := by
  have h : (flatten K).toAlgHom.comp (normalEmbedding (K := K)) = rename traceIndex := by
    ext j
    simp [flatten, traceIndex]
  exact congrArg (fun q : MvPolynomial TraceIndex K →ₐ[K] Poly K 6 => q f) h

/-- Restrict a six-coordinate point to its four trace entries. -/
def traceAt (z : Fin 6 → K) : TraceIndex → K := fun j => z (traceIndex j)

/-- The actual six projected cone supports in their displayed order. -/
def coreTracePoint (i : Fin 6) : TraceIndex → K :=
  ![traceBasePoint ((), false), traceBasePoint ((), true),
    layerPoint 0, pairedLayerPoint () 0, layerPoint 1, pairedLayerPoint () 1] i

variable [CharZero K]

set_option maxHeartbeats 800000 in
/-- The flattened core point matrix has exactly these trace projections. -/
theorem traceAt_pointMatrix (i : Fin 6) :
    traceAt K (pointMatrix K i) = coreTracePoint K i := by
  classical
  funext j
  fin_cases i <;> rcases j with ⟨u, b⟩ | j
  all_goals try cases u
  all_goals first | cases b | fin_cases j
  all_goals norm_num [traceAt, traceIndex, variableEquiv, pointMatrix, quadraticCoreConeMatrix,
    coreTracePoint, traceBasePoint, layerPoint, pairedLayerPoint, pairPoint, coordinatePoint]

/-- The two normal columns are retained as actual coordinate values. -/
theorem normalS_values (i : Fin 6) : normalS K i = ![(1 : K), 2, 1, 2, 1, 3] i := by
  fin_cases i <;> norm_num [normalS, pointMatrix, quadraticCoreConeMatrix]

theorem normalT_values (i : Fin 6) : normalT K i = ![(-1 : K), -1, 1, 4, 3, 12] i := by
  fin_cases i <;> norm_num [normalT, pointMatrix, quadraticCoreConeMatrix]

/-- The explicit layer directions and heights of the six cone points. -/
def coreParameters : QuadraticLiftParameters K Unit (Fin 2) where
  slope i := if i.2 then 2 else 1
  distinguishedPair := ()
  normal₀ j := ![(1, 1), (1, 3)] j
  normal₁ j := ![(1, 2), (1, 4)] j
  baseHeight := fun _ => 1
  height₀ := fun _ => 1
  height₁ j := ![(2 : K), 3] j
  baseHeight_ne := by intro i; norm_num
  height₀_ne := by intro j; norm_num
  height₁_ne := by intro j; fin_cases j <;> norm_num
  determinant_ne := by intro j; fin_cases j <;> norm_num

theorem coreSlope_injective : Function.Injective (coreParameters K).slope := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  cases u
  cases v
  cases a <;> cases b
  · rfl
  · norm_num [coreParameters] at h
  · norm_num [coreParameters] at h
  · rfl

section RepresentedQuadrics

variable (U V : Fin 3 → MvPolynomial TraceIndex K)
  (g₁ g₂ : KernelCoefficients K →ₗ[K] MvPolynomial TraceIndex K)

omit [CharZero K] in
/-- Flattening a represented quadric preserves its three normal coefficients
and embeds the trace coefficients by renaming. -/
theorem flatten_normalPolynomialMap (x : CoreLift K) :
    flatten K (normalPolynomialMap U V g₁ g₂ x) =
      liftedQuadratic (rename traceIndex) (X 0) (X 1) U V g₁ g₂ x := by
  simp [liftedQuadratic, quadraticExpression]

omit [CharZero K] in
/-- The represented quadric is homogeneous in all six coordinates. -/
theorem flattenedQuadric_homogeneous
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (x : CoreLift K) : (flatten K (normalPolynomialMap U V g₁ g₂ x)).IsHomogeneous 2 := by
  rw [flatten_normalPolynomialMap]
  have hs := isHomogeneous_X K (0 : Fin 6)
  have ht := isHomogeneous_X K (1 : Fin 6)
  have h0 := (hs.pow 2).C_mul (x.1 0)
  have h1 := (hs.mul ht).C_mul (x.1 1)
  have h2 := (ht.pow 2).C_mul (x.1 2)
  have hq : (quadraticExpression (X (0 : Fin 6)) (X 1)
      (fun i => algebraMap K (Poly K 6) (x.1 i))).IsHomogeneous 2 := by
    simp only [quadraticExpression, MvPolynomial.algebraMap_eq, mul_assoc]
    exact (h0.add h1).add h2
  have hu := lowerPart_homogeneous U g₁ hU hg₁ x
  have hv := lowerPart_homogeneous V g₂ hV hg₂ x
  exact (hq.add (hs.mul hu.rename_isHomogeneous)).add (ht.mul hv.rename_isHomogeneous)

omit [CharZero K] in
@[simp] theorem flattenedQuadric_restrict (x : CoreLift K) :
    coneRestrict K 2 4 (flatten K (normalPolynomialMap U V g₁ g₂ x)) = 0 := by
  have hs : coneRestrict K 2 4 (X (0 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 0
  have ht : coneRestrict K 2 4 (X (1 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 1
  rw [flatten_normalPolynomialMap]
  simp [liftedQuadratic, quadraticExpression, hs, ht]

omit [CharZero K] in
/-- Evaluating the flattened polynomial evaluates the original trace
coefficients at the projected support. -/
theorem flattenedQuadric_eval (z : Fin 6 → K) (x : CoreLift K) :
    eval z (flatten K (normalPolynomialMap U V g₁ g₂ x)) =
      liftedQuadratic (aeval (traceAt K z)) (z 0) (z 1) U V g₁ g₂ x := by
  rw [flatten_normalPolynomialMap]
  have hz : z ∘ traceIndex = traceAt K z := rfl
  simp [liftedQuadratic, quadraticExpression, eval_rename, hz]

/-- The six prescribed cone evaluations of the represented family vanish. -/
def ConeVanishing : Prop :=
  ∀ (i : Fin 6) (x : CoreLift K), liftedQuadratic (aeval (coreTracePoint K i))
    (normalS K i) (normalT K i) U V g₁ g₂ x = 0

omit [CharZero K] in
/-- Pure-normal coefficients are recovered from the polynomial. The remaining
mixed coefficients are recovered from the first mixed kernel map. -/
theorem representedQuadric_injective (hg : Function.Injective g₁) :
    Function.Injective (normalPolynomialMap U V g₁ g₂) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h : C (C (x.1 0)) * X false ^ 2 + C (C (x.1 1)) * X false * X true +
      C (C (x.1 2)) * X true ^ 2 + C (lowerPart U g₁ x) * X false +
      C (lowerPart V g₂ x) * X true = 0 := by
    simpa only [normalPolynomialMap_apply, liftedQuadratic, quadraticExpression,
      MvPolynomial.algebraMap_apply, Algebra.algebraMap_self_apply,
      normalEmbedding_apply, mul_comm] using hx
  obtain ⟨_, _, _, _, h0, h1, h2, hA, _⟩ :=
    IdealGeneration.QuadraticNormalCoefficients.normalDegree_separation
      (R := MvPolynomial TraceIndex K) 0 0 0 0 (C (x.1 0)) (C (x.1 1)) (C (x.1 2))
      (lowerPart U g₁ x) (lowerPart V g₂ x) 0 0 (by
        simpa only [map_zero, zero_mul, zero_add, add_zero] using h)
  have hq : x.1 = 0 := by
    funext i
    fin_cases i
    · change x.1 0 = 0
      exact MvPolynomial.C_injective TraceIndex K (by simpa only [map_zero] using h0)
    · change x.1 1 = 0
      exact MvPolynomial.C_injective TraceIndex K (by simpa only [map_zero] using h1)
    · change x.1 2 = 0
      exact MvPolynomial.C_injective TraceIndex K (by simpa only [map_zero] using h2)
  have hk : g₁ x.2 = 0 := by
    simpa [lowerPart, hq] using hA
  have hx₂ : x.2 = 0 := hg (by simpa only [map_zero] using hk)
  exact Prod.ext hq hx₂

variable (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
  (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
  (hvan : ConeVanishing K U V g₁ g₂)

/-- The represented quadrics map into the actual six-point residual space. -/
def representedToResidual : CoreLift K →ₗ[K] residualPiece K 2 where
  toFun x := ⟨⟨flatten K (normalPolynomialMap U V g₁ g₂ x),
    flattenedQuadric_homogeneous K U V g₁ g₂ hU hV hg₁ hg₂ x⟩,
    (mem_residualPiece K _).mpr ⟨fun i => by
      rw [flattenedQuadric_eval, traceAt_pointMatrix]
      exact hvan i x,
      flattenedQuadric_restrict K U V g₁ g₂ x⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten K).toAlgHom.toLinearMap.comp (normalPolynomialMap U V g₁ g₂)).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten K).toAlgHom.toLinearMap.comp (normalPolynomialMap U V g₁ g₂)).map_smul a x

theorem representedToResidual_injective (hg : Function.Injective g₁) :
    Function.Injective (representedToResidual K U V g₁ g₂ hU hV hg₁ hg₂ hvan) := by
  intro x y h
  apply representedQuadric_injective K U V g₁ g₂ hg
  apply (flatten K).injective
  exact congrArg (fun f => f.val.val) h

omit [CharZero K] in
theorem finrank_coreLift : finrank K (CoreLift K) = 5 := by
  change finrank K ((Fin 3 → K) × (Unit × Bool → K)) = 5
  simp [Module.finrank_prod]

/-- The five represented parameters exhaust the actual residual quadric space. -/
theorem representedToResidual_surjective (hg : Function.Injective g₁) :
    Function.Surjective (representedToResidual K U V g₁ g₂ hU hV hg₁ hg₂ hvan) := by
  let : AddCommGroup (residualPiece K 2) := Module.addCommMonoidToAddCommGroup K
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj (representedToResidual_injective K U V g₁ g₂
    hU hV hg₁ hg₂ hvan hg), finrank_coreLift, finrank_residualQuadrics]

/-- Regroup a six-coordinate source into its two normal and four trace coefficients. -/
def middleSourceOf (x : Fin 6 → CoreLift K) :
    (CoreLift K × CoreLift K) × (TraceIndex → CoreLift K) :=
  ((x 0, x 1), fun j => x (traceIndex j))

/-- Flattening identifies the nested multiplication with actual coordinate multiplication. -/
theorem flatten_middleMultiplication (x : Fin 6 → CoreLift K) :
    flatten K (middleMultiplication U V g₁ g₂ (middleSourceOf K x)) =
      (residualMultiplication K (fun k => representedToResidual K U V g₁ g₂
        hU hV hg₁ hg₂ hvan (x k))).val.val := by
  rw [residualMultiplication_val]
  change _ = ∑ k, X k * flatten K (normalPolynomialMap U V g₁ g₂ (x k))
  rw [← variableEquiv.sum_comp (fun k => X k * flatten K (normalPolynomialMap U V g₁ g₂ (x k))),
    Fintype.sum_sum_type, Fintype.sum_bool]
  simp [middleSourceOf, traceProduct, traceIndex, variableEquiv]
  all_goals abel

end RepresentedQuadrics

/-- The normal coordinates recovered from the chosen directions and heights. -/
def coreNormalPoint (i : Fin 6) : K × K :=
  let D := coreParameters K
  ![(D.baseHeight ((), false) * D.slope ((), false), D.baseHeight ((), false) * (-1)),
    (D.baseHeight ((), true) * D.slope ((), true), D.baseHeight ((), true) * (-1)),
    (D.height₀ 0 * (D.normal₀ 0).1, D.height₀ 0 * (D.normal₀ 0).2),
    (D.height₁ 0 * (D.normal₁ 0).1, D.height₁ 0 * (D.normal₁ 0).2),
    (D.height₀ 1 * (D.normal₀ 1).1, D.height₀ 1 * (D.normal₀ 1).2),
    (D.height₁ 1 * (D.normal₁ 1).1, D.height₁ 1 * (D.normal₁ 1).2)] i

theorem coreNormalPoint_eq (i : Fin 6) :
    (normalS K i, normalT K i) = coreNormalPoint K i := by
  fin_cases i <;> norm_num [normalS_values, normalT_values, coreNormalPoint, coreParameters]

/-- The actual explicit lifts vanish at all six displayed cone points. -/
theorem actualConeVanishing :
    ConeVanishing K (coreParameters K).firstLift (coreParameters K).secondLift
      (firstKernelMap (coreParameters K).firstCorrection)
      (secondKernelMap (coreParameters K).slope (coreParameters K).secondCorrection) := by
  intro i x
  have he := coreNormalPoint_eq K i
  rw [show normalS K i = (coreNormalPoint K i).1 from congrArg Prod.fst he,
    show normalT K i = (coreNormalPoint K i).2 from congrArg Prod.snd he]
  let C := (coreParameters K).actualNormalLiftVanishing
  fin_cases i
  · exact C.base ((), false) x
  · exact C.base ((), true) x
  · exact C.layer₀ 0 x
  · exact C.layer₁ 0 x
  · exact C.layer₀ 1 x
  · exact C.layer₁ 1 x

theorem firstKernelMap_injective :
    Function.Injective (firstKernelMap (coreParameters K).firstCorrection) := by
  intro x y h
  funext i
  simpa only [eval_firstKernelMap_base] using congrArg (eval (traceBasePoint i)) h

/-- The scalar flag ideal in the four trace variables. -/
abbrev coreFlagIdeal : Submodule K (Quadrics K TraceIndex) :=
  quadraticFlagVanishing (K := K) (P := Unit) (J := Fin 2)

abbrev coreFlagPairs : Submodule K (Quadrics K TraceIndex × Quadrics K TraceIndex) :=
  (coreFlagIdeal K).prod (coreFlagIdeal K)

/-- The six projected cone supports as indices of the flag. -/
def coreSupport (i : Fin 6) : FlagIndex Unit (Fin 2) :=
  ![.base ((), false), .base ((), true), .layer 0, .layerPair () 0,
    .layer 1, .layerPair () 1] i

omit [CharZero K] in
theorem coreTracePoint_eq_flagPoint (i : Fin 6) :
    coreTracePoint K i = flagPoint (coreSupport i) := by
  classical
  fin_cases i <;> funext j <;> rcases j with ⟨u, b⟩ | j
  all_goals try cases u
  all_goals first | cases b | fin_cases j
  all_goals norm_num [coreTracePoint, coreSupport, flagPoint, traceBasePoint, layerPoint,
    pairedLayerPoint, pairPoint, coordinatePoint]

omit [CharZero K] in
theorem eval_coreTracePoint_of_flag (f : Quadrics K TraceIndex)
    (hf : f ∈ coreFlagIdeal K) (i : Fin 6) : eval (coreTracePoint K i) f.val = 0 := by
  change ∀ t : FlagIndex Unit (Fin 2), eval (flagPoint t) f.val = 0 at hf
  rw [coreTracePoint_eq_flagPoint]
  exact hf _

omit [CharZero K] in
/-- The normal-linear embedding commutes with flattening. -/
theorem flatten_normalPairMap (f : MvPolynomial TraceIndex K × MvPolynomial TraceIndex K) :
    flatten K (normalPairMap f) = rename traceIndex f.1 * X 0 + rename traceIndex f.2 * X 1 := by
  simp

/-- A pair of flag equations gives a genuine normal-ideal cubic at the six points. -/
def flagPairCubic (f : Quadrics K TraceIndex × Quadrics K TraceIndex)
    (hf : f ∈ coreFlagPairs K) : residualPiece K 3 :=
  ⟨⟨flatten K (normalPairMap (f.1.val, f.2.val)), by
    rw [flatten_normalPairMap]
    exact (f.1.property.rename_isHomogeneous.mul (isHomogeneous_X K (0 : Fin 6))).add
      (f.2.property.rename_isHomogeneous.mul (isHomogeneous_X K (1 : Fin 6)))⟩,
    (mem_residualPiece K _).mpr ⟨fun i => by
      change (f.1 ∈ coreFlagIdeal K) ∧ (f.2 ∈ coreFlagIdeal K) at hf
      have ht : pointMatrix K i ∘ traceIndex = coreTracePoint K i := traceAt_pointMatrix K i
      change eval (pointMatrix K i) (flatten K (normalPairMap (f.1.val, f.2.val))) = 0
      rw [flatten_normalPairMap]
      simp only [map_add, map_mul, eval_rename, eval_X, ht,
        eval_coreTracePoint_of_flag K f.1 hf.1 i, eval_coreTracePoint_of_flag K f.2 hf.2 i,
        zero_mul, add_zero], by
      have hs : coneRestrict K 2 4 (X (0 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 0
      have ht : coneRestrict K 2 4 (X (1 : Fin 6)) = 0 := coneRestrict_X_normal K 2 4 1
      change coneRestrict K 2 4 (flatten K (normalPairMap (f.1.val, f.2.val))) = 0
      rw [flatten_normalPairMap]
      simp [hs, ht]⟩⟩

/-- Every pair of core flag equations is the normal-linear part of an
actual represented multiplication. -/
theorem flagPair_in_middleMultiplication_range
    (U V : Fin 3 → MvPolynomial TraceIndex K)
    (g₁ g₂ : KernelCoefficients K →ₗ[K] MvPolynomial TraceIndex K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (hvan : ConeVanishing K U V g₁ g₂) (hg : Function.Injective g₁)
    (f : Quadrics K TraceIndex × Quadrics K TraceIndex) (hf : f ∈ coreFlagPairs K) :
    normalPairMap (f.1.val, f.2.val) ∈ (middleMultiplication U V g₁ g₂).range := by
  classical
  obtain ⟨p, hp⟩ := residualMultiplication_surjective K (flagPairCubic K f hf)
  choose x hx using fun j => representedToResidual_surjective K U V g₁ g₂ hU hV hg₁ hg₂ hvan hg (p j)
  have he : (fun j => representedToResidual K U V g₁ g₂ hU hV hg₁ hg₂ hvan (x j)) = p :=
    funext hx
  refine ⟨middleSourceOf K x, (flatten K).injective ?_⟩
  rw [flatten_middleMultiplication K U V g₁ g₂ hU hV hg₁ hg₂ hvan, he, hp]
  all_goals rfl

/-- The actual normal-linear product space for the six-point core. -/
abbrev coreMiddleSpace : Submodule K (Quadrics K TraceIndex × Quadrics K TraceIndex) :=
  let D := coreParameters K
  quadraticMiddleSpace D.firstLift D.secondLift D.slope D.firstCorrection D.secondCorrection

theorem coreFlagPairs_le_middleSpace : coreFlagPairs K ≤ coreMiddleSpace K := by
  intro f hf
  let D := coreParameters K
  exact flagPair_in_middleMultiplication_range K D.firstLift D.secondLift
    (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
    D.firstLift_homogeneous D.secondLift_homogeneous
    (firstKernelMap_homogeneous D.firstCorrection)
    (secondKernelMap_homogeneous D.slope D.secondCorrection)
    (actualConeVanishing K) (firstKernelMap_injective K) f hf

/-- The core residual pair space `W'` is the full pair of scalar flag ideals. -/
theorem coreMiddleSpace_inf_flag : coreMiddleSpace K ⊓ coreFlagPairs K = coreFlagPairs K :=
  inf_eq_right.mpr (coreFlagPairs_le_middleSpace K)

theorem coreNormal₀_ne (j : Fin 2) : (coreParameters K).normal₀ j ≠ 0 := by
  intro hz
  have h := (coreParameters K).determinant_ne j
  simp [hz] at h

theorem coreNormal₁_ne (j : Fin 2) : (coreParameters K).normal₁ j ≠ 0 := by
  intro hz
  have h := (coreParameters K).determinant_ne j
  simp [hz] at h

/-- The core normal-linear product space fills all the allowed pairs. -/
theorem coreMiddleSpace_eq_allowed : coreMiddleSpace K =
    allowedQuadraticPairs (coreParameters K).slope () (coreParameters K).normal₀
      (coreParameters K).normal₁ := by
  let D := coreParameters K
  have hsplit := quadratic_flag_direct_sum D.slope D.firstCorrection D.secondCorrection
    D.distinguishedPair D.normal₀ D.normal₁ (coreSlope_injective K) (coreNormal₀_ne K)
    (coreNormal₁_ne K) D.first_normal_equation D.second_normal_equation
  have hmiddle : coreMiddleSpace K = quadraticMixedImage D.slope D.firstCorrection D.secondCorrection ⊔
      (quadraticPhi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
        (secondKernelMap D.slope D.secondCorrection) D.firstLift_homogeneous D.secondLift_homogeneous
        (firstKernelMap_homogeneous D.firstCorrection)
        (secondKernelMap_homogeneous D.slope D.secondCorrection)).range :=
    quadraticMiddleSpace_eq D.firstLift D.secondLift D.slope D.firstCorrection D.secondCorrection
      D.firstLift_homogeneous D.secondLift_homogeneous
  apply le_antisymm
  · rw [hmiddle]
    apply sup_le
    · exact quadraticMixedImage_le_allowed D.slope D.firstCorrection D.secondCorrection
        D.distinguishedPair D.normal₀ D.normal₁ D.first_normal_equation D.second_normal_equation
    · rintro f ⟨x, rfl⟩
      exact quadraticPhi_mem_allowed D.slope D.distinguishedPair D.normal₀ D.normal₁
        D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
        (secondKernelMap D.slope D.secondCorrection) D.firstLift_homogeneous D.secondLift_homogeneous
        (firstKernelMap_homogeneous D.firstCorrection)
        (secondKernelMap_homogeneous D.slope D.secondCorrection) D.actualNormalLiftVanishing x
  · change allowedQuadraticPairs D.slope D.distinguishedPair D.normal₀ D.normal₁ ≤ coreMiddleSpace K
    rw [hsplit.1]
    apply sup_le
    · rw [hmiddle]
      exact le_sup_left
    · exact coreFlagPairs_le_middleSpace K

theorem finrank_coreFlagIdeal : finrank K (coreFlagIdeal K) = 3 := by
  have h := finrank_quadraticFlagVanishing (J := Fin 2) (coreParameters K).slope () (coreSlope_injective K)
  norm_num [flagCount, N, Nat.choose, Fintype.card_prod] at h
  exact h

theorem finrank_coreFlagPairs : finrank K (coreFlagPairs K) = 6 := by
  have : Module.Free K (coreFlagIdeal K) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (coreFlagIdeal K)
  change finrank K ((coreFlagIdeal K).prod (coreFlagIdeal K)) = 6
  rw [(Submodule.prodEquiv (coreFlagIdeal K) (coreFlagIdeal K)).finrank_eq,
    Module.finrank_prod, finrank_coreFlagIdeal]

/-- The actual projected elimination map on the six-point core. -/
def coreProjectedMap :=
  let D := coreParameters K
  projectedEliminatedMap D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ (coreSlope_injective K) (coreNormal₀_ne K) (coreNormal₁_ne K)
    D.first_normal_equation D.second_normal_equation D.firstLift D.secondLift
    D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing

/-- Every pair of core flag equations is reached by the projected elimination map. -/
theorem coreProjectedMap_range : (coreProjectedMap K).range = coreFlagPairs K := by
  let D := coreParameters K
  have h := quadraticMiddleSpace_inf_flag D.slope D.firstCorrection D.secondCorrection
    D.distinguishedPair D.normal₀ D.normal₁ (coreSlope_injective K) (coreNormal₀_ne K)
    (coreNormal₁_ne K) D.first_normal_equation D.second_normal_equation
    D.firstLift D.secondLift D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing
  exact h.symm.trans (coreMiddleSpace_inf_flag K)

theorem finrank_coreProjectedMap_range : finrank K (coreProjectedMap K).range = 6 := by
  rw [coreProjectedMap_range, finrank_coreFlagPairs]

end IdealGeneration.QuadraticCoreMiddle
