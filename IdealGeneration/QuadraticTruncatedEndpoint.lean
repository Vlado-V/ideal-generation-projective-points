module

public import IdealGeneration.QuadraticResidualCoordinates
public import IdealGeneration.QuadraticTraceRepresentation
public import IdealGeneration.QuadraticTruncatedKernel
public import IdealGeneration.QuadraticTruncatedCone

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual appended-cone middle map at the injective endpoint. -/

noncomputable section
namespace IdealGeneration.QuadraticTruncatedEndpoint
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticVariableTransport
open QuadraticConeResidual QuadraticMiddleRank QuadraticMiddleEndpoint QuadraticAugmentedEvaluation
open QuadraticCoreRestriction QuadraticTracePostulation QuadraticTraceRepresentation
open QuadraticFlagFamily QuadraticFlagProbeScalar QuadraticTruncatedCone QuadraticTruncatedKernel
open QuadraticInjectiveCoreBridge QuadraticLiftParameters

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable {m p q : ℕ} (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q)

local notation "T" => ((P × Bool) ⊕ J)
local notation "L" => ResidualCoordinates (K := K) (P := P)
local instance residualCubicGroup : AddCommGroup (C.residualPiece 3) :=
  Module.addCommMonoidToAddCommGroup K
local instance flagPairGroup : AddCommGroup (FlagQuadricPairs K P J) :=
  Module.addCommMonoidToAddCommGroup K

private def pureNormalPoint : Fin (2 + m) → K :=
  pointOf e (fun b => if b then 0 else 1) (0 : T → K)

local notation "es" => pureNormalPoint (K := K) e

/-- The pure normal coordinate reads exactly the first lift coefficient. -/
theorem eval_representedQuadric_es (D : QuadraticLiftParameters K P J) (a : L) :
    eval es (flatten e (representedQuadric D a)) = a.1 0 := by
  have hU := lowerPart_homogeneous D.firstLift (firstKernelMap D.firstCorrection)
    D.firstLift_homogeneous (firstKernelMap_homogeneous _) a
  have hU0 : constantCoeff (lowerPart D.firstLift (firstKernelMap D.firstCorrection) a) = 0 := by
    simpa using homogeneous_eval_scale hU (0 : T → K) (0 : K)
  rw [pureNormalPoint, eval_flatten]
  simp [representedQuadric, liftedQuadratic, quadraticExpression, aevalTower_C, hU0]

/-- The first lift separates the added pure normal point from all old points. -/
theorem exists_residual_separator (D : QuadraticLiftParameters K P J)
    (h : Compatible D e r C) (qidx : Fin q) :
    ∃ Q : C.residualPiece 2, eval ((append C qidx).point (Fin.last p)) Q.val.val = 1 := by
  let a : L := (![(1 : K),0,0],0)
  refine ⟨representedToResidual D e r C h a, ?_⟩
  rw [append_point_last C qidx e, representedToResidual_val]
  exact eval_representedQuadric_es e D a

section Canonical

variable (K) [CharZero K] [DecidableEq J]
variable (p₀ : P) (layers : Bool → J)
local notation "D" => parameters K p₀ layers
local notation "hc" => parameters_slope_injective K p₀ layers
local notation "extra" => (probePoint (K := K) p₀ layers ∘ firstLayerProbeEmbedding p₀)
local notation "ev" => extraPairEvaluation extra

/-- Appending the pure normal point gives injective actual middle multiplication. -/
theorem canonical_truncated_middleMultiplication_injective
    (hne : layers false ≠ layers true)
    (h : Compatible D e r C)
    (k : TraceLabel P J (FirstLayerProbeLabel p₀) ≃ Fin q)
    (htrace : ∀ t, C.trace (k t) = traceLabelPoint extra t ∘ e.symm)
    (qidx : Fin q) :
    Function.Injective ((append C qidx).middleMultiplication 2) := by
  let C' := append C qidx
  have hΩ := canonicalActualProjectedMap_injective K p₀ layers hne
  have hi := (D).actualMiddleMultiplication_injective hc hΩ
  have hQ : Function.Injective (representedQuadric D) := (D).actualNormalPolynomialMap_injective hc hΩ
  let E := residualCoordinatesEquiv D e r C h hQ
  let R := traceEquationEquiv e C k extra htrace
  let g := flagProduct D e r C h
  let l := selectedLayerEmbedding layers hne
  have hprobe := fixedFirstLayerConstraintProbe_injective D l hc
    (restrict_canonical_parameters (K := K) p₀ layers hne) (fun i _ => gamma_t_firstLayer_ne K p₀ layers hne i)
  have hzero : ∀ x : ConeMiddleFamily.NativeSource C' 2, C'.middleMultiplication 2 x = 0 → x = 0 := by
    intro x hx
    let a := E.symm (fun i => residualInclusion C qidx 2 (x.1 i))
    let b := R.symm x.2
    let v := (-1 : K) • b.val
    have hRb : R b = x.2 := R.apply_symm_apply x.2
    have ha (i : Fin (2 + m)) :
        (representedToResidual D e r C h (a i)) = residualInclusion C qidx 2 (x.1 i) := by
      exact congrFun (E.apply_symm_apply (fun i => residualInclusion C qidx 2 (x.1 i))) i
    have hfirst (i : Fin (2 + m)) : (a i).1 0 = 0 := by
      rw [← eval_representedQuadric_es e D, ← representedToResidual_val D e r C h, ha,
        pureNormalPoint, ← append_point_last C qidx e]
      exact (C'.mem_conePiece _).mp (x.1 i).property.1 (Fin.last p)
    have hxold := middleMultiplication_covariance C qidx 2 x
    rw [hx, map_zero, middleSourceInclusion_apply] at hxold
    have hm : C.residualMultiplication 2 (E a) + g b.val = 0 := by
      rw [E.apply_symm_apply]
      have he := LinearMap.congr_fun (middleMultiplication_comp_traceEquationEquiv e C k extra htrace g
        (fun _ => rfl)) (fun i => residualInclusion C qidx 2 (x.1 i), b)
      change C.middleMultiplication 2 (fun i => residualInclusion C qidx 2 (x.1 i), R b) = _ at he
      rw [hRb] at he
      exact he.symm.trans hxold.symm
    have hp : residualProduct D e r C h a = g v := by
      rw [residualProduct_eq D e r C h hQ]
      change C.residualMultiplication 2 (E a) = g ((-1 : K) • b.val)
      rw [map_smul]
      calc
        _ = C.residualMultiplication 2 (E a) + (1 + (-1 : K)) • g b.val := by simp
        _ = (C.residualMultiplication 2 (E a) + g b.val) + (-1 : K) • g b.val := by
          rw [add_smul, one_smul, add_assoc]
        _ = _ := by rw [hm, zero_add]
    have hprod := congrArg (fun y : C.residualPiece 3 => y.val.val) hp
    rw [residualProduct_val, flagProduct_val] at hprod
    have hprod' := (flatten e).injective hprod
    have hextra (t : FirstLayerProbeLabel p₀) :
        (eval (extra t) v.val.1.val, eval (extra t) v.val.2.val) = 0 := by
      have hbval : ev b.val = 0 := LinearMap.mem_ker.mp b.property
      rw [← extraPairEvaluation_apply]
      change ev ((-1 : K) • b.val) t = 0
      rw [map_smul, hbval, smul_zero, Pi.zero_apply]
    have hcorePoint : embeddedCoreTProbe D l = extra (.inl ()) :=
      extendPoint_coreProbePoint p₀ layers hne 0
    have hb : v = 0 := truncatedProduct_eq_zero D hc l hprobe
      (a (normalIndex (m := m) false)) (a (normalIndex (m := m) true)) (fun j => a (traceIndex e j))
      v (hfirst _) (fun _ => hfirst _) hprod'
      (by rw [hcorePoint]; exact hextra (.inl ())) (fun p => hextra (.inr p))
    have hb0 : b = 0 := by
      apply Subtype.ext
      change b.val = 0
      calc
        b.val = (-1 : K) • v := by dsimp only [v]; simp
        _ = 0 := by rw [hb, smul_zero]
    have ha0 : a = 0 := residualProduct_injective D e r C h hi (by simp only [hp, hb, map_zero])
    apply Prod.ext
    · funext i
      apply residualInclusion_injective C qidx 2
      rw [← ha i, ha0]
      simp
    · exact hRb.symm.trans ((congrArg R hb0).trans (R.map_zero))
  let : AddCommGroup ((Fin (2 + m) → C'.residualPiece 2) × (Fin 2 → C'.tracePiece 2)) :=
    Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (C'.residualPiece (2 + 1)) := Module.addCommMonoidToAddCommGroup K
  exact (LinearMap.ker_eq_bot (f := C'.middleMultiplication 2)).mp (LinearMap.ker_eq_bot'.mpr hzero)


end Canonical
end IdealGeneration.QuadraticTruncatedEndpoint
