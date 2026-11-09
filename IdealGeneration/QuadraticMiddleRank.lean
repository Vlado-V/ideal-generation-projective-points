module

public import IdealGeneration.QuadraticConeResidual
public import IdealGeneration.QuadraticMiddleInjectivity
public import IdealGeneration.QuadraticAugmentedEvaluation
public import IdealGeneration.QuadraticJointProbeEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Residual multiplication and evaluation on its genuine normal-linear product coefficients. -/

noncomputable section
namespace IdealGeneration.QuadraticMiddleRank
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticVariableTransport
open QuadraticConeResidual QuadraticAugmentedEvaluation QuadraticCoreRestriction

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable {m p q : ℕ} (D : QuadraticLiftParameters K P J)
variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q) (h : Compatible D e r C)

local notation "T" => ((P × Bool) ⊕ J)
local notation "F" => quadraticFlagVanishing (K := K) (P := P) (J := J)
local notation "B" => (Submodule.prod F F)
local notation "L" => ResidualCoordinates (K := K) (P := P)
local notation "Nμ" => QuadraticElimination.middleMultiplication D.firstLift D.secondLift
  (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
local notation "W" => quadraticMiddleSpace D.firstLift D.secondLift D.slope
  D.firstCorrection D.secondCorrection

local instance residualCubicGroup : AddCommGroup (C.residualPiece 3) :=
  Module.addCommMonoidToAddCommGroup K

local instance flagPairGroup : AddCommGroup B := Module.addCommMonoidToAddCommGroup K

/-- Residual multiplication on the explicit coordinate coefficients. -/
def residualProduct : (Fin (2 + m) → L) →ₗ[K] C.residualPiece 3 :=
  (C.residualMultiplication 2).comp (LinearMap.pi fun i =>
    (representedToResidual D e r C h).comp (LinearMap.proj i))

theorem residualProduct_val (x : Fin (2 + m) → L) :
    (residualProduct D e r C h x).val.val = flatten e (Nμ (splitCoefficients e x)) := by
  rw [flatten_middleMultiplication]
  rfl

omit [Field K] [Fintype P] [Fintype J] in
/-- Every grouped tuple of coefficients comes from one ambient tuple. -/
theorem splitCoefficients_bijective :
    Function.Bijective (splitCoefficients (K := K) (H := P × Bool → K) e) := by
  constructor
  · intro x y he
    funext i
    refine Fin.addCases (fun b => ?_) (fun j => ?_) i
    · obtain ⟨b, rfl⟩ := finTwoEquiv.symm.surjective b
      cases b
      · exact congrArg (fun d => d.1.1) he
      · exact congrArg (fun d => d.1.2) he
    · obtain ⟨j, rfl⟩ := e.surjective j
      exact congrFun (congrArg Prod.snd he) j
  · rintro ⟨⟨a,b⟩,z⟩
    refine ⟨Fin.addCases (fun i => if finTwoEquiv i then b else a) (z ∘ e.symm), ?_⟩
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_) <;>
      simp [splitCoefficients, normalIndex, traceIndex]

/-- The actual residual multiplication is faithful if the nested product is. -/
theorem residualProduct_injective (hi : Function.Injective Nμ) :
    Function.Injective (residualProduct D e r C h) := by
  intro x y he
  apply (splitCoefficients_bijective (K := K) (P := P) e).1
  apply hi
  apply (flatten e).injective
  simpa only [residualProduct_val] using congrArg (fun z => z.val.val) he

omit [Fintype P] [Fintype J] in
/-- Every cone trace point belongs to the flag. -/
theorem exists_flagPoint_coneTracePoint (z : ConeIndex P J) :
    ∃ i : FlagIndex P J, flagPoint i = D.coneTracePoint z := by
  classical
  rcases z with i | ⟨j,b⟩
  · refine ⟨.base i, ?_⟩
    funext x
    cases x <;> simp [flagPoint, QuadraticLiftParameters.coneTracePoint,
      traceBasePoint, coordinatePoint]
  · cases b
    · refine ⟨.layer j, ?_⟩
      funext x
      cases x <;> simp [flagPoint, QuadraticLiftParameters.coneTracePoint, layerPoint, coordinatePoint]
    · refine ⟨.layerPair D.distinguishedPair j, ?_⟩
      funext x
      cases x <;> simp [flagPoint, QuadraticLiftParameters.coneTracePoint, pairedLayerPoint,
        pairPoint, coordinatePoint]

/-- Lift a pair of actual flag equations by the two normal coordinates. -/
def flagProduct : B →ₗ[K] C.residualPiece 3 where
  toFun b := ⟨⟨flatten e (normalPairMap (quadraticPairInclusion b.val)),
    flattenedPair_homogeneous e _ b.val.1.property b.val.2.property⟩,
    ⟨(C.mem_conePiece _).mpr (fun i => by
      obtain ⟨z, rfl⟩ := r.surjective i
      rw [eval_flatten_at_cone D e r C h, D.conePointEval_normalPairMap]
      obtain ⟨j, hj⟩ := exists_flagPoint_coneTracePoint D z
      rw [← hj]
      have h₁ : eval (flagPoint j) b.val.1.val = 0 := b.property.1 j
      have h₂ : eval (flagPoint j) b.val.2.val = 0 := b.property.2 j
      change D.coneNormalPoint z false * eval (flagPoint j) b.val.1.val +
        D.coneNormalPoint z true * eval (flagPoint j) b.val.2.val = 0
      rw [h₁, h₂, mul_zero, mul_zero, add_zero]),
      Subtype.ext (flattenedPair_restrict e _)⟩⟩
  map_add' b c := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten e).toAlgHom.toLinearMap.comp
      (normalPairMap.comp (quadraticPairInclusion.comp (Submodule.subtype B)))).map_add b c
  map_smul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten e).toAlgHom.toLinearMap.comp
      (normalPairMap.comp (quadraticPairInclusion.comp (Submodule.subtype B)))).map_smul a b

omit [Fintype P] [Fintype J] in
@[simp] theorem flagProduct_val (b : B) :
    (flagProduct D e r C h b).val.val = flatten e (normalPairMap (quadraticPairInclusion b.val)) := rfl

omit [Fintype P] [Fintype J] in
theorem flagProduct_injective : Function.Injective (flagProduct D e r C h) := by
  intro b c he
  apply Subtype.ext
  apply quadraticPairInclusion_injective
  apply normalLinearPair_injective
  apply (flatten e).injective
  exact congrArg (fun z => z.val.val) he

/-- The actual product condition recovers the normal-linear multiplication space. -/
theorem mem_productCoefficients_iff (b : B) :
    b ∈ productCoefficients (residualProduct D e r C h) (flagProduct D e r C h) ↔
      b.val ∈ W := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨splitCoefficients e x, (flatten e).injective ?_⟩
    rw [← residualProduct_val D e r C h, hx, flagProduct_val]
  · rintro ⟨y,hy⟩
    obtain ⟨x,rfl⟩ := (splitCoefficients_bijective (K := K) (P := P) e).2 y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [residualProduct_val, hy, flagProduct_val]

local notation "f" => residualProduct D e r C h
local notation "g" => flagProduct D e r C h
local notation "Z" => productCoefficients f g

/-- The coefficient-space intersection is the actual projected elimination image. -/
def productCoefficientsEquiv (hc : Function.Injective D.slope) :
    Z ≃ₗ[K] D.projectedPairSpace hc := by
  have hw : W ⊓ B = D.projectedPairSpace hc :=
    quadraticMiddleSpace_inf_flag D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
      D.normal₀ D.normal₁ hc _ _ D.first_normal_equation D.second_normal_equation D.firstLift
      D.secondLift D.firstLift_homogeneous D.secondLift_homogeneous D.actualNormalLiftVanishing
  let map := (Submodule.subtype B).comp (Submodule.subtype Z)
  refine LinearEquiv.ofBijective (map.codRestrict _ fun b => by
    rw [← hw]
    exact ⟨(mem_productCoefficients_iff D e r C h b.val).1 b.property, b.val.property⟩) ?_
  constructor
  · intro b c he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : D.projectedPairSpace hc => x.val) he
  · intro w
    have hw' : w.val ∈ W ⊓ B := by rw [hw]; exact w.property
    refine ⟨⟨⟨w.val,hw'.2⟩, (mem_productCoefficients_iff D e r C h _).2 hw'.1⟩, ?_⟩
    exact Subtype.ext rfl

@[simp] theorem productCoefficientsEquiv_val (hc : Function.Injective D.slope) (b : Z) :
    (productCoefficientsEquiv D e r C h hc b).val = b.val.val := rfl

/-- Because lifting the two normal coefficients is injective, the product
coefficient subspace maps isomorphically onto the intersection of the two images. -/
def productCoefficientsImageEquiv : Z ≃ₗ[K] ↥((LinearMap.range f) ⊓ (LinearMap.range g)) := by
  let k := LinearMap.comp g (Submodule.subtype Z)
  refine LinearEquiv.ofBijective (k.codRestrict (LinearMap.range f ⊓ LinearMap.range g) fun z => by
    change g z.val ∈ LinearMap.range f ⊓ LinearMap.range g
    exact ⟨z.property, ⟨z.val, rfl⟩⟩) ?_
  constructor
  · intro a b he
    exact Subtype.ext (flagProduct_injective D e r C h (congrArg Subtype.val he))
  · intro w
    obtain ⟨v,hv⟩ := w.property.2
    have hv' : v ∈ Z := by
      change g v ∈ LinearMap.range f
      rw [hv]
      exact w.property.1
    exact ⟨⟨v,hv'⟩,Subtype.ext hv⟩

/-- The two residual product images span all actual residual cubics at the
paper's expected dimension. -/
theorem residualProduct_sup_flagProduct (hc : Function.Injective D.slope)
    (hi : Function.Injective Nμ)
    (hd : finrank K (D.projectedPairSpace hc) = 2 * Fintype.card (P × Bool) + 2)
    (hs : ∀ i, C.point i (normalIndex (m := m) false) ≠ 0) :
    (LinearMap.range f) ⊔ (LinearMap.range g) = ⊤ := by
  let a := Fintype.card (P × Bool)
  let b := Fintype.card J
  have hm : m = a + b := trace_cardinality e
  have hp : p = a + 2 * b := cone_cardinality r
  have ha : Even a := ⟨Fintype.card P, by simp [a, Fintype.card_prod, Nat.mul_two]⟩
  have hf : finrank K (LinearMap.range f) = (2 + m) * (a + 3) := by
    rw [LinearMap.finrank_range_of_inj (residualProduct_injective D e r C h hi)]
    simp [a, Module.finrank_prod, Module.finrank_pi_fintype, Nat.add_comm]
  have hFree : Module.Free K F := by
    with_unfolding_all exact Module.Free.of_divisionRing K F
  have hg : finrank K (LinearMap.range g) = 2 * (N m 2 - flagCount a b) := by
    rw [LinearMap.finrank_range_of_inj (flagProduct_injective D e r C h),
      (Submodule.prodEquiv F F).finrank_eq, Module.finrank_prod,
      finrank_quadraticFlagVanishing D.slope D.distinguishedPair hc, hm]
    change (N (a + b) 2 - flagCount a b) + (N (a + b) 2 - flagCount a b) = _
    omega
  have hz : finrank K ↥((LinearMap.range f) ⊓ (LinearMap.range g)) = 2 * a + 2 :=
    (productCoefficientsImageEquiv D e r C h).finrank_eq.symm.trans
      ((productCoefficientsEquiv D e r C h hc).finrank_eq.trans hd)
  have hsups := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  rw [hf,hg,hz] at hsups
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_residualCubics D e r C h hs]
  have hflag : 2 * (N m 2 - flagCount a b) = m * (m + 1) - (a * m + p) := by
    have hx := flagCount_le_quadratic_count a b ha
    rw [← hm] at hx
    have hy := two_mul_flagCount a b ha
    rw [← hm, ← hp] at hy
    have hN := two_mul_quadratic_count m
    omega
  have hpc : p ≤ (m + 2) ^ 2 := by nlinarith [Nat.zero_le (m * m)]
  have hfN : a * m + p ≤ m * (m + 1) := by
    have hx := flagCount_le_quadratic_count a b ha
    rw [← hm] at hx
    have hy := two_mul_flagCount a b ha
    rw [← hm, ← hp] at hy
    have hN := two_mul_quadratic_count m
    omega
  rw [hflag] at hsups
  have hnat := Nat.sub_add_cancel hfN
  have hnat' := Nat.sub_add_cancel hpc
  nlinarith

end IdealGeneration.QuadraticMiddleRank
