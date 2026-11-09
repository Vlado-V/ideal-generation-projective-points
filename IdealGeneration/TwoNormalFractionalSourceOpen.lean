module

public import IdealGeneration.TwoNormalFractionalSource
public import IdealGeneration.TwoGroupInterpolation
public import IdealGeneration.ConstrainedRankOpen
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Rank opens for the enlarged fractional slice products

The coefficient ideal varies with the attached off-slice points. Stacking
evaluation of each coefficient with evaluation of the fixed slice product
makes the desired injection an ordinary rank-open condition.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoGroupInterpolation ConstrainedRankOpen
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d b q : ℕ}

/-- General slice points detect every form in an injective enlarged product. -/
theorem exists_enlargedProductEvaluation_injective [Infinite K]
    (G : Submodule K (Forms K (m + 2) d))
    (Q : ((Fin m → G) × G) →ₗ[K] Forms K (m + 1) (d + 1))
    (hQ : Function.Injective Q) (hb : (m + 1) * finrank K G ≤ b) :
    ∃ a : PointCoordinates K m b, Function.Injective ((pointEvaluation K a (d + 1)).comp Q) := by
  let : AddCommGroup G := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K G := Module.Free.of_divisionRing K G
  have hd : finrank K Q.range ≤ b := by
    rw [LinearMap.finrank_range_of_inj hQ, Module.finrank_prod, Module.finrank_pi_fintype]
    simpa [Nat.add_mul] using hb
  obtain ⟨P, ⟨a, ha⟩, hp⟩ := generic_subspaceEvaluation_injective Q.range b hd
  refine ⟨a, ?_⟩
  intro u v huv
  apply hQ
  exact congrArg Subtype.val (hp a ha (show
    subspaceEvaluation Q.range a (Q.rangeRestrict u) =
      subspaceEvaluation Q.range a (Q.rangeRestrict v) from huv))

/-- The unconstrained ambient coefficients of an enlarged slice product. -/
abbrev EnlargedCoefficients (K : Type*) [Field K] (m d : ℕ) :=
  (Fin m → Forms K (m + 2) d) × Forms K (m + 2) d

/-- Evaluate each unconstrained coefficient at all attached off-slice points. -/
def enlargedCoefficientEvaluation (x : PointCoordinates K (m + 1) q) (d : ℕ) :
    EnlargedCoefficients K m d →ₗ[K] ((Fin m × Fin q → K) × (Fin q → K)) :=
  (LinearMap.pi fun ij => (evaluationLinear K (m + 2) d (chartPoint K x ij.2)).comp
    (LinearMap.proj ij.1)).prodMap (pointEvaluation K x d)

/-- The slice product on fixed ambient forms, before imposing any ideal conditions. -/
def fixedEnlargedProduct
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1)) :
    EnlargedCoefficients K m d →ₗ[K] Forms K (m + 1) (d + 1) :=
  R.comp ((TwoNormalTrace.tangentProduct K m d).coprod M)

private theorem enlargedCoefficientEvaluation_polynomial :
    IsPolynomialFamily (fun x : PointCoordinates K (m + 1) q =>
      enlargedCoefficientEvaluation x d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have h₁ : IsPolynomialFamily (fun x : PointCoordinates K (m + 1) q =>
      fun ij : Fin m × Fin q => pointEvaluation K x d (f.1 ij.1) ij.2) := by
    apply DeformationMatrix.isPolynomialFamily_pi
    intro ij
    simpa only [eval_chartEvaluationPolynomial] using
      isPolynomialFamily_eval (chartEvaluationPolynomial (f.1 ij.1) ij.2)
  have h₂ := (pointEvaluation_isPolynomialFamily (K := K) (m + 1) q d).linear_comp
    (LinearMap.applyₗ f.2)
  exact h₁.prod_mk h₂

private theorem enlargedProductEvaluation_injective_iff
    (x : PointCoordinates K (m + 1) q) (a : PointCoordinates K m b)
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1)) :
    Function.Injective ((pointEvaluation K a (d + 1)).comp
      (sliceProductOf K m (pointDegreePiece K x d) R M)) ↔
    Function.Injective ((enlargedCoefficientEvaluation x d).prod
      ((pointEvaluation K a (d + 1)).comp (fixedEnlargedProduct R M))) := by
  let G := pointDegreePiece K x d
  let : AddCommGroup (EnlargedCoefficients K m d) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup ((Fin m → G) × G) := Module.addCommMonoidToAddCommGroup K
  let E := enlargedCoefficientEvaluation x d
  let F := (pointEvaluation K a (d + 1)).comp (fixedEnlargedProduct R M)
  let L := (pointEvaluation K a (d + 1)).comp (sliceProductOf K m G R M)
  constructor
  · intro hL
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hcoeff : E f = 0 := congrArg Prod.fst hf
    let w : (Fin m → G) × G :=
      (fun j => ⟨f.1 j, (mem_pointDegreePiece x (f.1 j)).mpr
        (fun i => congrFun (congrArg Prod.fst hcoeff) (j, i))⟩,
        ⟨f.2, (mem_pointDegreePiece x f.2).mpr (fun i => congrFun (congrArg Prod.snd hcoeff) i)⟩)
    have hw : L w = 0 := congrArg Prod.snd hf
    have hw0 := hL (hw.trans (map_zero L).symm)
    apply Prod.ext
    · funext j
      exact congrArg (fun v : (Fin m → G) × G => (v.1 j).val) hw0
    · exact congrArg (fun v : (Fin m → G) × G => v.2.val) hw0
  · intro hF u v huv
    let lift : ((Fin m → G) × G) → EnlargedCoefficients K m d :=
      fun w => (fun i => (w.1 i).val, w.2.val)
    have he (w : (Fin m → G) × G) : E (lift w) = 0 := by
      apply Prod.ext
      · funext ij
        exact (mem_pointDegreePiece x (w.1 ij.1).val).mp (w.1 ij.1).property ij.2
      · funext i
        exact (mem_pointDegreePiece x w.2.val).mp w.2.property i
    have hLift : lift u = lift v := hF (Prod.ext ((he u).trans (he v).symm) huv)
    apply Prod.ext
    · funext j
      exact Subtype.ext (congrFun (congrArg Prod.fst hLift) j)
    · exact Subtype.ext (congrArg Prod.snd hLift)

/-- An enlarged slice interpolation witness gives a principal open in any
common parameter space selecting its attached and slice coordinates. -/
theorem enlargedProductEvaluation_open_of_witness {ι : Type*}
    (eX : (Fin q × Fin (m + 1)) → ι) (eA : (Fin b × Fin m) → ι)
    (R : Forms K (m + 2) (d + 1) →ₗ[K] Forms K (m + 1) (d + 1))
    (M : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1))
    (c₀ : ι → K)
    (h₀ : Function.Injective ((pointEvaluation K (c₀ ∘ eA) (d + 1)).comp
      (sliceProductOf K m (pointDegreePiece K (c₀ ∘ eX) d) R M))) :
    ∃ P : MvPolynomial ι K, eval c₀ P ≠ 0 ∧
      ∀ c, eval c P ≠ 0 → Function.Injective ((pointEvaluation K (c ∘ eA) (d + 1)).comp
        (sliceProductOf K m (pointDegreePiece K (c ∘ eX) d) R M)) := by
  let : AddCommGroup (EnlargedCoefficients K m d) := Module.addCommMonoidToAddCommGroup K
  let E := fun c : ι → K => enlargedCoefficientEvaluation (c ∘ eX) d
  let F := fun c : ι → K => (pointEvaluation K (c ∘ eA) (d + 1)).comp (fixedEnlargedProduct R M)
  have hE : IsPolynomialFamily E := polynomialFamily_reindex
    (enlargedCoefficientEvaluation_polynomial (K := K) (m := m) (d := d) (q := q)) eX
  have hF : IsPolynomialFamily F := by
    apply isPolynomialFamily_linearMap
    intro w
    have hp := (pointEvaluation_isPolynomialFamily (K := K) m b (d + 1)).linear_comp
      (LinearMap.applyₗ (fixedEnlargedProduct R M w))
    exact polynomialFamily_reindex hp eA
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open
    (fun c => (E c).prod (F c)) (stack_isPolynomialFamily E F hE hF) c₀
    ((enlargedProductEvaluation_injective_iff (c₀ ∘ eX) (c₀ ∘ eA) R M).mp h₀)
  exact ⟨P, hP, fun c hc =>
    (enlargedProductEvaluation_injective_iff (c ∘ eX) (c ∘ eA) R M).mpr (hgood c hc)⟩

end IdealGeneration.TwoNormalFractional
