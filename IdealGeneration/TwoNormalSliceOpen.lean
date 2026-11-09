module

public import IdealGeneration.TwoNormalAttachedInterpolation
public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.TwoGroupInterpolation
public import IdealGeneration.DeformationMatrix
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial detection of the slice-code rank

The point ideal varies with the slice points. Evaluating all coefficient
forms first, then evaluating their fixed trace product, gives a single map
on a fixed coefficient space. Its injectivity detects unisolvence on the
actual slice product space.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b q d : ℕ}

abbrev SliceCoefficients (K : Type*) [Field K] (n d : ℕ) :=
  Fin (n + 1) → Forms K (n + 2) d

/-- Evaluate all coefficients at the slice points. -/
def sliceCoefficientEvaluation (a : PointCoordinates K (n + 1) b) (d : ℕ) :
    SliceCoefficients K n d →ₗ[K] (Fin (n + 1) × Fin b → K) :=
  LinearMap.pi fun ij =>
    (evaluationLinear K (n + 2) d (chartPoint K a ij.2)).comp (LinearMap.proj ij.1)

/-- The scalar product followed by the trace restriction, on fixed forms. -/
def fixedSliceTraceProduct (n d : ℕ) : SliceCoefficients K n d →ₗ[K] Forms K (n + 1) (d + 1) :=
  (restrictForm K (n + 1) (d + 1)).comp (HyperplaneEuler.tangentProduct K (n + 1) d)

/-- On ideal coefficients, the fixed map is the actual slice trace product. -/
theorem fixedSliceTraceProduct_on_ideal (a : PointCoordinates K (n + 1) b)
    (f : Fin (n + 1) → pointDegreePiece K a d) :
    fixedSliceTraceProduct n d (fun i => (f i).val) =
      tangentPointProductForm a d (fun i => pointPolynomialPieceEquiv a d (f i)) := by
  apply Subtype.ext
  change hyperplaneRestrict K (n + 1) (∑ i, X i.succ * (f i).val.val) =
    ∑ i, X i * hyperplaneRestrict K (n + 1) (f i).val.val
  simp

/-- The fixed-source stack detects a zero trace product on ideal coefficients. -/
def sliceCodeDetection (a : PointCoordinates K (n + 1) b)
    (z : PointCoordinates K n q) (d : ℕ) : SliceCoefficients K n d →ₗ[K]
      ((Fin (n + 1) × Fin b → K) × (Fin q → K)) :=
  (sliceCoefficientEvaluation a d).prod
    ((pointEvaluation K z (d + 1)).comp (fixedSliceTraceProduct n d))

local instance sliceCoefficientsGroup : AddCommGroup (SliceCoefficients K n d) :=
  Module.addCommMonoidToAddCommGroup K

/-- An injective trace product and a unisolvent evaluation give an injective detector. -/
theorem sliceCodeDetection_injective (a : PointCoordinates K (n + 1) b)
    (z : PointCoordinates K n q)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (heval : Function.Injective (subspaceEvaluation (tangentPointProductForm a d).range z)) :
    Function.Injective (sliceCodeDetection a z d) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hcoeff : sliceCoefficientEvaluation a d f = 0 := congrArg Prod.fst hf
  have htrace : pointEvaluation K z (d + 1) (fixedSliceTraceProduct n d f) = 0 :=
    congrArg Prod.snd hf
  let g : Fin (n + 1) → pointDegreePiece K a d := fun i => ⟨f i, by
    rw [mem_pointDegreePiece]
    intro j
    exact congrFun hcoeff (i, j)⟩
  let w : Fin (n + 1) → pointPolynomialPiece a d := fun i => pointPolynomialPieceEquiv a d (g i)
  have hprod : tangentPointProductForm a d w = fixedSliceTraceProduct n d f :=
    (fixedSliceTraceProduct_on_ideal a g).symm
  let u : (tangentPointProductForm a d).range := ⟨tangentPointProductForm a d w, ⟨w, rfl⟩⟩
  have hu : subspaceEvaluation (tangentPointProductForm a d).range z u = 0 := by
    change pointEvaluation K z (d + 1) (tangentPointProductForm a d w) = 0
    rwa [hprod]
  have hu0 : u = 0 := heval (hu.trans (map_zero _).symm)
  have hzero : tangentPointProductForm a d w = 0 :=
    congrArg (fun v : (tangentPointProductForm a d).range => v.val) hu0
  have hw : w = 0 := tangentPointProductForm_injective a ha hmul
    (hzero.trans (map_zero _).symm)
  funext i
  apply Subtype.ext
  exact congrArg (fun g : Fin (n + 1) → pointPolynomialPiece a d => (g i).val) hw

/-- Injectivity of the detector implies unisolvence on the actual product space. -/
theorem sliceCodeEvaluation_injective_of_detection (a : PointCoordinates K (n + 1) b)
    (z : PointCoordinates K n q)
    (h : Function.Injective (sliceCodeDetection a z d)) :
    Function.Injective (subspaceEvaluation (tangentPointProductForm a d).range z) := by
  intro u v huv
  obtain ⟨w, hw⟩ := u.property
  obtain ⟨w', hw'⟩ := v.property
  let g : Fin (n + 1) → pointDegreePiece K a d := fun i => (pointPolynomialPieceEquiv a d).symm (w i)
  let g' : Fin (n + 1) → pointDegreePiece K a d := fun i => (pointPolynomialPieceEquiv a d).symm (w' i)
  have hprod : fixedSliceTraceProduct n d (fun i => (g i).val) = u.val := by
    rw [fixedSliceTraceProduct_on_ideal]
    simpa [g] using hw
  have hprod' : fixedSliceTraceProduct n d (fun i => (g' i).val) = v.val := by
    rw [fixedSliceTraceProduct_on_ideal]
    simpa [g'] using hw'
  have heq : (fun i => (g i).val) = fun i => (g' i).val := by
    apply h
    apply Prod.ext
    · funext ij
      exact ((mem_pointDegreePiece a (g ij.1).val).mp (g ij.1).property ij.2).trans
        ((mem_pointDegreePiece a (g' ij.1).val).mp (g' ij.1).property ij.2).symm
    · change pointEvaluation K z (d + 1) (fixedSliceTraceProduct n d (fun i => (g i).val)) =
        pointEvaluation K z (d + 1) (fixedSliceTraceProduct n d (fun i => (g' i).val))
      rw [hprod, hprod']
      exact huv
  apply Subtype.ext
  rw [← hprod, ← hprod', heq]

/-- The tuple evaluations are polynomial in the slice-point coordinates. -/
theorem sliceCoefficientEvaluation_polynomial (n b d : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K (n + 1) b => sliceCoefficientEvaluation a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro ij
  change IsPolynomialFamily (fun a : PointCoordinates K (n + 1) b => pointEvaluation K a d (f ij.1) ij.2)
  simpa only [eval_chartEvaluationPolynomial] using
    isPolynomialFamily_eval (chartEvaluationPolynomial (f ij.1) ij.2)

/-- A witnessed code condition is a principal-open condition in any common
parameter space that selects the slice and trace point coordinates. -/
theorem generic_sliceCode_open_of_witness {ι : Type*}
    (eA : (Fin b × Fin (n + 1)) → ι) (eZ : (Fin q × Fin n) → ι)
    (c₀ : ι → K)
    (hA : ∀ i, chartPoint K (c₀ ∘ eA) i (0 : Fin (n + 2)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication (c₀ ∘ eA) d))
    (heval : Function.Injective (subspaceEvaluation
      (tangentPointProductForm (c₀ ∘ eA) d).range (c₀ ∘ eZ))) :
    ∃ P : MvPolynomial ι K, eval c₀ P ≠ 0 ∧ ∀ c, eval c P ≠ 0 →
      Function.Injective (subspaceEvaluation (tangentPointProductForm (c ∘ eA) d).range (c ∘ eZ)) := by
  let F := fun c : ι → K => sliceCodeDetection (c ∘ eA) (c ∘ eZ) d
  have hpoly : IsPolynomialFamily F := by
    apply isPolynomialFamily_linearMap
    intro f
    have h₁ := polynomialFamily_reindex
      ((sliceCoefficientEvaluation_polynomial (K := K) n b d).linear_comp
        (LinearMap.applyₗ f)) eA
    have h₂ := polynomialFamily_reindex
      ((pointEvaluation_isPolynomialFamily (K := K) n q (d + 1)).linear_comp
        (LinearMap.applyₗ (fixedSliceTraceProduct n d f))) eZ
    exact h₁.prod_mk h₂
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open F hpoly c₀
    (sliceCodeDetection_injective (c₀ ∘ eA) (c₀ ∘ eZ) hA hmul heval)
  exact ⟨P, hP, fun c hc =>
    sliceCodeEvaluation_injective_of_detection (c ∘ eA) (c ∘ eZ) (hgood c hc)⟩

end IdealGeneration.TwoNormalIntegral
