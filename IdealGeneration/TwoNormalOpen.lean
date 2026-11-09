module

public import IdealGeneration.TwoNormalTrace
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Polynomial opens for two-normal ideal restrictions

Restriction and multiplication on a varying point-ideal kernel are detected
by maps whose source spaces stay fixed. Their matrices are polynomial in the
point coordinates, so an injective specialization persists on a principal open.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- Evaluation together with restriction detects forms in the point ideal
whose trace is zero. -/
def restrictionDetection {p : ℕ} (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    Forms K (m + 2) d →ₗ[K] ((Fin p → K) × Forms K m d) :=
  (pointEvaluation K x d).prod (restrictTraceForm K m d)

/-- Evaluate every coefficient of a tangential tuple at every point. -/
def tupleEvaluation {p : ℕ} (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    (Fin m → Forms K (m + 2) d) →ₗ[K] (Fin m × Fin p → K) :=
  LinearMap.pi fun ij =>
    (evaluationLinear K (m + 2) d (chartPoint K x ij.2)).comp (LinearMap.proj ij.1)

/-- The common-trace tangential product on the fixed ambient coefficient space. -/
def ambientTraceProduct (d : ℕ) :
    (Fin m → Forms K (m + 2) d) →ₗ[K] Forms K m (d + 1) :=
  (restrictTraceForm K m (d + 1)).comp (tangentProduct K m d)

/-- Detect relations in the restricted product of a varying point ideal. -/
def productDetection {p : ℕ} (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    (Fin m → Forms K (m + 2) d) →ₗ[K]
      ((Fin m × Fin p → K) × Forms K m (d + 1)) :=
  (tupleEvaluation K m x d).prod (ambientTraceProduct K m d)

@[simp] theorem tupleEvaluation_apply {p d : ℕ} (x : PointCoordinates K (m + 1) p)
    (a : Fin m → Forms K (m + 2) d) (i : Fin m) (j : Fin p) :
    tupleEvaluation K m x d a (i, j) = pointEvaluation K x d (a i) j := rfl

@[simp] theorem ambientTraceProduct_on_ideal {p d : ℕ}
    (x : PointCoordinates K (m + 1) p) (a : Fin m → pointDegreePiece K x d) :
    ambientTraceProduct K m d (fun i => (a i).val) =
      traceProduct K m d (pointDegreePiece K x d) a := rfl

/-- Fixed-source restriction detection is equivalent to restriction injectivity
on the actual point ideal. -/
theorem restrictionDetection_injective_iff {p d : ℕ} (x : PointCoordinates K (m + 1) p) :
    Function.Injective (restrictionDetection K m x d) ↔
      Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype) := by
  constructor
  · intro h f g hfg
    apply Subtype.ext
    apply h
    apply Prod.ext
    · exact f.property.trans g.property.symm
    · exact hfg
  · intro h f g hfg
    have he := congrArg Prod.fst hfg
    have ht := congrArg Prod.snd hfg
    let a : pointDegreePiece K x d := ⟨f - g, by
      change pointEvaluation K x d (f - g) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr he⟩
    have ha : ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype) a = 0 := by
      change restrictTraceForm K m d (f - g) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr ht
    have ha0 : a = 0 := h (by simpa using ha)
    exact sub_eq_zero.mp (congrArg Subtype.val ha0)

/-- Fixed-source product detection is equivalent to product injectivity on
the actual varying point ideal. -/
theorem productDetection_injective_iff {p d : ℕ} (x : PointCoordinates K (m + 1) p) :
    Function.Injective (productDetection K m x d) ↔
      Function.Injective (traceProduct K m d (pointDegreePiece K x d)) := by
  constructor
  · intro h a b hab
    have he : tupleEvaluation K m x d (fun i => (a i).val) =
        tupleEvaluation K m x d (fun i => (b i).val) := by
      funext ij
      exact (congrFun (a ij.1).property ij.2).trans
        (congrFun (b ij.1).property ij.2).symm
    have hfull := h (show productDetection K m x d (fun i => (a i).val) =
        productDetection K m x d (fun i => (b i).val) from Prod.ext he hab)
    funext i
    exact Subtype.ext (congrFun hfull i)
  · intro h a b hab
    have he := congrArg Prod.fst hab
    have ht := congrArg Prod.snd hab
    let g : Fin m → pointDegreePiece K x d := fun i => ⟨a i - b i, by
      change pointEvaluation K x d (a i - b i) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      funext j
      exact congrFun he (i, j)⟩
    have hg : traceProduct K m d (pointDegreePiece K x d) g = 0 := by
      change ambientTraceProduct K m d (a - b) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr ht
    have hg0 : g = 0 := h (by simpa using hg)
    funext i
    exact sub_eq_zero.mp (congrArg Subtype.val (congrFun hg0 i))

/-- Restriction detection has polynomial dependence on the point coordinates. -/
theorem restrictionDetection_isPolynomialFamily (p d : ℕ) :
    IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p =>
      restrictionDetection K m x d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have he : IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p =>
      pointEvaluation K x d f) :=
    (pointEvaluation_isPolynomialFamily (K := K) (m + 1) p d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin p → K) f)
  exact he.prod_mk (isPolynomialFamily_const (restrictTraceForm K m d f))

/-- Tuple evaluation is polynomial in its point parameters. -/
theorem tupleEvaluation_isPolynomialFamily (p d : ℕ) :
    IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p => tupleEvaluation K m x d) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro ij
  change IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p =>
    pointEvaluation K x d (f ij.1) ij.2)
  simpa only [eval_chartEvaluationPolynomial] using
    isPolynomialFamily_eval (chartEvaluationPolynomial (f ij.1) ij.2)

/-- Product detection has polynomial dependence on the point coordinates. -/
theorem productDetection_isPolynomialFamily (p d : ℕ) :
    IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p => productDetection K m x d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have he : IsPolynomialFamily (fun x : PointCoordinates K (m + 1) p =>
      tupleEvaluation K m x d f) :=
    (tupleEvaluation_isPolynomialFamily K m p d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin m × Fin p → K) f)
  exact he.prod_mk (isPolynomialFamily_const (ambientTraceProduct K m d f))

/-- An injective trace restriction at one point configuration persists on a
nonempty principal open in the full configuration space. -/
theorem generic_restriction_injective_of_witness {p d : ℕ}
    (x₀ : PointCoordinates K (m + 1) p)
    (h₀ : Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x₀ d).subtype)) :
    ∃ P : MvPolynomial (Fin p × Fin (m + 1)) K,
      eval x₀ P ≠ 0 ∧ ∀ x, eval x P ≠ 0 →
        Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype) := by
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open
    (fun x : PointCoordinates K (m + 1) p => restrictionDetection K m x d)
    (restrictionDetection_isPolynomialFamily K m p d) x₀
    ((restrictionDetection_injective_iff K m x₀).mpr h₀)
  exact ⟨P, hP, fun x hx => (restrictionDetection_injective_iff K m x).mp (hgood x hx)⟩

/-- Injective multiplication of the restricted ideal at one configuration
persists on a principal open although the ideal kernel varies. -/
theorem generic_traceProduct_injective_of_witness {p d : ℕ}
    (x₀ : PointCoordinates K (m + 1) p)
    (h₀ : Function.Injective (traceProduct K m d (pointDegreePiece K x₀ d))) :
    ∃ P : MvPolynomial (Fin p × Fin (m + 1)) K,
      eval x₀ P ≠ 0 ∧ ∀ x, eval x P ≠ 0 →
        Function.Injective (traceProduct K m d (pointDegreePiece K x d)) := by
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open
    (fun x : PointCoordinates K (m + 1) p => productDetection K m x d)
    (productDetection_isPolynomialFamily K m p d) x₀
    ((productDetection_injective_iff K m x₀).mpr h₀)
  exact ⟨P, hP, fun x hx => (productDetection_injective_iff K m x).mp (hgood x hx)⟩

/-- Both varying-kernel injections hold on one explicit nonempty open. -/
theorem generic_trace_injections_of_witness {p d : ℕ}
    (x₀ : PointCoordinates K (m + 1) p)
    (hR : Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x₀ d).subtype))
    (hP : Function.Injective (traceProduct K m d (pointDegreePiece K x₀ d))) :
    ∃ P : MvPolynomial (Fin p × Fin (m + 1)) K,
      eval x₀ P ≠ 0 ∧ ∀ x, eval x P ≠ 0 →
        Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype) ∧
        Function.Injective (traceProduct K m d (pointDegreePiece K x d)) := by
  obtain ⟨P, hP₀, hPgood⟩ := generic_restriction_injective_of_witness K m x₀ hR
  obtain ⟨Q, hQ₀, hQgood⟩ := generic_traceProduct_injective_of_witness K m x₀ hP
  refine ⟨P * Q, by simpa using mul_ne_zero hP₀ hQ₀, ?_⟩
  intro x hx
  have hparts : eval x P ≠ 0 ∧ eval x Q ≠ 0 := by simpa using hx
  exact ⟨hPgood x hparts.1, hQgood x hparts.2⟩

end IdealGeneration.TwoNormalTrace
