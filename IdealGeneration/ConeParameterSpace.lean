module

public import IdealGeneration.ConeSplitting
public import IdealGeneration.PointAvoidance
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The affine parameter space of marked cones

The support assignment is fixed. Trace coordinates, normal coordinates and
heights vary independently. Polynomial pullback along the trace projection
preserves nonzero polynomials, and independently witnessed principal opens
therefore meet in this actual parameter space.
-/

noncomputable section
namespace IdealGeneration.ConeParameterSpace
open MvPolynomial

variable {K : Type*} [Field K] {c m p q d : ℕ}

abbrev Index (c m p q : ℕ) := (Fin q × Fin m) ⊕ ((Fin p × Fin c) ⊕ Fin p)

abbrev Parameters (K : Type*) (c m p q : ℕ) := Index c m p q → K

def traceCoordinates (a : Parameters K c m p q) : Fin q × Fin m → K :=
  fun ij => a (Sum.inl ij)

def normalCoordinates (a : Parameters K c m p q) : Fin p × Fin c → K :=
  fun ij => a (Sum.inr (Sum.inl ij))

def heights (a : Parameters K c m p q) : Fin p → K :=
  fun i => a (Sum.inr (Sum.inr i))

/-- Assemble independent coordinate groups into one marked-cone parameter. -/
def assemble (t : Fin q × Fin m → K) (n : Fin p × Fin c → K) (h : Fin p → K) :
    Parameters K c m p q :=
  Sum.elim t (Sum.elim n h)

omit [Field K] in
@[simp] theorem traceCoordinates_assemble (t : Fin q × Fin m → K)
    (n : Fin p × Fin c → K) (h : Fin p → K) :
    traceCoordinates (assemble t n h) = t := rfl

omit [Field K] in
@[simp] theorem normalCoordinates_assemble (t : Fin q × Fin m → K)
    (n : Fin p × Fin c → K) (h : Fin p → K) :
    normalCoordinates (assemble t n h) = n := rfl

omit [Field K] in
@[simp] theorem heights_assemble (t : Fin q × Fin m → K)
    (n : Fin p × Fin c → K) (h : Fin p → K) :
    heights (assemble t n h) = h := rfl

/-- The trace projection is onto, with a section using unit heights. -/
theorem traceCoordinates_surjective :
    Function.Surjective (traceCoordinates (K := K) (c := c) (m := m) (p := p) (q := q)) :=
  fun t => ⟨assemble t (fun _ => 0) (fun _ => 1), rfl⟩

/-- The actual cone configuration represented by a parameter. -/
def configuration (support : Fin p → Fin q) (a : Parameters K c m p q) :
    ConeConfiguration K c m p q where
  trace i j := traceCoordinates a (i, j)
  normal i j := normalCoordinates a (i, j)
  support := support
  height := heights a

/-- Every concrete configuration occurs in the marked affine family. -/
def encode (C : ConeConfiguration K c m p q) : Parameters K c m p q :=
  assemble (fun ij => C.trace ij.1 ij.2) (fun ij => C.normal ij.1 ij.2) C.height

omit [Field K] in
@[simp] theorem configuration_encode (C : ConeConfiguration K c m p q) :
    configuration C.support (encode C) = C := by
  cases C
  rfl

def liftTracePolynomial (D : MvPolynomial (Fin q × Fin m) K) :
    MvPolynomial (Index c m p q) K :=
  rename Sum.inl D

@[simp] theorem eval_liftTracePolynomial (D : MvPolynomial (Fin q × Fin m) K)
    (a : Parameters K c m p q) :
    eval a (liftTracePolynomial (c := c) (p := p) D) = eval (traceCoordinates a) D := by
  exact eval_rename _ _ _

/-- Pullback along the surjective trace projection preserves nonzero equations. -/
theorem liftTracePolynomial_ne_zero (D : MvPolynomial (Fin q × Fin m) K) (hD : D ≠ 0) :
    liftTracePolynomial (c := c) (p := p) D ≠ 0 := by
  exact fun h => hD ((rename_injective Sum.inl Sum.inl_injective) (h.trans (map_zero _).symm))

/-- An independently witnessed cone condition meets an independently witnessed
trace condition. -/
theorem compatible_trace_open [Infinite K]
    (P : MvPolynomial (Index c m p q) K) (hP : ∃ a, eval a P ≠ 0)
    (D : MvPolynomial (Fin q × Fin m) K) (hD : ∃ t, eval t D ≠ 0) :
    ∃ a : Parameters K c m p q, eval a P ≠ 0 ∧ eval (traceCoordinates a) D ≠ 0 := by
  have hLift : ∃ a : Parameters K c m p q,
      eval a (liftTracePolynomial (c := c) (p := p) D) ≠ 0 := by
    obtain ⟨t, ht⟩ := hD
    exact ⟨assemble t (fun _ => 0) (fun _ => 1), by simpa using ht⟩
  obtain ⟨a, ha, hb⟩ := principal_opens_meet P (liftTracePolynomial D) hP hLift
  exact ⟨a, ha, by simpa using hb⟩

/-- A principal open ensuring nonzero heights and a selected nonzero normal
coordinate at every cone point. -/
def nonzeroPolynomial (j : Fin p → Fin c) : MvPolynomial (Index c m p q) K :=
  ∏ i, X (Sum.inr (Sum.inl (i, j i))) * X (Sum.inr (Sum.inr i))

@[simp] theorem eval_nonzeroPolynomial_iff (j : Fin p → Fin c)
    (a : Parameters K c m p q) :
    eval a (nonzeroPolynomial (m := m) (q := q) j) ≠ 0 ↔
      (∀ i, normalCoordinates a (i, j i) ≠ 0) ∧ (∀ i, heights a i ≠ 0) := by
  simp [nonzeroPolynomial, Finset.prod_ne_zero_iff, normalCoordinates, heights,
    forall_and]

theorem nonzeroPolynomial_nonempty (j : Fin p → Fin c) :
    ∃ a : Parameters K c m p q, eval a (nonzeroPolynomial j) ≠ 0 := by
  refine ⟨fun _ => 1, ?_⟩
  simp [nonzeroPolynomial]

/-- Nonzero cone representatives can be imposed together with independent
cone and trace principal-open conditions. -/
theorem compatible_trace_open_nonzero [Infinite K] (j : Fin p → Fin c)
    (P : MvPolynomial (Index c m p q) K) (hP : ∃ a, eval a P ≠ 0)
    (D : MvPolynomial (Fin q × Fin m) K) (hD : ∃ t, eval t D ≠ 0) :
    ∃ a : Parameters K c m p q,
      eval a P ≠ 0 ∧ eval (traceCoordinates a) D ≠ 0 ∧
      (∀ i, normalCoordinates a (i, j i) ≠ 0) ∧ (∀ i, heights a i ≠ 0) := by
  obtain ⟨b, hbP, hbN⟩ := principal_opens_meet P (nonzeroPolynomial j) hP
    (nonzeroPolynomial_nonempty j)
  have hPN : ∃ a, eval a (P * nonzeroPolynomial j) ≠ 0 :=
    ⟨b, by simpa only [map_mul] using mul_ne_zero hbP hbN⟩
  obtain ⟨a, haPN, haD⟩ := compatible_trace_open (P * nonzeroPolynomial j) hPN D hD
  have ha : eval a P ≠ 0 ∧ eval a (nonzeroPolynomial j) ≠ 0 := by simpa using haPN
  exact ⟨a, ha.1, haD, (eval_nonzeroPolynomial_iff j a).mp ha.2⟩

/-- Parameter polynomials for the coordinates of a marked cone point. -/
def pointPolynomials (support : Fin p → Fin q) (i : Fin p) :
    Fin (c + m) → MvPolynomial (Index c m p q) K :=
  Fin.addCases (fun j => X (Sum.inr (Sum.inl (i, j))))
    (fun j => X (Sum.inr (Sum.inr i)) * X (Sum.inl (support i, j)))

@[simp] theorem eval_pointPolynomials (support : Fin p → Fin q)
    (a : Parameters K c m p q) (i : Fin p) (j : Fin (c + m)) :
    eval a (pointPolynomials support i j) = (configuration support a).point i j := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
    simp [pointPolynomials, configuration, ConeConfiguration.point,
      traceCoordinates, normalCoordinates, heights]

def coneEvaluation (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    Forms K (c + m) d →ₗ[K] (Fin p → K) :=
  LinearMap.pi (fun i => evaluationLinear K (c + m) d ((configuration support a).point i))

def coneEvaluationPolynomial (support : Fin p → Fin q)
    (f : Forms K (c + m) d) (i : Fin p) : MvPolynomial (Index c m p q) K :=
  eval₂ C (pointPolynomials support i) f.val

@[simp] theorem eval_coneEvaluationPolynomial (support : Fin p → Fin q)
    (a : Parameters K c m p q) (f : Forms K (c + m) d) (i : Fin p) :
    eval a (coneEvaluationPolynomial support f i) = coneEvaluation support a d f i := by
  rw [coneEvaluationPolynomial, eval_eval₂]
  change eval₂ ((eval a).comp C) (fun j => eval a (pointPolynomials support i j)) f.val = _
  have hc : (eval a).comp C = RingHom.id K := by ext x; simp
  rw [hc]
  simp only [eval_pointPolynomials]
  rfl

/-- Evaluation on the moving cone points is a polynomial family on a fixed
space of homogeneous forms. -/
theorem coneEvaluation_isPolynomialFamily (support : Fin p → Fin q) (d : ℕ) :
    IsPolynomialFamily (fun a : Parameters K c m p q => coneEvaluation support a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro i
  simpa only [eval_coneEvaluationPolynomial] using
    isPolynomialFamily_eval (coneEvaluationPolynomial support f i)

def traceEvaluation (a : Parameters K c m p q) (d : ℕ) :
    Forms K m d →ₗ[K] (Fin q → K) :=
  LinearMap.pi (fun i => evaluationLinear K m d (fun j => traceCoordinates a (i, j)))

def traceEvaluationPolynomial (f : Forms K m d) (i : Fin q) :
    MvPolynomial (Index c m p q) K :=
  eval₂ C (fun j => X (Sum.inl (i, j))) f.val

@[simp] theorem eval_traceEvaluationPolynomial (a : Parameters K c m p q)
    (f : Forms K m d) (i : Fin q) :
    eval a (traceEvaluationPolynomial (c := c) (p := p) f i) = traceEvaluation a d f i := by
  rw [traceEvaluationPolynomial, eval_eval₂]
  change eval₂ ((eval a).comp C) (fun j => eval a (X (Sum.inl (i, j)))) f.val = _
  have hc : (eval a).comp C = RingHom.id K := by ext x; simp
  rw [hc]
  simp only [eval_X]
  rfl

theorem traceEvaluation_isPolynomialFamily (d : ℕ) :
    IsPolynomialFamily (fun a : Parameters K c m p q => traceEvaluation a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply DeformationMatrix.isPolynomialFamily_pi
  intro i
  simpa only [eval_traceEvaluationPolynomial] using
    isPolynomialFamily_eval (traceEvaluationPolynomial (c := c) (p := p) f i)

end IdealGeneration.ConeParameterSpace
