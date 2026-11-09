module

public import IdealGeneration.TwoNormalTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar correction over a codimension-two trace

The specialization in Lemma 4.2 retains enough off-trace points to determine
every form whose trace is zero. Subtracting the unique such correction
identifies the specialized point ideal with the ordinary trace point ideal.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- Evaluation at chosen representatives of points on the trace. -/
def traceEvaluation {q : ℕ} (y : Fin q → Fin m → K) (d : ℕ) :
    Forms K m d →ₗ[K] (Fin q → K) :=
  LinearMap.pi fun i => evaluationLinear K m d (y i)

/-- On normalized representatives this is the existing point-ideal evaluation. -/
@[simp] theorem traceEvaluation_chart {n q d : ℕ} (y : PointCoordinates K n q) :
    traceEvaluation K (n + 1) (chartPoint K y) d = pointEvaluation K y d := rfl

/-- Its kernel on normalized representatives is the genuine homogeneous point ideal. -/
@[simp] theorem traceEvaluation_chart_ker {n q d : ℕ} (y : PointCoordinates K n q) :
    (traceEvaluation K (n + 1) (chartPoint K y) d).ker = pointDegreePiece K y d := rfl

/-- Forms vanishing on the retained off-trace points and the trace points. -/
def specializedPiece {p q : ℕ} (x : PointCoordinates K (m + 1) p)
    (y : Fin q → Fin m → K) (d : ℕ) : Submodule K (Forms K (m + 2) d) :=
  ((pointEvaluation K x d).prod
    ((traceEvaluation K m y d).comp (restrictTraceForm K m d))).ker

/-- Evaluation on off-trace points restricted to forms with zero trace. -/
def offNormalEvaluation {p : ℕ} (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    (restrictTraceForm K m d).ker →ₗ[K] (Fin p → K) :=
  (pointEvaluation K x d).comp (restrictTraceForm K m d).ker.subtype

/-- Restriction of the specialized point ideal to the ordinary trace ideal. -/
def specializedRestriction {p q : ℕ} (x : PointCoordinates K (m + 1) p)
    (y : Fin q → Fin m → K) (d : ℕ) :
    specializedPiece K m x y d →ₗ[K] (traceEvaluation K m y d).ker where
  toFun f := ⟨restrictTraceForm K m d f.val, by
    have hf := congrArg Prod.snd f.property
    exact hf⟩
  map_add' f g := Subtype.ext ((restrictTraceForm K m d).map_add _ _)
  map_smul' c f := Subtype.ext ((restrictTraceForm K m d).map_smul _ _)

/-- Unique interpolation on the zero-trace forms makes ideal restriction injective. -/
theorem specializedRestriction_injective {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Injective (offNormalEvaluation K m x d)) :
    Function.Injective (specializedRestriction K m x y d) := by
  intro f g hfg
  have hr : restrictTraceForm K m d (f.val - g.val) = 0 := by
    have hh := congrArg Subtype.val hfg
    change restrictTraceForm K m d f.val = restrictTraceForm K m d g.val at hh
    rw [map_sub, hh, sub_self]
  let n : (restrictTraceForm K m d).ker := ⟨f.val - g.val, hr⟩
  have hn : offNormalEvaluation K m x d n = 0 := by
    have hf := congrArg Prod.fst f.property
    have hg := congrArg Prod.fst g.property
    change pointEvaluation K x d f.val = 0 at hf
    change pointEvaluation K x d g.val = 0 at hg
    change pointEvaluation K x d (f.val - g.val) = 0
    rw [map_sub, hf, hg, sub_self]
  have hnzero : n = 0 := hOff (by simpa using hn)
  apply Subtype.ext
  exact sub_eq_zero.mp (congrArg Subtype.val hnzero)

/-- Scalar correction supplies every trace-ideal form as a restriction. -/
theorem specializedRestriction_surjective {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Surjective (offNormalEvaluation K m x d)) :
    Function.Surjective (specializedRestriction K m x y d) := by
  intro w
  let lift := extendTraceForm K m d w.val
  obtain ⟨c, hc⟩ := hOff (pointEvaluation K x d lift)
  have hc0 : restrictTraceForm K m d c.val = 0 := c.property
  let f := lift - c.val
  have hf : f ∈ specializedPiece K m x y d := by
    change (pointEvaluation K x d f,
      traceEvaluation K m y d (restrictTraceForm K m d f)) = 0
    apply Prod.ext
    · change pointEvaluation K x d (lift - c.val) = 0
      change pointEvaluation K x d c.val = pointEvaluation K x d lift at hc
      rw [map_sub, hc, sub_self]
    · change traceEvaluation K m y d (restrictTraceForm K m d (lift - c.val)) = 0
      rw [map_sub, hc0, sub_zero]
      change traceEvaluation K m y d
        (restrictTraceForm K m d (extendTraceForm K m d w.val)) = 0
      rw [restrict_extendTraceForm]
      exact w.property
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  change restrictTraceForm K m d (lift - c.val) = w.val
  rw [map_sub, hc0, sub_zero]
  exact restrict_extendTraceForm K m w.val

/-- The scalar correction identifies the two actual homogeneous ideals. -/
def specializedRestrictionEquiv {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Bijective (offNormalEvaluation K m x d)) :
    specializedPiece K m x y d ≃ₗ[K] (traceEvaluation K m y d).ker :=
  LinearEquiv.ofBijective (specializedRestriction K m x y d)
    ⟨specializedRestriction_injective K m x y hOff.1,
      specializedRestriction_surjective K m x y hOff.2⟩

/-- The specialized ideal has exactly the dimension of the ordinary trace ideal. -/
theorem specializedPiece_finrank {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Bijective (offNormalEvaluation K m x d)) :
    finrank K (specializedPiece K m x y d) =
      finrank K (traceEvaluation K m y d).ker :=
  (specializedRestrictionEquiv K m x y hOff).finrank_eq

/-- Independent trace-point conditions give the dimension asserted in Lemma 4.2. -/
theorem specializedPiece_finrank_of_independent {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Bijective (offNormalEvaluation K m x d))
    (hy : Function.Surjective (traceEvaluation K m y d)) :
    finrank K (specializedPiece K m x y d) = finrank K (Forms K m d) - q := by
  rw [specializedPiece_finrank K m x y hOff]
  have h := (traceEvaluation K m y d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hy, finrank_top] at h
  have hdim : finrank K (Fin q → K) = q := by simp
  rw [hdim] at h
  omega

/-- The zero-trace space has the expected complementary dimension. -/
theorem traceKernel_finrank (d : ℕ) :
    finrank K (restrictTraceForm K m d).ker =
      finrank K (Forms K (m + 2) d) - finrank K (Forms K m d) := by
  have h := (restrictTraceForm K m d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (restrictTraceForm_surjective K m d), finrank_top] at h
  omega

/-- Injective multiplication on the ordinary trace ideal transfers through
scalar correction to multiplication of restricted specialized-ideal forms. -/
theorem specialized_traceProduct_injective {p q d : ℕ}
    (x : PointCoordinates K (m + 1) p) (y : Fin q → Fin m → K)
    (hOff : Function.Injective (offNormalEvaluation K m x d))
    (hProduct : Function.Injective (fun a : Fin m → (traceEvaluation K m y d).ker =>
      ∑ i, X i * (a i).val.val)) :
    Function.Injective (traceProduct K m d (specializedPiece K m x y d)) := by
  intro a b hab
  have hpol := congrArg Subtype.val hab
  simp only [traceProduct_val] at hpol
  have hrestrict :
      (fun i => specializedRestriction K m x y d (a i)) =
        (fun i => specializedRestriction K m x y d (b i)) := hProduct hpol
  funext i
  exact specializedRestriction_injective K m x y hOff (congrFun hrestrict i)

private theorem surjective_of_injective_equal_dimension
    {V W : Type*} [AddCommMonoid V] [Module K V] [Module.Finite K V]
    [AddCommMonoid W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hdim : finrank K V = finrank K W) : Function.Surjective f := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf

/-- A set of retained points can determine exactly all zero-trace forms. -/
theorem exists_offNormalEvaluation_bijective [Infinite K] (d : ℕ) :
    ∃ x : PointCoordinates K (m + 1) (finrank K (restrictTraceForm K m d).ker),
      Function.Bijective (offNormalEvaluation K m x d) := by
  obtain ⟨x, hx⟩ := exists_injective_subspaceEvaluation (restrictTraceForm K m d).ker
    (finrank K (restrictTraceForm K m d).ker) le_rfl
  have hi : Function.Injective (offNormalEvaluation K m x d) := hx
  have hdim : finrank K (restrictTraceForm K m d).ker =
      finrank K (Fin (finrank K (restrictTraceForm K m d).ker) → K) := by
    rw [Module.finrank_pi, Fintype.card_fin]
  exact ⟨x, hi, surjective_of_injective_equal_dimension K (offNormalEvaluation K m x d) hi hdim⟩

/-- The normal-height condition is itself a polynomial open condition. -/
def normalHeightPolynomial (hm : 1 ≤ m) (p : ℕ) :
    MvPolynomial (Fin p × Fin (m + 1)) K :=
  ∏ i : Fin p, X (i, (0 : Fin (m + 1))) * X (i, (⟨1, by omega⟩ : Fin (m + 1)))

/-- Retained scalar interpolation points can have both normal coordinates nonzero. -/
theorem exists_offNormalEvaluation_bijective_nonzero [Infinite K]
    (hm : 1 ≤ m) (d : ℕ) :
    ∃ x : PointCoordinates K (m + 1) (finrank K (restrictTraceForm K m d).ker),
      Function.Bijective (offNormalEvaluation K m x d) ∧
      (∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0) ∧
      (∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0) := by
  classical
  let p := finrank K (restrictTraceForm K m d).ker
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation_injective
    (restrictTraceForm K m d).ker p le_rfl
  have hDn : D ≠ 0 := by
    obtain ⟨a, ha⟩ := hD
    intro hz
    simp [hz] at ha
  let H := normalHeightPolynomial K m hm p
  have hH : H ≠ 0 := by
    have heval : eval (fun _ => (1 : K)) H = 1 := by simp [H, normalHeightPolynomial]
    intro hz
    simp [hz] at heval
  obtain ⟨x, hx⟩ : ∃ x : PointCoordinates K (m + 1) p, eval x (D * H) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hDn hH (MvPolynomial.funext h)
  have hparts : eval x D ≠ 0 ∧ eval x H ≠ 0 := by simpa using hx
  have hi : Function.Injective (offNormalEvaluation K m x d) := hgood x hparts.1
  have hs : ∀ i : Fin p, x (i, 0) ≠ 0 ∧ x (i, (⟨1, by omega⟩ : Fin (m + 1))) ≠ 0 := by
    have hh : ∀ i : Fin p,
        x (i, 0) * x (i, (⟨1, by omega⟩ : Fin (m + 1))) ≠ 0 := by
      simpa only [H, normalHeightPolynomial, map_prod, map_mul, eval_X,
        Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left] using hparts.2
    exact fun i => mul_ne_zero_iff.mp (hh i)
  have hdim : finrank K (restrictTraceForm K m d).ker = finrank K (Fin p → K) := by
    rw [Module.finrank_pi, Fintype.card_fin]
  refine ⟨x, ⟨hi, surjective_of_injective_equal_dimension K (offNormalEvaluation K m x d) hi hdim⟩, ?_, ?_⟩
  · intro i
    change chartPoint K x i (0 : Fin (m + 1)).castSucc ≠ 0
    simpa only [chartPoint_castSucc] using (hs i).1
  · intro i
    change chartPoint K x i (⟨1, by omega⟩ : Fin (m + 1)).castSucc ≠ 0
    simpa only [chartPoint_castSucc] using (hs i).2

end IdealGeneration.TwoNormalTrace
