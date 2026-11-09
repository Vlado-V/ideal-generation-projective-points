module

public import IdealGeneration.SubspaceInterpolation
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar completion and compatibility for the fractional hyperplane step

An independent fixed scalar trace can be completed to a scalar isomorphism.
The completion condition remains compatible with any independently witnessed
polynomial condition on the joint trace and residual-point coordinates.
-/

noncomputable section
namespace IdealGeneration.FractionalCompatibility
open MvPolynomial Module
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {K : Type*} [Field K]

/-- Scalar evaluation at the fixed points followed by the new trace points. -/
def completedEvaluation {n p q : ℕ} (fixed : PointCoordinates K n p)
    (trace : PointCoordinates K n q) (d : ℕ) :
    Forms K (n + 1) d →ₗ[K] (Fin p → K) × (Fin q → K) :=
  (pointEvaluation K fixed d).prod (pointEvaluation K trace d)

/-- Concatenate the fixed and variable affine point coordinates. -/
def appendCoordinates {n p q : ℕ} (fixed : PointCoordinates K n p)
    (trace : PointCoordinates K n q) : PointCoordinates K n (p + q) :=
  fun ij => Fin.addCases (fun i => fixed (i, ij.2)) (fun i => trace (i, ij.2)) ij.1

@[simp] theorem chartPoint_append_left {n p q : ℕ}
    (fixed : PointCoordinates K n p) (trace : PointCoordinates K n q) (i : Fin p) :
    chartPoint K (appendCoordinates fixed trace) (Fin.castAdd q i) = chartPoint K fixed i := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint, appendCoordinates]

@[simp] theorem chartPoint_append_right {n p q : ℕ}
    (fixed : PointCoordinates K n p) (trace : PointCoordinates K n q) (i : Fin q) :
    chartPoint K (appendCoordinates fixed trace) (Fin.natAdd p i) = chartPoint K trace i := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint, appendCoordinates]

@[simp] theorem pointEvaluation_append_left {n p q d : ℕ}
    (fixed : PointCoordinates K n p) (trace : PointCoordinates K n q)
    (f : Forms K (n + 1) d) (i : Fin p) :
    pointEvaluation K (appendCoordinates fixed trace) d f (Fin.castAdd q i) =
      pointEvaluation K fixed d f i := by
  simp

@[simp] theorem pointEvaluation_append_right {n p q d : ℕ}
    (fixed : PointCoordinates K n p) (trace : PointCoordinates K n q)
    (f : Forms K (n + 1) d) (i : Fin q) :
    pointEvaluation K (appendCoordinates fixed trace) d f (Fin.natAdd p i) =
      pointEvaluation K trace d f i := by
  simp

/-- The scalar product map is the usual scalar evaluation on the concatenated points. -/
theorem pointEvaluation_append_bijective {n p q d : ℕ}
    (fixed : PointCoordinates K n p) (trace : PointCoordinates K n q)
    (h : Function.Bijective (completedEvaluation fixed trace d)) :
    Function.Bijective (pointEvaluation K (appendCoordinates fixed trace) d) := by
  constructor
  · intro f g hfg
    apply h.1
    apply Prod.ext
    · ext i
      change pointEvaluation K fixed d f i = pointEvaluation K fixed d g i
      simpa only [pointEvaluation_append_left] using congrFun hfg (Fin.castAdd q i)
    · ext i
      change pointEvaluation K trace d f i = pointEvaluation K trace d g i
      simpa only [pointEvaluation_append_right] using congrFun hfg (Fin.natAdd p i)
  · intro w
    obtain ⟨f, hf⟩ := h.2 ((fun i => w (Fin.castAdd q i)), (fun i => w (Fin.natAdd p i)))
    refine ⟨f, ?_⟩
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [pointEvaluation_append_left]
      exact congrFun (congrArg Prod.fst hf) j
    · intro j
      rw [pointEvaluation_append_right]
      exact congrFun (congrArg Prod.snd hf) j

/-- The fixed points impose independent scalar conditions and leave exactly `q` dimensions. -/
theorem fixed_kernel_finrank {n p q d : ℕ} (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed d))
    (hcount : p + q = (n + d).choose d) :
    finrank K (pointEvaluation K fixed d).ker = q := by
  have hr : finrank K (pointEvaluation K fixed d).range = p := by
    rw [LinearMap.range_eq_top.mpr hfixed, finrank_top]
    simp
  have hd := (pointEvaluation K fixed d).finrank_range_add_finrank_ker
  rw [hr, finrank_chart_forms] at hd
  omega

/-- Scalar isomorphism after completing a prescribed independent fixed trace. -/
theorem scalar_completion_principal_open [Infinite K] {n p q d : ℕ}
    (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed d))
    (hcount : p + q = (n + d).choose d) :
    ∃ D : MvPolynomial (Fin q × Fin n) K,
      (∃ trace : PointCoordinates K n q, eval trace D ≠ 0) ∧
      ∀ trace, eval trace D ≠ 0 →
        Function.Bijective (completedEvaluation fixed trace d) := by
  let U := (pointEvaluation K fixed d).ker
  have hdimU : finrank K U = q := fixed_kernel_finrank fixed hfixed hcount
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation_injective U q (by omega)
  refine ⟨D, hD, fun trace htrace => ?_⟩
  have hinj : Function.Injective (completedEvaluation fixed trace d) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hfixedf : pointEvaluation K fixed d f = 0 := congrArg Prod.fst hf
    have htracef : pointEvaluation K trace d f = 0 := congrArg Prod.snd hf
    have hmem : f ∈ U := hfixedf
    have hu : (⟨f, hmem⟩ : U) = 0 := by
      apply hgood trace htrace
      change pointEvaluation K trace d f = 0
      exact htracef
    exact congrArg Subtype.val hu
  have hdim : finrank K (Forms K (n + 1) d) =
      finrank K ((Fin p → K) × (Fin q → K)) := by
    simpa [finrank_chart_forms] using hcount.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- Coordinates for trace points on `H` and full points in the ambient projective chart. -/
abbrev JointIndex (n q z : ℕ) := (Fin q × Fin n) ⊕ (Fin z × Fin (n + 1))

abbrev JointCoordinates (n q z : ℕ) := JointIndex n q z → K

/-- The trace-point coordinates in the first parameter factor. -/
def traceCoordinates {n q z : ℕ} (a : JointCoordinates (K := K) n q z) :
    PointCoordinates K n q := fun ij => a (Sum.inl ij)

/-- The ambient-point coordinates in the second parameter factor. -/
def offCoordinates {n q z : ℕ} (a : JointCoordinates (K := K) n q z) :
    PointCoordinates K (n + 1) z := fun ij => a (Sum.inr ij)

/-- Lift a scalar completion condition to the joint parameter space. -/
def liftTracePolynomial {n q z : ℕ} (D : MvPolynomial (Fin q × Fin n) K) :
    MvPolynomial (JointIndex n q z) K := rename Sum.inl D

@[simp] theorem eval_liftTracePolynomial {n q z : ℕ}
    (a : JointCoordinates (K := K) n q z) (D : MvPolynomial (Fin q × Fin n) K) :
    eval a (liftTracePolynomial (z := z) D) = eval (traceCoordinates a) D := by
  rw [liftTracePolynomial, eval_rename]
  rfl

/-- The second factor avoids the hyperplane when this polynomial is nonzero. -/
def offPolynomial (n q z : ℕ) : MvPolynomial (JointIndex n q z) K :=
  rename Sum.inr (offHyperplanePolynomial (K := K) n z)

@[simp] theorem eval_offPolynomial_ne_zero_iff {n q z : ℕ}
    (a : JointCoordinates (K := K) n q z) :
    eval a (offPolynomial (K := K) n q z) ≠ 0 ↔ ∀ i, offCoordinates a (i, 0) ≠ 0 := by
  rw [offPolynomial, eval_rename]
  exact eval_offHyperplanePolynomial_ne_zero_iff (offCoordinates a)

/-- Scalar completion is compatible with any nonempty polynomial condition on both point groups. -/
theorem compatible_scalar_completion [Infinite K] {n p q z d : ℕ}
    (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed d))
    (hcount : p + q = (n + d).choose d)
    (P : MvPolynomial (JointIndex n q z) K)
    (hP : ∃ a : JointCoordinates (K := K) n q z, eval a P ≠ 0) :
    ∃ a : JointCoordinates (K := K) n q z,
      eval a P ≠ 0 ∧
      Function.Bijective (completedEvaluation fixed (traceCoordinates a) d) ∧
      ∀ i, offCoordinates a (i, 0) ≠ 0 := by
  obtain ⟨D, ⟨trace, htrace⟩, hgood⟩ := scalar_completion_principal_open fixed hfixed hcount
  let E : MvPolynomial (JointIndex n q z) K :=
    liftTracePolynomial D * offPolynomial n q z
  have hE : ∃ a : JointCoordinates (K := K) n q z, eval a E ≠ 0 := by
    refine ⟨Sum.elim trace (fun _ => 1), ?_⟩
    change eval (Sum.elim trace (fun _ => 1))
      (liftTracePolynomial D * offPolynomial n q z) ≠ 0
    rw [map_mul]
    apply mul_ne_zero
    · rw [eval_liftTracePolynomial]
      exact htrace
    · apply (eval_offPolynomial_ne_zero_iff _).mpr
      intro i
      exact one_ne_zero
  obtain ⟨a, haP, haE⟩ := principal_opens_meet P E hP hE
  have hparts : eval (traceCoordinates a) D ≠ 0 ∧
      eval a (offPolynomial (K := K) n q z) ≠ 0 := by
    simpa only [E, map_mul, mul_ne_zero_iff, eval_liftTracePolynomial] using haE
  exact ⟨a, haP, hgood _ hparts.1, (eval_offPolynomial_ne_zero_iff a).mp hparts.2⟩

/-- The same compatibility statement using the single concatenated scalar point configuration. -/
theorem compatible_scalar_completion_appended [Infinite K] {n p q z d : ℕ}
    (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed d))
    (hcount : p + q = (n + d).choose d)
    (P : MvPolynomial (JointIndex n q z) K)
    (hP : ∃ a : JointCoordinates (K := K) n q z, eval a P ≠ 0) :
    ∃ a : JointCoordinates (K := K) n q z,
      eval a P ≠ 0 ∧
      Function.Bijective (pointEvaluation K (appendCoordinates fixed (traceCoordinates a)) d) ∧
      ∀ i, offCoordinates a (i, 0) ≠ 0 := by
  obtain ⟨a, haP, haEval, haOff⟩ := compatible_scalar_completion fixed hfixed hcount P hP
  exact ⟨a, haP, pointEvaluation_append_bijective fixed (traceCoordinates a) haEval, haOff⟩

end IdealGeneration.FractionalCompatibility
