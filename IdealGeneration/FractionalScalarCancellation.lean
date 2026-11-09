module

public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.ScalarTraceReduction
public import IdealGeneration.ScalarTraceDimensions
public import IdealGeneration.FractionalCompatibility
public import IdealGeneration.FractionalTraceChoice

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The outer scalar cancellation in the fractional hyperplane transfer

The hyperplane list consists of scalar points, the fixed partial point, and
full vector points. Sequence (3.2) removes precisely the scalar quotient.
-/

noncomputable section
namespace IdealGeneration.FractionalScalarCancellation
open MvPolynomial Module HyperplaneEuler HyperplaneEulerScalar ScalarTraceReduction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*}

/-- The ordered hyperplane configuration `A`, the partial point, and `T`. -/
def allOn {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K) :
    Fin (a + 1 + t) → Fin (n + 1) → K :=
  Fin.append (Fin.snoc A y) T

@[simp] theorem allOn_scalar {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K) (i : Fin a) :
    allOn A y T (Fin.castAdd t i.castSucc) = A i := by simp [allOn]

@[simp] theorem allOn_partial {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K) :
    allOn A y T (Fin.castAdd t (Fin.last a)) = y := by simp [allOn]

@[simp] theorem allOn_full {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K) (i : Fin t) :
    allOn A y T (Fin.natAdd (a + 1) i) = T i := by simp [allOn]

variable [Field K]

/-- The concatenated representatives agree with the ordinary appended chart configuration. -/
theorem allOn_chart_eq {n a t : ℕ} (A : PointCoordinates K n a)
    (y : Fin n → K) (T : PointCoordinates K n t) :
    allOn (fun i => chartPoint K A i) (Fin.snoc y 1) (fun i => chartPoint K T i) =
      fun i => chartPoint K
        (FractionalCompatibility.appendCoordinates (FractionalTraceChoice.adjoinPoint A y) T) i := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · funext k
      refine Fin.lastCases ?_ (fun l => ?_) k <;>
        simp [allOn, chartPoint, FractionalTraceChoice.adjoinPoint,
          FractionalCompatibility.appendCoordinates]
    · funext l
      refine Fin.lastCases ?_ (fun m => ?_) l <;>
        simp [allOn, chartPoint, FractionalTraceChoice.adjoinPoint,
          FractionalCompatibility.appendCoordinates]
  · simp [allOn]

/-- The scalar trace map is exactly the scalar evaluation used by the compatibility construction. -/
theorem traceScalarEvaluation_allOn_chart_eq {n a t d : ℕ}
    (A : PointCoordinates K n a) (y : Fin n → K) (T : PointCoordinates K n t) :
    traceScalarEvaluation (d := d)
      (allOn (fun i => chartPoint K A i) (Fin.snoc y 1) (fun i => chartPoint K T i)) =
      pointEvaluation K
        (FractionalCompatibility.appendCoordinates (FractionalTraceChoice.adjoinPoint A y) T) (d + 1) := by
  rw [allOn_chart_eq]
  rfl

/-- Scalar conditions at `A`, the partial condition at `y`, and full values at `T`. -/
def allAllowed {n a : ℕ} (A : Fin a → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (t : ℕ) :
    Fin (a + 1 + t) → Submodule K (Fin (n + 1) → K) :=
  Fin.append (Fin.snoc (fun i => TraceFiber (A i)) L) (fun _ => ⊥)

@[simp] theorem allAllowed_scalar {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (i : Fin a) :
    allAllowed A L t (Fin.castAdd t i.castSucc) = TraceFiber (A i) := by simp [allAllowed]

@[simp] theorem allAllowed_partial {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) :
    allAllowed A L t (Fin.castAdd t (Fin.last a)) = L := by simp [allAllowed]

@[simp] theorem allAllowed_full {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (i : Fin t) :
    allAllowed A L t (Fin.natAdd (a + 1) i) = ⊥ := by simp [allAllowed]

/-- Every allowed value lies in the corresponding trace fiber. -/
theorem allAllowed_le {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (hL : L ≤ TraceFiber y) :
    ∀ i, allAllowed A L t i ≤ TraceFiber (allOn A y T i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hL
    · simp
  · simp

/-- Split the three types of hyperplane value conditions. -/
theorem allowedValues_iff {n a t d : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K))
    (g : Fin (n + 1) → Forms K (n + 2) d) :
    (∀ i, tangentEvaluation (Fin.cons 0 (allOn A y T i)) g ∈ allAllowed A L t i) ↔
      (∀ i, tangentEvaluation (Fin.cons 0 (A i)) g ∈ TraceFiber (A i)) ∧
      tangentEvaluation (Fin.cons 0 y) g ∈ L ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (T i)) g = 0) := by
  rw [Fin.forall_fin_add]
  simp only [allOn, allAllowed, Fin.append_left, Fin.append_right]
  rw [Fin.forall_fin_succ']
  simp [and_assoc]

/-- Scalar membership is the actual evaluation of the tangential polynomial product. -/
theorem tangent_mem_traceFiber_iff {n d : ℕ} (y : Fin (n + 1) → K)
    (g : Fin (n + 1) → Forms K (n + 2) d) :
    tangentEvaluation (Fin.cons 0 y) g ∈ TraceFiber y ↔
      eval (Fin.cons 0 y) (tangentProduct K (n + 1) d g).val = 0 := by
  change pointDot y (tangentEvaluation (Fin.cons 0 y) g) = 0 ↔ _
  have heq : pointDot y (tangentEvaluation (Fin.cons 0 y) g) =
      eval (Fin.cons 0 y) (tangentProduct K (n + 1) d g).val := by
    simp [pointDot, tangentEvaluation, evaluationLinear, tangentProduct_val]
  rw [heq]

/-- The genuine residual evaluation before scalar cancellation. -/
abbrev residualMap {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :=
  mixedEvaluation (d := d) off (allOn A y T) (allAllowed A L t)

/-- The genuine lower Euler evaluation after scalar cancellation. -/
abbrev lowerMap {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y) :=
  relationEvaluation (d := d) off (allOn A y T) (allAllowed A L t)
    (allAllowed_le A y T L hL)

/-- The residual kernel has full off values, scalar `A` values, a partial value, and full `T` values. -/
theorem residualMap_eq_zero_iff {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (g : Fin (n + 1) → Forms K (n + 2) d) :
    residualMap off A y T L g = 0 ↔
      (∀ i, tangentEvaluation (off i) g = 0) ∧
      (∀ i, eval (Fin.cons 0 (A i)) (tangentProduct K (n + 1) d g).val = 0) ∧
      tangentEvaluation (Fin.cons 0 y) g ∈ L ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (T i)) g = 0) := by
  rw [mixedEvaluation_eq_zero_iff, allowedValues_iff]
  simp_rw [tangent_mem_traceFiber_iff]

/-- The lower Euler kernel retains only full off values, trace `T` values, and the partial value. -/
theorem lowerMap_eq_zero_iff {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y) (hoff : ∀ i, off i 0 ≠ 0)
    (f : (formMultiplication K (n + 2) d).ker) :
    lowerMap off A y T L hL f = 0 ↔
      (∀ i, relationValue (off i) f = 0) ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (T i)) (forgetNormal K (n + 1) d f) = 0) ∧
      tangentEvaluation (Fin.cons 0 y) (forgetNormal K (n + 1) d f) ∈ L := by
  rw [relationEvaluation_eq_zero_iff off (allOn A y T) (allAllowed A L t)
    (allAllowed_le A y T L hL) hoff, allowedValues_iff]
  have hA (i : Fin a) := relation_tangentValue_mem_traceFiber (A i) f
  constructor
  · rintro ⟨ho, _, hp, hT⟩
    exact ⟨ho, hT, hp⟩
  · rintro ⟨ho, hT, hp⟩
    exact ⟨ho, hA, hp, hT⟩

/-- The tangential value on the hyperplane is the evaluation of the restricted relation. -/
theorem tangentEvaluation_forgetNormal_eq_trace {n d : ℕ} (y : Fin (n + 1) → K)
    (f : Relations K (n + 2) d) :
    tangentEvaluation (Fin.cons 0 y) (forgetNormal K (n + 1) d f) =
      fun j => eval y (((trace K (n + 1) d f).val j).val) := by
  funext j
  exact (eval_hyperplaneRestrict K (n + 1) (f.val j.succ).val y).symm

/-- The reduced kernel expressed using the actual restricted Euler relation. -/
theorem lowerMap_eq_zero_iff_trace {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y) (hoff : ∀ i, off i 0 ≠ 0)
    (f : Relations K (n + 2) d) :
    lowerMap off A y T L hL f = 0 ↔
      (∀ i, relationValue (off i) f = 0) ∧
      (∀ i, (fun j => eval (T i) (((trace K (n + 1) d f).val j).val)) = 0) ∧
      (fun j => eval y (((trace K (n + 1) d f).val j).val)) ∈ L := by
  simpa only [tangentEvaluation_forgetNormal_eq_trace] using
    lowerMap_eq_zero_iff off A y T L hL hoff f

/-- The scalar isomorphism identifies the two actual kernels. -/
def cancellationKernelEquiv {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y)
    (heval : Function.Injective (traceScalarEvaluation (d := d) (allOn A y T))) :
    (residualMap (d := d) off A y T L).ker ≃ₗ[K] (lowerMap (d := d) off A y T L hL).ker :=
  kernelEquiv off (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) heval

/-- Injectivity passes through the scalar cancellation. -/
theorem cancellation_injective_iff {n a t z d : ℕ} (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y)
    (heval : Function.Injective (traceScalarEvaluation (d := d) (allOn A y T))) :
    Function.Injective (residualMap (d := d) off A y T L) ↔
      Function.Injective (lowerMap (d := d) off A y T L hL) :=
  injective_iff off (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) heval

/-- Independence passes through a bijective scalar evaluation. -/
theorem cancellation_surjective_iff [CharZero K] {n a t z d : ℕ}
    (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y)
    (heval : Function.Bijective (traceScalarEvaluation (d := d) (allOn A y T))) :
    Function.Surjective (residualMap (d := d) off A y T L) ↔
      Function.Surjective (lowerMap (d := d) off A y T L hL) :=
  surjective_iff off (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) heval

/-- Maximal rank passes through the scalar cancellation. -/
theorem cancellation_maximalRank_iff [CharZero K] {n a t z d : ℕ}
    (off : Fin z → Fin (n + 2) → K)
    (A : Fin a → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (T : Fin t → Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : L ≤ TraceFiber y)
    (heval : Function.Bijective (traceScalarEvaluation (d := d) (allOn A y T))) :
    HasMaximalRank (residualMap (d := d) off A y T L) ↔
      HasMaximalRank (lowerMap (d := d) off A y T L hL) :=
  maximalRank_iff off (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) heval

/-- Normalization of all three parts normalizes the combined scalar configuration. -/
theorem allOn_last {n a t : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K)
    (hA : ∀ i, A i (Fin.last n) = 1) (hy : y (Fin.last n) = 1)
    (hT : ∀ i, T i (Fin.last n) = 1) :
    ∀ i, allOn A y T i (Fin.last n) = 1 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hy
    · simpa using hA j
  · simpa using hT j

/-- The scalar-point contributions disappear from the reduced dimension sum. -/
theorem allAllowed_reduced_sum {n a : ℕ} (A : Fin a → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (t : ℕ)
    (hA : ∀ i, A i (Fin.last n) = 1) :
    (∑ i, (n - finrank K (allAllowed A L t i))) =
      t * n + (n - finrank K L) := by
  have hdim (i : Fin a) : finrank K (TraceFiber (A i)) = n := by
    have hne : ∃ j, A i j ≠ 0 := ⟨Fin.last n, by rw [hA i]; exact one_ne_zero⟩
    simpa using traceFiber_finrank (A i) hne
  let dim := fun W : Submodule K (Fin (n + 1) → K) => finrank K W
  have ha' (i : Fin a) : finrank K (allAllowed A L t (Fin.castAdd t i.castSucc)) = n :=
    (congrArg dim (allAllowed_scalar (t := t) A L i)).trans (hdim i)
  have hy' : finrank K (allAllowed A L t (Fin.castAdd t (Fin.last a))) = finrank K L :=
    congrArg dim (allAllowed_partial (t := t) A L)
  have ht' (i : Fin t) : finrank K (allAllowed A L t (Fin.natAdd (a + 1) i)) = 0 :=
    (congrArg dim (allAllowed_full A L i)).trans (by simp [dim])
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  simp [ha', hy', ht', Nat.add_comm]

/-- The reduced target dimension in the outer fractional specialization. -/
theorem lowerTarget_finrank {n a t z : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (hL : L ≤ TraceFiber y)
    (hA : ∀ i, A i (Fin.last n) = 1) (hy : y (Fin.last n) = 1)
    (hT : ∀ i, T i (Fin.last n) = 1) :
    finrank K (conditionScalarProjection (p := z) (allOn A y T) (allAllowed A L t)
      (allAllowed_le A y T L hL)).ker =
      z * (n + 1) + t * n + (n - finrank K L) := by
  have hon : ∀ i, ∃ j, allOn A y T i j ≠ 0 := by
    intro i
    exact ⟨Fin.last n, by rw [allOn_last A y T hA hy hT i]; exact one_ne_zero⟩
  rw [conditionScalarProjection_ker_finrank_eq (p := z)
    (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) hon]
  simp only [Nat.add_sub_cancel]
  rw [allAllowed_reduced_sum A L t hA]
  omega

/-- The original residual target has one full vector value per point of `T`. -/
theorem residualTarget_finrank {n a t z : ℕ} (A : Fin a → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (T : Fin t → Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (hL : L ≤ TraceFiber y)
    (hA : ∀ i, A i (Fin.last n) = 1) (hy : y (Fin.last n) = 1)
    (hT : ∀ i, T i (Fin.last n) = 1) :
    finrank K (ConditionSpace (p := z) (allAllowed A L t)) =
      (z + t) * (n + 1) + a + (n + 1 - finrank K L) := by
  have hon : ∀ i, ∃ j, allOn A y T i j ≠ 0 := by
    intro i
    exact ⟨Fin.last n, by rw [allOn_last A y T hA hy hT i]; exact one_ne_zero⟩
  have hc := conditionScalarProjection_ker_finrank_add (p := z)
    (allOn A y T) (allAllowed A L t) (allAllowed_le A y T L hL) hon
  rw [lowerTarget_finrank A y T L hL hA hy hT] at hc
  have hdim := Submodule.finrank_mono hL
  rw [traceFiber_finrank y ⟨Fin.last n, by rw [hy]; exact one_ne_zero⟩] at hdim
  simp only [Nat.add_sub_cancel] at hdim
  rw [← hc, Nat.add_mul, Nat.mul_add t n 1, Nat.mul_one]
  omega

end IdealGeneration.FractionalScalarCancellation
