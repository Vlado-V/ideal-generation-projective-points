module

public import IdealGeneration.DifferentialPoint
public import IdealGeneration.DifferentialFiber
public import IdealGeneration.DifferentialResponse

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The independent-condition endpoint of the moving-point step

Residual quotient surjectivity supplies the actual kernel-to-cokernel response.
-/

noncomputable section
namespace IdealGeneration.DifferentialPoint
open MvPolynomial HyperplaneEuler Module
set_option maxHeartbeats 1200000
variable {K : Type*} [Field K]

local instance surjRelationsGroup {n d : ℕ} : AddCommGroup (Relations K n d) :=
  Module.addCommMonoidToAddCommGroup K

local instance surjFixedSpaceGroup {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) : AddCommGroup (fixedSpace off on B) :=
  Module.addCommMonoidToAddCommGroup K

/-- Vector evaluation on the residual polynomial tuples. -/
def tupleEvaluation {n m d : ℕ} (y : Fin m → K) :
    (Fin n → Forms K m d) →ₗ[K] (Fin n → K) where
  toFun g i := eval y (g i).val
  map_add' g h := by ext i; simp
  map_smul' c g := by ext i; simp

/-- The residual space after the fixed off-hyperplane and scalar conditions. -/
def residualSpace {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K) :
    Submodule K (Fin n → Forms K (n + 1) d) where
  carrier := {g | (∀ i j, eval (off i) (g j).val = 0) ∧
    (∀ i, eval (on i) (tangentProduct K n d g).val = 0)}
  zero_mem' := by simp
  add_mem' := by
    intro g h hg hh
    exact ⟨fun i j => by simp [hg.1 i j, hh.1 i j],
      fun i => by
        rw [map_add]
        change eval (on i) ((tangentProduct K n d g).val + (tangentProduct K n d h).val) = 0
        rw [map_add, hg.2 i, hh.2 i, add_zero]⟩
  smul_mem' := by
    intro c g hg
    exact ⟨fun i j => by simp [hg.1 i j],
      fun i => by
        rw [map_smul]
        change eval (on i) (c • (tangentProduct K n d g).val) = 0
        simp only [smul_eq_C_mul, map_mul, eval_C, hg.2 i, mul_zero]⟩

local instance residualSpaceGroup {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K) :
    AddCommGroup (residualSpace (d := d) off on) :=
  Module.addCommMonoidToAddCommGroup K

/-- The residual quotient condition at the point to be moved. -/
def residualQuotient {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K) :
    residualSpace (d := d) off on →ₗ[K] ((Fin n → K) ⧸ traceImage B y) :=
  (traceImage B y).mkQ.comp ((tupleEvaluation y).comp (residualSpace off on).subtype)

/-- A residual tuple gives an actual section satisfying all fixed conditions. -/
theorem normal_mem_fixed_of_residual {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (hon : ∀ i, on i 0 = 0)
    (g : residualSpace (d := d) off on) :
    normalInjection K n d g.val ∈ fixedSpace off on B := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro i
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [vectorEvaluation_apply, tangentProduct_val, g.property.1]
    · simp [vectorEvaluation_apply, g.property.1]
  · intro i
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [vectorEvaluation_apply, normalInjection_zero, Submodule.coe_neg,
        map_neg, Pi.zero_apply, neg_eq_zero] using g.property.2 i
    · simp [vectorEvaluation_apply, hon]

/-- Surjectivity of the residual quotient supplies any prescribed value modulo the trace image. -/
theorem exists_residual_value_mod_trace {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K)
    (hsurj : Function.Surjective (residualQuotient off on B y)) (q : Fin n → K) :
    ∃ g : residualSpace (d := d) off on,
      tupleEvaluation y g.val - q ∈ traceImage B y := by
  obtain ⟨g, hg⟩ := hsurj ((traceImage B y).mkQ q)
  refine ⟨g, ?_⟩
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (traceImage B y).mkQ (tupleEvaluation y g.val - q) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hg

/-- All full-vector and scalar residual conditions, before taking their kernel. -/
def residualFullConditions {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K) :
    (Fin n → Forms K (n + 1) d) →ₗ[K] (O → Fin n → K) × (H → K) where
  toFun g := (fun i => tupleEvaluation (off i) g,
    fun i => eval (on i) (tangentProduct K n d g).val)
  map_add' g h := by ext <;> simp [tupleEvaluation, map_add]
  map_smul' c g := by ext <;> simp [tupleEvaluation, map_smul]

/-- The complete residual conditions in Lemma 3.4. -/
def residualConditions {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K) :
    (Fin n → Forms K (n + 1) d) →ₗ[K]
      ((O → Fin n → K) × (H → K)) × ((Fin n → K) ⧸ traceImage B y) :=
  (residualFullConditions off on).prod ((traceImage B y).mkQ.comp (tupleEvaluation y))

/-- Independence of the complete residual conditions implies independence of the fixed ones. -/
theorem residualFullConditions_surjective {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K)
    (h : Function.Surjective (residualConditions off on B y)) :
    Function.Surjective (residualFullConditions (d := d) off on) := by
  intro z
  obtain ⟨g, hg⟩ := h (z, 0)
  exact ⟨g, congrArg Prod.fst hg⟩

/-- Independence also makes the last quotient condition onto on the fixed residual kernel. -/
theorem residualQuotient_surjective {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K)
    (h : Function.Surjective (residualConditions off on B y)) :
    Function.Surjective (residualQuotient off on B y) := by
  intro q
  obtain ⟨g, hg⟩ := h (0, q)
  have hfull : residualFullConditions off on g = 0 := congrArg Prod.fst hg
  have hmem : g ∈ residualSpace off on := by
    constructor
    · intro i j
      exact congrFun (congrFun (congrArg Prod.fst hfull) i) j
    · intro i
      exact congrFun (congrArg Prod.snd hfull) i
  refine ⟨⟨g, hmem⟩, ?_⟩
  exact congrArg Prod.snd hg

/-- Away from the hyperplane the tangential components determine a full Euler value. -/
theorem evaluation_zero_of_succ_zero {n d : ℕ} (y : Fin (n + 1) → K)
    (hy : y 0 ≠ 0) (f : Relations K (n + 1) d)
    (hsucc : ∀ i : Fin n, vectorEvaluation y f i.succ = 0) : vectorEvaluation y f = 0 := by
  have hf : (∑ j, X j * (f.val j).val) = 0 := congrArg Subtype.val f.property
  have he := congrArg (eval y) hf
  simp only [map_sum, map_mul, eval_X, map_zero] at he
  rw [Fin.sum_univ_succ] at he
  have hnormal : vectorEvaluation y f 0 = 0 := by
    have hs : (∑ i : Fin n, y i.succ * eval y (f.val i.succ).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← vectorEvaluation_apply, hsucc i, mul_zero]
    rw [hs, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hy
  ext j
  exact Fin.cases hnormal hsucc j

/-- The fixed sections map to their allowed traces. -/
def fixedTrace {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) : fixedSpace off on B →ₗ[K] B where
  toFun f := ⟨trace K n (d + 1) f.val, f.property.1⟩
  map_add' f g := Subtype.ext ((trace K n (d + 1)).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((trace K n (d + 1)).map_smul c f.val)

/-- Independent residual conditions let every permitted trace lift through the fixed full points. -/
theorem fixedTrace_surjective_of_residual {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1)))
    (hoff : ∀ i, off i 0 ≠ 0) (hon : ∀ i, on i 0 = 0)
    (hBon : ∀ b : B, ∀ i, vectorEvaluation (fun j => on i j.succ) b.val = 0)
    (hres : Function.Surjective (residualFullConditions (d := d) off on)) :
    Function.Surjective (fixedTrace off on B) := by
  intro b
  let f := extend K n (d + 1) b.val
  let values : O → Fin n → K := fun i j =>
    -(off i 0)⁻¹ * vectorEvaluation (off i) f j.succ
  obtain ⟨g, hg⟩ := hres (values, 0)
  let F := f + normalInjection K n d g
  have htrace : trace K n (d + 1) F = b.val := by
    simp [F, f]
  have hoffF (i : O) : vectorEvaluation (off i) F = 0 := by
    apply evaluation_zero_of_succ_zero (off i) (hoff i)
    intro j
    have hgj : eval (off i) (g j).val = values i j :=
      congrFun (congrFun (congrArg Prod.fst hg) i) j
    change vectorEvaluation (off i) (f + normalInjection K n d g) j.succ = 0
    rw [map_add]
    change vectorEvaluation (off i) f j.succ +
      eval (off i) (X 0 * (g j).val) = 0
    rw [map_mul, eval_X, hgj]
    dsimp [values]
    field_simp [hoff i]
    ring
  have honF (i : H) : vectorEvaluation (on i) F = 0 := by
    change vectorEvaluation (on i) (f + normalInjection K n d g) = 0
    rw [map_add]
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · have hgi : eval (on i) (tangentProduct K n d g).val = 0 :=
        congrFun (congrArg Prod.snd hg) i
      change eval (on i) (f.val 0).val +
        eval (on i) (-(tangentProduct K n d g).val) = 0
      have hfzero : (f.val 0).val = 0 := rfl
      rw [hfzero, map_zero, map_neg, hgi]
      simp
    · have hb := congrFun (hBon b i) k
      have ht := trace_evaluation (on i) (hon i) f k
      rw [show trace K n (d + 1) f = b.val from trace_extend K n (d + 1) b.val] at ht
      change vectorEvaluation (on i) f k.succ + eval (on i) (X 0 * (g k).val) = 0
      rw [← ht, hb]
      simp [hon]
  have hmember : trace K n (d + 1) F ∈ B := by
    rw [htrace]
    exact b.property
  refine ⟨⟨F, hmember, hoffF, honF⟩, ?_⟩
  apply Subtype.ext
  exact htrace

/-- Residual tuples inject into the space satisfying the fixed conditions. -/
def residualNormal {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (hon : ∀ i, on i 0 = 0) :
    residualSpace (d := d) off on →ₗ[K] fixedSpace off on B where
  toFun g := ⟨normalInjection K n d g.val, normal_mem_fixed_of_residual off on B hon g⟩
  map_add' g h := Subtype.ext ((normalInjection K n d).map_add g.val h.val)
  map_smul' c g := Subtype.ext ((normalInjection K n d).map_smul c g.val)

/-- Coordinates in the Euler fiber obtained by forgetting the final component. -/
def chartProjection {n : ℕ} : (Fin (n + 2) → K) →ₗ[K] K × (Fin n → K) where
  toFun w := (w 0, fun i => w i.castSucc.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation in the normalized final-coordinate chart. -/
def chartEvaluation {n d : ℕ} (y : Fin (n + 2) → K) :
    Relations K (n + 2) d →ₗ[K] K × (Fin n → K) :=
  chartProjection.comp (vectorEvaluation y)

/-- The chart coordinates vanish precisely when the full Euler value vanishes. -/
theorem chartEvaluation_eq_zero_iff {n d : ℕ} (y : Fin (n + 2) → K)
    (hy : y (Fin.last (n + 1)) ≠ 0) (f : Relations K (n + 2) d) :
    chartEvaluation y f = 0 ↔ vectorEvaluation y f = 0 := by
  constructor
  · intro h
    have hfirst (j : Fin (n + 1)) : vectorEvaluation y f j.castSucc = 0 := by
      refine Fin.cases ?_ (fun i => ?_) j
      · exact congrArg Prod.fst h
      · exact congrFun (congrArg Prod.snd h) i
    have hf : (∑ j, X j * (f.val j).val) = 0 := congrArg Subtype.val f.property
    have he := congrArg (eval y) hf
    simp only [map_sum, map_mul, eval_X, map_zero] at he
    rw [Fin.sum_univ_castSucc] at he
    have hs : (∑ j : Fin (n + 1), y j.castSucc * eval y (f.val j.castSucc).val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [← vectorEvaluation_apply, hfirst j, mul_zero]
    rw [hs, zero_add] at he
    have hlast : vectorEvaluation y f (Fin.last (n + 1)) = 0 :=
      (mul_eq_zero.mp he).resolve_left hy
    ext j
    exact Fin.lastCases hlast hfirst j
  · intro h
    change chartProjection (vectorEvaluation y f) = 0
    rw [h, map_zero]

/-- The fixed-space evaluation in that chart. -/
def fixedChartEvaluation {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1))) (y : Fin (n + 2) → K) :
    fixedSpace off on B →ₗ[K] K × (Fin n → K) :=
  (chartEvaluation y).comp (fixedSpace off on B).subtype

/-- The scalar component of the residual normal tuple is the Euler dot product. -/
theorem eval_tangentProduct {n d : ℕ} (y : Fin (n + 1) → K)
    (g : Fin n → Forms K (n + 1) d) :
    eval y (tangentProduct K n d g).val =
      (∑ i, y i.succ * tupleEvaluation y g i) := by
  simp [tangentProduct_val, tupleEvaluation]

/-- At the hyperplane the normal tuple contributes only its scalar component. -/
theorem chartEvaluation_normal {n d : ℕ} (y : Fin (n + 2) → K)
    (hy : y 0 = 0) (g : Fin (n + 1) → Forms K (n + 2) d) :
    chartEvaluation y (normalInjection K (n + 1) d g) =
      (-DifferentialFiber.dot (fun i => y i.succ) (tupleEvaluation y g), 0) := by
  apply Prod.ext
  · change eval y (-(tangentProduct K (n + 1) d g).val) = _
    rw [map_neg, eval_tangentProduct]
    rfl
  · ext i
    change eval y (X 0 * (g i.castSucc).val) = 0
    simp [hy]

/-- The trace image lies in the tangent Euler fiber. -/
theorem traceImage_dot_eq_zero {n d : ℕ}
    (B : Submodule K (Relations K (n + 1) d)) (y : Fin (n + 2) → K)
    (l : Fin (n + 1) → K) (hl : l ∈ traceImage B y) :
    DifferentialFiber.dot (fun i => y i.succ) l = 0 := by
  obtain ⟨b, _, rfl⟩ := hl
  exact DifferentialFiber.dot_evaluation_eq_zero (fun i => y i.succ) d b

/-- Every value in the trace image occurs as the tangential part of a fixed section. -/
theorem fixedChart_trace_image {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1)))
    (y : Fin (n + 2) → K) (hy : y 0 = 0)
    (htrace : Function.Surjective (fixedTrace off on B))
    (l : Fin (n + 1) → K) (hl : l ∈ traceImage B y) :
    ∃ f : fixedSpace off on B,
      (fixedChartEvaluation off on B y f).2 = DifferentialFiber.dropLast l := by
  obtain ⟨b, hb, heval⟩ := hl
  obtain ⟨f, hf⟩ := htrace ⟨b, hb⟩
  refine ⟨f, ?_⟩
  ext i
  have hvalue : trace K (n + 1) (d + 1) f.val = b := congrArg Subtype.val hf
  have ht := trace_evaluation y hy f.val i.castSucc
  rw [hvalue] at ht
  change vectorEvaluation y f.val i.castSucc.succ = l i.castSucc
  rw [← ht]
  exact congrFun heval i.castSucc

/-- The genuine first response is onto when the residual quotient conditions are independent. -/
theorem chart_response_surjective {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1)))
    (y v : Fin (n + 2) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hylast : y (Fin.last (n + 1)) = 1) (hon : ∀ i, on i 0 = 0)
    (htrace : Function.Surjective (fixedTrace off on B))
    (hres : Function.Surjective (residualQuotient off on B y)) :
    Function.Surjective (DeformationGeneral.response (V := fixedSpace off on B)
      (fixedChartEvaluation off on B y)
      (chartProjection.comp ((lineQuotient y v 0).comp (fixedSpace off on B).subtype))
      (fixedChartEvaluation off on B y).range.mkQ) := by
  apply DifferentialResponse.split_response_surjective
    (fixedChartEvaluation off on B y)
    (chartProjection.comp ((lineQuotient y v 0).comp (fixedSpace off on B).subtype))
    (residualNormal off on B hon)
    ((tupleEvaluation y).comp (residualSpace off on).subtype)
    (DifferentialFiber.dot (fun i => y i.succ))
    DifferentialFiber.dropLast (DifferentialFiber.tangentLift (fun i => y i.succ))
    (traceImage B y) DifferentialFiber.lastUnit (v 0) hv
  · apply DifferentialFiber.dot_lastUnit
    exact hylast
  · intro u
    apply DifferentialFiber.dot_tangentLift
    exact hylast
  · exact DifferentialFiber.dropLast_tangentLift _
  · exact traceImage_dot_eq_zero B y
  · exact hres
  · exact fixedChart_trace_image off on B y hy htrace
  · intro g
    exact chartEvaluation_normal y hy g.val
  · intro g
    ext i
    exact lineQuotient_normal_succ y v hy g.val i.castSucc

/-- Independent residual conditions make evaluation at a general moving point onto its Euler fiber. -/
theorem moving_point_surjective_principal_open {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (B : Submodule K (Relations K (n + 1) (d + 1)))
    (y v : Fin (n + 2) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hylast : y (Fin.last (n + 1)) = 1) (hon : ∀ i, on i 0 = 0)
    (htrace : Function.Surjective (fixedTrace off on B))
    (hres : Function.Surjective (residualQuotient off on B y)) :
    ∃ p : MvPolynomial (Fin 1) K, eval 0 p ≠ 0 ∧
      ∀ t : K, t ≠ 0 → eval (fun _ => t) p ≠ 0 →
        Function.Surjective (fixedChartEvaluation off on B (fun i => y i + t * v i)) := by
  let A : (Fin 1 → K) → (fixedSpace off on B →ₗ[K] K × (Fin n → K)) :=
    fun a => chartProjection.comp ((lineEvaluation y v (a 0)).comp (fixedSpace off on B).subtype)
  let D : (Fin 1 → K) → (fixedSpace off on B →ₗ[K] K × (Fin n → K)) :=
    fun a => chartProjection.comp ((lineQuotient y v (a 0)).comp (fixedSpace off on B).subtype)
  have hA : IsPolynomialFamily A := by
    apply isPolynomialFamily_linearMap
    intro f
    exact ((lineEvaluation_polynomial y v).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin (n + 2) → K) f.val)).linear_comp chartProjection
  have hD : IsPolynomialFamily D := by
    apply isPolynomialFamily_linearMap
    intro f
    exact ((lineQuotient_polynomial y v).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin (n + 2) → K) f.val)).linear_comp chartProjection
  have hfactor : ∀ a, A a = A 0 + a 0 • D a := by
    intro a
    apply LinearMap.ext
    intro f
    change chartProjection ((lineEvaluation y v (a 0)) f.val) =
      chartProjection ((lineEvaluation y v 0) f.val) +
        a 0 • chartProjection ((lineQuotient y v (a 0)) f.val)
    rw [lineEvaluation_expansion]
    simp
  have hzero : A 0 = fixedChartEvaluation off on B y := by
    dsimp [A, fixedChartEvaluation, chartEvaluation]
    rw [lineEvaluation_zero]
    rfl
  have hresponse : Function.Surjective (DeformationGeneral.response
      (A 0) (D 0) (A 0).range.mkQ) := by
    rw [hzero]
    exact chart_response_surjective off on B y v hy hv hylast hon htrace hres
  obtain ⟨p, hp, hgood⟩ := DifferentialResponse.surjective_principal_open_of_response_surjective
    A D hA hD hfactor hresponse
  refine ⟨p, hp, fun t ht hpt => ?_⟩
  have h := hgood (fun _ => t) ht hpt
  have heq : A (fun _ => t) = fixedChartEvaluation off on B (fun i => y i + t * v i) := by
    apply LinearMap.ext
    intro f
    apply congrArg chartProjection
    ext i
    exact lineEvaluation_apply y v t f.val i
  rwa [heq] at h

/-- The on-hyperplane trace constraints, off-hyperplane full values, and on-hyperplane normal values. -/
def fixedConditionEvaluation {n d : ℕ} {O H C : Type*}
    [AddCommGroup C] [Module K C]
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (T : Relations K n (d + 1) →ₗ[K] C) :
    Relations K (n + 1) (d + 1) →ₗ[K] (O → Fin n → K) × ((H → K) × C) where
  toFun f := (fun i j => vectorEvaluation (off i) f j.succ,
    (fun i => vectorEvaluation (on i) f 0, T (trace K n (d + 1) f)))
  map_add' f g := by
    apply Prod.ext
    · ext i j
      exact congrFun ((vectorEvaluation (off i)).map_add f g) j.succ
    · apply Prod.ext
      · ext i
        exact congrFun ((vectorEvaluation (on i)).map_add f g) 0
      · simp
  map_smul' c f := by
    apply Prod.ext
    · ext i j
      exact congrFun ((vectorEvaluation (off i)).map_smul c f) j.succ
    · apply Prod.ext
      · ext i
        exact congrFun ((vectorEvaluation (on i)).map_smul c f) 0
      · simp

/-- Independent residual full conditions and independent trace conditions give independent fixed conditions. -/
theorem fixedConditionEvaluation_surjective {n d : ℕ} {O H C : Type*}
    [AddCommGroup C] [Module K C]
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (T : Relations K n (d + 1) →ₗ[K] C)
    (hoff : ∀ i, off i 0 ≠ 0)
    (hT : Function.Surjective T)
    (hres : Function.Surjective (residualFullConditions (d := d) off on)) :
    Function.Surjective (fixedConditionEvaluation off on T) := by
  rintro ⟨a, b, c⟩
  obtain ⟨β, hβ⟩ := hT c
  let f := extend K n (d + 1) β
  let values : O → Fin n → K := fun i j =>
    (off i 0)⁻¹ * (a i j - vectorEvaluation (off i) f j.succ)
  obtain ⟨g, hg⟩ := hres (values, -b)
  refine ⟨f + normalInjection K n d g, ?_⟩
  apply Prod.ext
  · ext i j
    have hgj : eval (off i) (g j).val = values i j :=
      congrFun (congrFun (congrArg Prod.fst hg) i) j
    change vectorEvaluation (off i) (f + normalInjection K n d g) j.succ = a i j
    rw [map_add]
    change vectorEvaluation (off i) f j.succ + eval (off i) (X 0 * (g j).val) = a i j
    rw [map_mul, eval_X, hgj]
    dsimp [values]
    field_simp [hoff i]
    ring
  · apply Prod.ext
    · ext i
      have hgi : eval (on i) (tangentProduct K n d g).val = -b i :=
        congrFun (congrArg Prod.snd hg) i
      change vectorEvaluation (on i) (f + normalInjection K n d g) 0 = b i
      rw [map_add]
      change eval (on i) (f.val 0).val + eval (on i) (-(tangentProduct K n d g).val) = b i
      have hfzero : (f.val 0).val = 0 := rfl
      rw [hfzero, map_zero, map_neg, hgi]
      simp
    · change T (trace K n (d + 1) (f + normalInjection K n d g)) = c
      simpa [f] using hβ

/-- These coordinate conditions have exactly the fixed-space kernel. -/
theorem fixedConditionEvaluation_ker {n d : ℕ} {O H C : Type*}
    [AddCommGroup C] [Module K C]
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (T : Relations K n (d + 1) →ₗ[K] C)
    (hoff : ∀ i, off i 0 ≠ 0) (hon : ∀ i, on i 0 = 0)
    (hTon : ∀ b : T.ker, ∀ i, vectorEvaluation (fun j => on i j.succ) b.val = 0) :
    (fixedConditionEvaluation off on T).ker = fixedSpace off on T.ker := by
  ext f
  constructor
  · intro hf
    change fixedConditionEvaluation off on T f = 0 at hf
    have htrace : trace K n (d + 1) f ∈ T.ker := by
      change T (trace K n (d + 1) f) = 0
      exact congrArg (fun z : (O → Fin n → K) × ((H → K) × C) => z.2.2) hf
    refine ⟨htrace, ?_, ?_⟩
    · intro i
      apply evaluation_zero_of_succ_zero (off i) (hoff i)
      intro j
      exact congrFun (congrFun (congrArg Prod.fst hf) i) j
    · intro i
      ext j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact congrFun (congrArg (fun z => z.2.1) hf) i
      · rw [← trace_evaluation (on i) (hon i)]
        exact congrFun (hTon ⟨trace K n (d + 1) f, htrace⟩ i) k
  · rintro ⟨htrace, hoffF, honF⟩
    apply Prod.ext
    · ext i j
      exact congrFun (hoffF i) j.succ
    · apply Prod.ext
      · ext i
        exact congrFun (honF i) 0
      · exact htrace

section Combine
variable {V C W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C]
  [AddCommGroup W] [Module K W]

/-- Surjectivity of fixed conditions and of the new conditions on their kernel combine. -/
theorem independent_conditions_combine (F : V →ₗ[K] C) (M : V →ₗ[K] W)
    (hF : Function.Surjective F)
    (hM : Function.Surjective (M.comp F.ker.subtype)) :
    Function.Surjective (F.prod M) := by
  rintro ⟨c, w⟩
  obtain ⟨x, hx⟩ := hF c
  obtain ⟨k, hk⟩ := hM (w - M x)
  refine ⟨x + k.val, ?_⟩
  apply Prod.ext
  · change F (x + k.val) = c
    rw [map_add, hx, k.property, add_zero]
  · change M (x + k.val) = w
    rw [map_add]
    change M x + M k.val = w
    rw [show M k.val = w - M x from hk]
    abel

end Combine

/-- The independent-condition assertion of Lemma 3.4, with actual residual and trace evaluation maps. -/
theorem moving_point_independent_principal_open {n d : ℕ} {O H C : Type*}
    [AddCommGroup C] [Module K C]
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (T : Relations K (n + 1) (d + 1) →ₗ[K] C)
    (y v : Fin (n + 2) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hylast : y (Fin.last (n + 1)) = 1)
    (hoff : ∀ i, off i 0 ≠ 0) (hon : ∀ i, on i 0 = 0)
    (hTon : ∀ b : T.ker, ∀ i, vectorEvaluation (fun j => on i j.succ) b.val = 0)
    (hT : Function.Surjective T)
    (hres : Function.Surjective (residualConditions off on T.ker y)) :
    ∃ p : MvPolynomial (Fin 1) K, eval 0 p ≠ 0 ∧
      ∀ t : K, t ≠ 0 → eval (fun _ => t) p ≠ 0 →
        Function.Surjective ((fixedConditionEvaluation off on T).prod
          (chartEvaluation (fun i => y i + t * v i))) := by
  have hfull := residualFullConditions_surjective off on T.ker y hres
  have hfixedTrace := fixedTrace_surjective_of_residual off on T.ker hoff hon hTon hfull
  have hquot := residualQuotient_surjective off on T.ker y hres
  obtain ⟨p, hp, hgood⟩ := moving_point_surjective_principal_open
    off on T.ker y v hy hv hylast hon hfixedTrace hquot
  refine ⟨p, hp, fun t ht hpt => ?_⟩
  apply independent_conditions_combine
  · exact fixedConditionEvaluation_surjective off on T hoff hT hfull
  · intro w
    obtain ⟨f, hf⟩ := hgood t ht hpt w
    have hmem : f.val ∈ (fixedConditionEvaluation off on T).ker := by
      rw [fixedConditionEvaluation_ker off on T hoff hon hTon]
      exact f.property
    exact ⟨⟨f.val, hmem⟩, hf⟩

/-- A nonconstant affine line meets a finite list of point representatives at finitely many parameters. -/
theorem finite_line_collision_parameters {m : ℕ} {I : Type*} [Finite I]
    (points : I → Fin m → K) (y v : Fin m → K) (j : Fin m) (hv : v j ≠ 0) :
    Set.Finite {t : K | ∃ i, (fun k => y k + t * v k) = points i} := by
  apply (Set.finite_range (fun i : I => (points i j - y j) / v j)).subset
  rintro t ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply (div_eq_iff hv).mpr
  have hj := congrFun hi j
  linear_combination -hj

/-- A nonzero independent specialization can avoid any finite list of line parameters. -/
theorem exists_moving_point_independent_avoiding [Infinite K]
    {n d : ℕ} {O H C : Type*} [AddCommGroup C] [Module K C]
    (off : O → Fin (n + 2) → K) (on : H → Fin (n + 2) → K)
    (T : Relations K (n + 1) (d + 1) →ₗ[K] C)
    (y v : Fin (n + 2) → K) (hy : y 0 = 0) (hv : v 0 ≠ 0)
    (hylast : y (Fin.last (n + 1)) = 1)
    (hoff : ∀ i, off i 0 ≠ 0) (hon : ∀ i, on i 0 = 0)
    (hTon : ∀ b : T.ker, ∀ i, vectorEvaluation (fun j => on i j.succ) b.val = 0)
    (hT : Function.Surjective T)
    (hres : Function.Surjective (residualConditions off on T.ker y))
    (F : Set K) (hF : F.Finite) :
    ∃ t : K, t ≠ 0 ∧ (y 0 + t * v 0) ≠ 0 ∧ t ∉ F ∧
      Function.Surjective ((fixedConditionEvaluation off on T).prod
        (chartEvaluation (fun i => y i + t * v i))) := by
  obtain ⟨p, hp, hgood⟩ := moving_point_independent_principal_open
    off on T y v hy hv hylast hoff hon hTon hT hres
  obtain ⟨t, ht, hpt, htF⟩ := DifferentialResponse.exists_parameter_avoiding_finite p hp F hF
  exact ⟨t, ht, by simpa [hy] using mul_ne_zero ht hv, htF, hgood t ht hpt⟩

end IdealGeneration.DifferentialPoint
