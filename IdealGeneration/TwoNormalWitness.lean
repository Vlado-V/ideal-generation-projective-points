module

public import IdealGeneration.TwoNormalOpen
public import IdealGeneration.TwoNormalRestriction
public import IdealGeneration.HyperplanePoints

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Actual point configurations for the two-normal restriction argument

A retained group is joined to a trace configuration embedded twice. The
resulting homogeneous point ideal is exactly the scalar-correction ideal.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (n : ℕ)

/-- Join ambient retained points to points on the common trace. -/
def twoNormalConfiguration {p q : ℕ}
    (x : PointCoordinates K (n + 2) p) (a : PointCoordinates K n q) :
    PointCoordinates K (n + 2) (p + q) :=
  hyperplaneConfiguration x (embedHyperplanePoints a)

/-- Evaluating a twice-restricted polynomial equals evaluation on the
common trace embedded into the ambient space. -/
theorem eval_restrictTrace_at_chart {q : ℕ}
    (a : PointCoordinates K n q) (i : Fin q) (f : Poly K (n + 3)) :
    eval (chartPoint K a i) (restrictTrace K (n + 1) f) =
      eval (chartPoint K (embedHyperplanePoints (embedHyperplanePoints a)) i) f := by
  simp only [restrictTrace, AlgHom.comp_apply, eval_hyperplaneRestrict,
    chartPoint_embedHyperplanePoints]

/-- The scalar correction ideal is a genuine homogeneous ideal of points. -/
theorem twoNormalConfiguration_piece_eq {p q d : ℕ}
    (x : PointCoordinates K (n + 2) p) (a : PointCoordinates K n q) :
    pointDegreePiece K (twoNormalConfiguration K n x a) d =
      specializedPiece K (n + 1) x (chartPoint K a) d := by
  ext f
  rw [twoNormalConfiguration, mem_hyperplaneConfiguration_piece_iff]
  constructor
  · rintro ⟨hx, ha⟩
    change (pointEvaluation K x d f,
      traceEvaluation K (n + 1) (chartPoint K a) d (restrictTraceForm K (n + 1) d f)) = 0
    apply Prod.ext
    · change pointEvaluation K x d f = 0 at hx
      exact hx
    · funext i
      change eval (chartPoint K a i) (restrictTrace K (n + 1) f.val) = 0
      rw [eval_restrictTrace_at_chart]
      exact (mem_pointDegreePiece _ f).mp ha i
  · intro hf
    have hx := congrArg Prod.fst hf
    have ha := congrArg Prod.snd hf
    refine ⟨hx, ?_⟩
    rw [mem_pointDegreePiece]
    intro i
    have hi := congrFun ha i
    change eval (chartPoint K a i) (restrictTrace K (n + 1) f.val) = 0 at hi
    rwa [eval_restrictTrace_at_chart] at hi

/-- Ordinary point-ideal multiplication is exactly the polynomial product
map used by the scalar correction theorem. -/
theorem trace_ideal_product_injective {q d : ℕ}
    (a : PointCoordinates K n q) (h : Function.Injective (pointMultiplication a d)) :
    Function.Injective (fun f : Fin (n + 1) → (traceEvaluation K (n + 1) (chartPoint K a) d).ker =>
      ∑ i, X i * (f i).val.val) := by
  intro f g hfg
  apply h
  apply Subtype.ext
  exact Subtype.ext hfg

/-- A lower-dimensional multiplication injection produces a genuine
specialized configuration with both required trace injections. -/
theorem exists_twoNormal_trace_injections [Infinite K] {q d : ℕ}
    (a : PointCoordinates K n q) (h : Function.Injective (pointMultiplication a d)) :
    ∃ x : PointCoordinates K (n + 2) (finrank K (restrictTraceForm K (n + 1) d).ker),
      Function.Injective ((restrictTraceForm K (n + 1) d).comp
        (pointDegreePiece K (twoNormalConfiguration K n x a) d).subtype) ∧
      Function.Injective (traceProduct K (n + 1) d
        (pointDegreePiece K (twoNormalConfiguration K n x a) d)) := by
  obtain ⟨x, hx, _, _⟩ := exists_offNormalEvaluation_bijective_nonzero K (n + 1) (by omega) d
  refine ⟨x, ?_, ?_⟩
  · rw [twoNormalConfiguration_piece_eq]
    intro f g hfg
    exact specializedRestriction_injective K (n + 1) x (chartPoint K a) hx.1 (Subtype.ext hfg)
  · rw [twoNormalConfiguration_piece_eq]
    exact specialized_traceProduct_injective K (n + 1) x (chartPoint K a) hx.1
      (trace_ideal_product_injective K n a h)

/-- The two injections hold on an actual nonempty open of ambient point
configurations, starting from the lower-dimensional point ideal. -/
theorem generic_twoNormal_trace_injections [Infinite K] {q d : ℕ}
    (a : PointCoordinates K n q) (h : Function.Injective (pointMultiplication a d)) :
    ∃ P : MvPolynomial
      (Fin (finrank K (restrictTraceForm K (n + 1) d).ker + q) × Fin (n + 2)) K,
      (∃ x, eval x P ≠ 0) ∧ ∀ x, eval x P ≠ 0 →
        Function.Injective ((restrictTraceForm K (n + 1) d).comp (pointDegreePiece K x d).subtype) ∧
        Function.Injective (traceProduct K (n + 1) d (pointDegreePiece K x d)) := by
  obtain ⟨x, hR, hP⟩ := exists_twoNormal_trace_injections K n a h
  obtain ⟨P, hP₀, hgood⟩ := generic_trace_injections_of_witness K (n + 1)
    (twoNormalConfiguration K n x a) hR hP
  exact ⟨P, ⟨_, hP₀⟩, hgood⟩

/-- Lemma 4.2 on a nonempty principal open of actual, distinct ambient
points with both normal coordinates nonzero. The ideal has the dimension
of the original trace ideal and inherits its multiplication injection. -/
theorem generic_twoNormal_point_ideal [CharZero K] {q d : ℕ}
    (a : PointCoordinates K n q)
    (hMul : Function.Injective (pointMultiplication a d))
    (hScalar : Function.Surjective (pointEvaluation K a d)) :
    ∃ P : MvPolynomial
      (Fin (finrank K (restrictTraceForm K (n + 1) d).ker + q) × Fin (n + 2)) K,
      (∃ x, eval x P ≠ 0) ∧ ∀ x, eval x P ≠ 0 →
        DistinctPoints K x ∧
        (∀ i, chartPoint K x i (0 : Fin (n + 3)) ≠ 0) ∧
        (∀ i, chartPoint K x i (0 : Fin (n + 2)).succ ≠ 0) ∧
        finrank K (pointDegreePiece K x d) = finrank K (pointDegreePiece K a d) ∧
        Function.Injective ((restrictTraceForm K (n + 1) d).comp (pointDegreePiece K x d).subtype) ∧
        Function.Injective (traceProduct K (n + 1) d (pointDegreePiece K x d)) := by
  classical
  let r := finrank K (restrictTraceForm K (n + 1) d).ker + q
  obtain ⟨P, hP, hPgood⟩ := generic_twoNormal_trace_injections K n a hMul
  obtain ⟨S, hS, hSgood⟩ := generic_pointHilbertFunction (K := K)
    (n := n + 2) (by omega) r
  let H := normalHeightPolynomial K (n + 1) (by omega) r
  have hPn : P ≠ 0 := by
    obtain ⟨x, hx⟩ := hP
    intro hz
    simp [hz] at hx
  have hSn : S ≠ 0 := by
    obtain ⟨x, hx⟩ := hS
    intro hz
    simp [hz] at hx
  have hHn : H ≠ 0 := by
    have heval : eval (fun _ => (1 : K)) H = 1 := by
      simp [H, normalHeightPolynomial]
    intro hz
    simp [hz] at heval
  have hn : P * S * H ≠ 0 := mul_ne_zero (mul_ne_zero hPn hSn) hHn
  have hex : ∃ x : PointCoordinates K (n + 2) r, eval x (P * S * H) ≠ 0 := by
    by_contra! h
    exact hn (MvPolynomial.funext h)
  refine ⟨P * S * H, hex, ?_⟩
  intro x hx
  have hparts : (eval x P ≠ 0 ∧ eval x S ≠ 0) ∧ eval x H ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hx
  obtain ⟨hdist, hpost⟩ := hSgood x hparts.1.2
  obtain ⟨hR, hT⟩ := hPgood x hparts.1.1
  have hnormal : ∀ i : Fin r,
      x (i, 0) ≠ 0 ∧ x (i, (⟨1, by omega⟩ : Fin (n + 2))) ≠ 0 := by
    have hh : ∀ i : Fin r,
        x (i, 0) * x (i, (⟨1, by omega⟩ : Fin (n + 2))) ≠ 0 := by
      simpa only [H, normalHeightPolynomial, map_prod, map_mul, eval_X,
        Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left] using hparts.2
    exact fun i => mul_ne_zero_iff.mp (hh i)
  have hdimTrace := (restrictTraceForm K (n + 1) d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (restrictTraceForm_surjective K (n + 1) d),
    finrank_top] at hdimTrace
  have hdimA := (pointEvaluation K a d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hScalar, finrank_top, Module.finrank_pi,
    Fintype.card_fin] at hdimA
  have hdimX := ideal_piece_finrank_of_postulation x (hpost d)
  rw [← finrank_chart_forms (K := K) (n + 2) d] at hdimX
  have hdim : finrank K (pointDegreePiece K x d) =
      finrank K (pointDegreePiece K a d) := by
    change q + finrank K (pointDegreePiece K a d) = finrank K (Forms K (n + 1) d) at hdimA
    change finrank K (Forms K (n + 1) d) +
      finrank K (restrictTraceForm K (n + 1) d).ker =
      finrank K (Forms K (n + 3) d) at hdimTrace
    change finrank K (pointDegreePiece K x d) = finrank K (Forms K (n + 3) d) - r at hdimX
    dsimp [r] at hdimX
    rw [← hdimTrace, ← hdimA] at hdimX
    omega
  refine ⟨hdist, ?_, ?_, hdim, hR, hT⟩
  · intro i
    change chartPoint K x i (0 : Fin (n + 2)).castSucc ≠ 0
    simpa only [chartPoint_castSucc] using (hnormal i).1
  · intro i
    change chartPoint K x i (⟨1, by omega⟩ : Fin (n + 2)).castSucc ≠ 0
    simpa only [chartPoint_castSucc] using (hnormal i).2

end IdealGeneration.TwoNormalTrace
