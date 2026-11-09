module

public import IdealGeneration.DifferentialSurjectivity
public import IdealGeneration.FixedPointEulerWitness
public import IdealGeneration.FractionalTraceNumerics
public import IdealGeneration.ScalarTraceReduction
public import IdealGeneration.FractionalCompatibility
public import IdealGeneration.FixedPartialTraceLemma
public import IdealGeneration.FractionalNonvanishing
public import IdealGeneration.FractionalTraceChoice
public import IdealGeneration.FractionalInner
public import IdealGeneration.FractionalRegroupCoordinates
public import IdealGeneration.FractionalHyperplaneCounts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Assembly lemmas for the fractional hyperplane transfer

These statements compare full tangent values with the normalized coordinates
used by fixed-partial interpolation. They construct the trace kernel and the
injective evaluation at the extra point from adjacent interpolation assertions.
-/

noncomputable section
namespace IdealGeneration.FractionalHyperplane
open Module MvPolynomial DifferentialPoint DifferentialFiber HyperplaneEuler
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local instance relationGroup {n d : ℕ} : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

local instance relationSubmoduleGroup {n d : ℕ} (U : Submodule K (EulerRelations K n d)) :
    AddCommGroup U := Module.addCommMonoidToAddCommGroup K

/-- The Euler relation dimension in the paper's polynomial coordinates. -/
theorem eulerRelations_finrank [CharZero K] (n d : ℕ) :
    finrank K (EulerRelations K n d) =
      (n + 1) * N (n + 1) d - N (n + 1) (d + 1) := by
  have h := (formMultiplication K (n + 1) d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (formMultiplication_surjective (n + 1) d), finrank_top] at h
  have hsource : finrank K (Fin (n + 1) → Forms K (n + 1) d) =
      (n + 1) * N (n + 1) d := by
    simp [Module.finrank_pi_fintype, finrank_forms, N]
  have htarget : finrank K (Forms K (n + 1) (d + 1)) = N (n + 1) (d + 1) := by
    simpa only [N] using finrank_forms (K := K) (n + 1) (d + 1)
  rw [hsource, htarget] at h
  change finrank K (formMultiplication K (n + 1) d).ker = _
  omega

section KernelComparison
variable {V W Q : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

omit [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K Q] in
/-- Different coordinate descriptions with the same kernel preserve injectivity. -/
theorem injective_iff_of_kernel_eq (f : V →ₗ[K] W) (g : V →ₗ[K] Q)
    (hker : f.ker = g.ker) : Function.Injective f ↔ Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, hker]

/-- Equal kernels and equal condition-space dimensions preserve independence. -/
theorem surjective_iff_of_kernel_eq (f : V →ₗ[K] W) (g : V →ₗ[K] Q)
    (hker : f.ker = g.ker) (hdim : finrank K W = finrank K Q) :
    Function.Surjective f ↔ Function.Surjective g := by
  have hrank : finrank K f.range = finrank K g.range := by
    have hf := f.finrank_range_add_finrank_ker
    have hg := g.finrank_range_add_finrank_ker
    rw [hker] at hf
    omega
  constructor
  · intro hf
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [← hrank, LinearMap.range_eq_top.mpr hf, finrank_top, hdim]
  · intro hg
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank, LinearMap.range_eq_top.mpr hg, finrank_top, ← hdim]

end KernelComparison

/-- Dropping the normalized last coordinate preserves membership in a tangent subspace. -/
theorem mem_tangent_subspace_iff_drop {n : ℕ}
    (y : Fin (n + 1) → K) (hy : y (Fin.last n) = 1)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot y l = 0)
    (w : Fin (n + 1) → K) (hw : dot y w = 0) :
    w ∈ L ↔ dropLast w ∈ L.map dropLast := by
  constructor
  · intro h
    exact ⟨w, h, rfl⟩
  · rintro ⟨l, hl, heq⟩
    have hrecover := congrArg (tangentLift y) heq
    rw [tangentLift_dropLast_of_dot_eq_zero y l hy (hL l hl),
      tangentLift_dropLast_of_dot_eq_zero y w hy hw] at hrecover
    exact hrecover ▸ hl

/-- The same coordinate reduction preserves the dimension of the partial subspace. -/
theorem finrank_drop_tangent_subspace {n : ℕ}
    (y : Fin (n + 1) → K) (hy : y (Fin.last n) = 1)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot y l = 0) :
    finrank K (L.map dropLast) = finrank K L := by
  let f : L →ₗ[K] (Fin n → K) := dropLast.comp L.subtype
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hh := congrArg (tangentLift y) h
    change tangentLift y (dropLast a.val) = tangentLift y (dropLast b.val) at hh
    rwa [tangentLift_dropLast_of_dot_eq_zero y a.val hy (hL a.val a.property),
      tangentLift_dropLast_of_dot_eq_zero y b.val hy (hL b.val b.property)] at hh
  have hr : f.range = L.map dropLast := by
    ext w
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l.val, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_of_inj hf

/-- Full Euler evaluation lies in the tangent fiber at every representative. -/
theorem full_euler_value_tangent {n d : ℕ} (y : Fin (n + 1) → K)
    (f : EulerRelations K n d) : dot y (vectorEvaluation y f) = 0 :=
  dot_evaluation_eq_zero y d f

/-- The fixed partial condition in full coordinates agrees with its reduced-coordinate form. -/
theorem full_partial_iff_reduced {n d : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (f : EulerRelations K n d) :
    vectorEvaluation (Fin.snoc y 1) f ∈ L ↔
      eulerTraceAt y d f ∈ L.map dropLast := by
  have h := mem_tangent_subspace_iff_drop (Fin.snoc y 1) (by simp) L hL
    (vectorEvaluation (Fin.snoc y 1) f) (full_euler_value_tangent _ f)
  exact h

/-- Full vanishing at a normalized point is equivalent to vanishing of its first coordinates. -/
theorem full_euler_value_zero_iff {n d : ℕ} (y : Fin n → K)
    (f : EulerRelations K n d) :
    vectorEvaluation (Fin.snoc y 1) f = 0 ↔ eulerTraceAt y d f = 0 := by
  constructor
  · intro h
    exact congrArg dropLast h
  · intro h
    have hh := tangentLift_dropLast_of_dot_eq_zero (Fin.snoc y 1)
      (vectorEvaluation (Fin.snoc y 1) f) (by simp) (full_euler_value_tangent _ f)
    change tangentLift (Fin.snoc y 1) (eulerTraceAt y d f) = _ at hh
    simpa only [h, map_zero] using hh.symm

/-- Injective evaluation identifies the trace kernel dimension with its value image. -/
theorem finrank_traceImage_of_injective {n d : ℕ}
    (B : Submodule K (Relations K (n + 1) d)) (y : Fin (n + 1) → K)
    (hB : Function.Injective ((vectorEvaluation y).comp B.subtype)) :
    finrank K (traceImage B (Fin.cons 0 y)) = finrank K B := by
  have hr : ((vectorEvaluation y).comp B.subtype).range = traceImage B (Fin.cons 0 y) := by
    ext w
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.val, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_of_inj hB

/-- The trace problem with a fixed partial condition, using full tangent coordinates. -/
def traceProblem {n p d : ℕ} (P : PointCoordinates K n p) (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K)) : Submodule K (EulerRelations K n d) :=
  (fixedPartialTraceEvaluation y (L.map dropLast) P d).ker

/-- The trace-problem kernel is exactly the full point conditions and the prescribed partial condition. -/
theorem mem_traceProblem {n p d : ℕ} (P : PointCoordinates K n p) (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) (f : EulerRelations K n d) :
    f ∈ traceProblem P y L ↔
      (∀ i, vectorEvaluation (chartPoint K P i) f = 0) ∧
      vectorEvaluation (Fin.snoc y 1) f ∈ L := by
  rw [traceProblem, mem_fixedPartialTraceEvaluation_ker]
  constructor
  · rintro ⟨hP, hy⟩
    refine ⟨fun i => ?_, (full_partial_iff_reduced y L hL f).mpr hy⟩
    apply (full_euler_value_zero_iff (fun j => P (i, j)) f).mpr
    exact funext (hP i)
  · rintro ⟨hP, hy⟩
    refine ⟨fun i j => ?_, (full_partial_iff_reduced y L hL f).mp hy⟩
    exact congrFun (hP i) j.castSucc

/-- Appending a point imposes exactly its full value on the fixed partial trace problem. -/
theorem mem_traceProblem_snoc {n p d : ℕ} (P : PointCoordinates K n p)
    (y z : Fin n → K) (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) (f : EulerRelations K n d) :
    f ∈ traceProblem (snocPoints P z) y L ↔
      f ∈ traceProblem P y L ∧ vectorEvaluation (Fin.snoc z 1) f = 0 := by
  rw [mem_traceProblem _ _ _ hL, mem_traceProblem _ _ _ hL]
  constructor
  · rintro ⟨hP, hy⟩
    refine ⟨⟨fun i => ?_, hy⟩, ?_⟩
    · simpa only [chartPoint, snocPoints_castSucc] using hP i.castSucc
    · simpa only [chartPoint, snocPoints_last] using hP (Fin.last p)
  · rintro ⟨⟨hP, hy⟩, hz⟩
    refine ⟨fun i => ?_, hy⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [chartPoint, snocPoints_last] using hz
    · simpa only [chartPoint, snocPoints_castSucc] using hP j

/-- Zero kernel after an extra point is precisely the injectivity required by Lemma 3.4. -/
theorem traceProblem_value_injective_of_snoc_finrank_zero {n p d : ℕ}
    (P : PointCoordinates K n p) (y z : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0)
    (hzero : finrank K (traceProblem (d := d) (snocPoints P z) y L) = 0) :
    Function.Injective ((vectorEvaluation (Fin.snoc z 1)).comp
      (traceProblem (d := d) P y L).subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hmem : f.val ∈ traceProblem (snocPoints P z) y L :=
    (mem_traceProblem_snoc P y z L hL f.val).mpr ⟨f.property, hf⟩
  have hbot := Submodule.finrank_eq_zero.mp hzero
  apply Subtype.ext
  change f.val = 0
  simpa only [hbot, Submodule.mem_bot] using hmem

/-- Adjacent interpolation assertions construct the initial fractional trace and an injective extra value. -/
theorem exists_initial_trace_kernel [CharZero K] {n p d : ℕ}
    (y : Fin n → K) (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1))
    (hsize : finrank K (EulerRelations K n d) ≤ n * (p + 1)) :
    ∃ P : PointCoordinates K n p,
      finrank K (eulerTraceEvaluation P d).ker =
        finrank K (EulerRelations K n d) - n * p ∧
      Function.Injective ((eulerTraceAt y d).comp (eulerTraceEvaluation P d).ker.subtype) := by
  obtain ⟨P, hP, hPy⟩ := exists_fixedPoint_euler_kernel_dimensions y hp h₀ h₁
  refine ⟨P, hP, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have hmem : f.val ∈ (eulerTraceEvaluation (snocPoints P y) d).ker := by
    rw [eulerTraceEvaluation_snoc_ker]
    exact Prod.ext f.property hf
  have hzero : (eulerTraceEvaluation (snocPoints P y) d).ker = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  apply Subtype.ext
  change f.val = 0
  simpa only [hzero, Submodule.mem_bot] using hmem

/-- The initial trace and its extra point can simultaneously satisfy scalar postulation. -/
theorem exists_initial_trace_and_scalar [CharZero K] {n p d : ℕ}
    (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1))
    (hsize : finrank K (EulerRelations K n d) ≤ n * (p + 1)) :
    ∃ (P : PointCoordinates K n p) (y : Fin n → K),
      Function.Surjective (pointEvaluation K (snocPoints P y) d) ∧
      finrank K (eulerTraceEvaluation P d).ker =
        finrank K (EulerRelations K n d) - n * p ∧
      Function.Injective ((eulerTraceAt y d).comp (eulerTraceEvaluation P d).ker.subtype) := by
  obtain ⟨D₀, hD₀, hgood₀⟩ := generic_eulerEvaluation_kernel_finrank (by omega) h₀
  obtain ⟨D₁, hD₁, hgood₁⟩ := generic_eulerEvaluation_kernel_finrank hp h₁
  obtain ⟨S, hS, hscalar⟩ := generic_pointHilbertFunction_at (K := K) n (p + 1) d
  let D₀' := rename (fun ij : Fin p × Fin n => (ij.1.castSucc, ij.2)) D₀
  have hD₀' : ∃ b : PointCoordinates K n (p + 1), eval b D₀' ≠ 0 := by
    obtain ⟨a, ha⟩ := hD₀
    refine ⟨snocPoints a (fun _ => 0), ?_⟩
    rw [eval_rename_castSucc]
    simpa only [restrict_snocPoints_castSucc] using ha
  obtain ⟨b₁, hb₁₀, hb₁₁⟩ := principal_opens_meet D₀' D₁ hD₀' hD₁
  have hproduct : ∃ b : PointCoordinates K n (p + 1), eval b (D₀' * D₁) ≠ 0 :=
    ⟨b₁, by simpa only [map_mul] using mul_ne_zero hb₁₀ hb₁₁⟩
  obtain ⟨b, hb, hbS⟩ := principal_opens_meet (D₀' * D₁) S hproduct hS
  have hparts : eval b D₀' ≠ 0 ∧ eval b D₁ ≠ 0 := by simpa only [map_mul, mul_ne_zero_iff] using hb
  let P := restrictPoints b Fin.castSucc
  let y : Fin n → K := fun j => b (Fin.last p, j)
  have hsnoc : snocPoints P y = b := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [snocPoints, y]
    · simp [snocPoints, P, restrictPoints]
  have hP : finrank K (eulerTraceEvaluation P d).ker =
      finrank K (EulerRelations K n d) - n * p := by
    rw [eulerTraceEvaluation_kernel_finrank]
    apply hgood₀ P
    simpa only [D₀', eval_rename_castSucc, P] using hparts.1
  have hbzero : (eulerTraceEvaluation b d).ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [eulerTraceEvaluation_kernel_finrank, hgood₁ b hparts.2]
    omega
  refine ⟨P, y, ?_, hP, ?_⟩
  · rw [hsnoc]
    apply pointEvaluation_surjective_of_hilbert_eq
    have hh := hscalar b hbS
    rw [← N_chart n d, min_eq_right hp] at hh
    exact hh
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hmem : f.val ∈ (eulerTraceEvaluation (snocPoints P y) d).ker := by
      rw [eulerTraceEvaluation_snoc_ker]
      exact Prod.ext f.property hf
    rw [hsnoc, hbzero] at hmem
    exact Subtype.ext hmem

/-- The lower trace and its further point meet the fixed partial, scalar-row, and nonvanishing opens. -/
theorem exists_lower_trace_choice [CharZero K] {n z p d b : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1)))
    (ystar : Fin n → K) (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hp : p + 2 ≤ N (n + 1) (d + 2))
    (h₀ : IdealGenerationAt K n (d + 2) p)
    (h₁ : IdealGenerationAt K n (d + 2) (p + 1))
    (h₂ : IdealGenerationAt K n (d + 2) (p + 2))
    (hdim : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) p = b)
    (hnext : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) (p + 1) = 0)
    (E : MvPolynomial (Fin p × Fin n) K)
    (hE : ∃ P : PointCoordinates K n p, eval P E ≠ 0) :
    ∃ (P : PointCoordinates K n p) (y : Fin n → K),
      eval P E ≠ 0 ∧
      finrank K (traceProblem (d := d + 2) P ystar Lstar) = b ∧
      Function.Injective ((vectorEvaluation (Fin.snoc y 1)).comp
        (traceProblem (d := d + 2) P ystar Lstar).subtype) ∧
      ∃ w : pointPolynomialPiece a (d + 1),
        eval (Fin.cons 0 (Fin.snoc y 1)) w.val ≠ 0 := by
  obtain ⟨D, hD, hpartial⟩ := generic_fixedPartialTrace_successive
    ystar (Lstar.map dropLast) hp h₀ h₁ h₂
  obtain ⟨F, hF, hnonzero⟩ := FractionalNonvanishing.nonvanishing_principal_open_of_multiplication
    a ha hmul hpos
  obtain ⟨P, y, hPD, hPE, hyF⟩ := FractionalTraceChoice.exists_prefix_and_point D E F hD hE hF
  have hsnoc : FractionalTraceChoice.adjoinPoint P y = snocPoints P y := rfl
  rw [hsnoc] at hPD
  have hparts := hpartial (snocPoints P y) hPD
  have hprefix : restrictPoints (snocPoints P y) Fin.castSucc = P := by
    ext ij
    simp [restrictPoints]
  rw [hprefix] at hparts
  have hdimP : finrank K (traceProblem (d := d + 2) P ystar Lstar) = b :=
    hparts.1.trans hdim
  have hzero : finrank K (traceProblem (d := d + 2) (snocPoints P y) ystar Lstar) = 0 :=
    hparts.2.trans hnext
  exact ⟨P, y, hPE, hdimP,
    traceProblem_value_injective_of_snoc_finrank_zero P ystar y Lstar hLstar hzero,
    hnonzero y hyF⟩

/-- The injective inner construction in Proposition 3.8, including selection after the whole trace. -/
theorem exists_inner_injective [CharZero K] {n z p q d b : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1)))
    (ystar : Fin n → K) (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hp : p + 2 ≤ N (n + 1) (d + 2))
    (h₀ : IdealGenerationAt K n (d + 2) p)
    (h₁ : IdealGenerationAt K n (d + 2) (p + 1))
    (h₂ : IdealGenerationAt K n (d + 2) (p + 2))
    (hdim : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) p = b)
    (hnext : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) (p + 1) = 0)
    (hbudget : (n + 1) * finrank K (pointDegreePiece K a (d + 1)) ≤ p)
    (hq : q ≤ p)
    (hrows : (n + 1) * finrank K (pointDegreePiece K a (d + 1)) - ((n + 1) - b) ≤ q) :
    ∃ (P : PointCoordinates K n p) (y : Fin n → K) (s : Finset (Fin p)) (t : K),
      s.card = q ∧ t ≠ 0 ∧ Function.Injective
        (fixedEvaluation (fun i => chartPoint K a i) (FractionalResidual.selectedPoints P s)
          (traceProblem (d := d + 2) P ystar Lstar) (Fin.cons t (Fin.snoc y 1))) := by
  have ha' : ∀ i, chartPoint K a i 0 ≠ 0 := by
    intro i
    simpa only [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
      chartPoint_castSucc] using ha i
  obtain ⟨E, hE, hinner⟩ := FractionalInner.generic_inner_injective a ha' hmul p q hbudget hq
  obtain ⟨P, y, hPE, hBdim, hB, hy⟩ := exists_lower_trace_choice a ha hmul hpos
    ystar Lstar hLstar hp h₀ h₁ h₂ hdim hnext E hE
  let B := traceProblem (d := d + 2) P ystar Lstar
  have hvalueDim : finrank K (traceImage B (Fin.cons 0 (Fin.snoc y 1))) = b := by
    rw [finrank_traceImage_of_injective B (Fin.snoc y 1) hB]
    exact hBdim
  have hspaceDim : finrank K
      (residualPartialSpace a (d + 1) (Fin.snoc y 1) (traceImage B (Fin.cons 0 (Fin.snoc y 1)))) ≤ q := by
    rw [finrank_residualPartialSpace a (Fin.snoc y 1) _ hy, hvalueDim]
    exact hrows
  obtain ⟨s, hs, t, ht, hgood⟩ := hinner P hPE B (Fin.snoc y 1) hB hy hspaceDim
  exact ⟨P, y, s, t, hs, ht, hgood⟩

/-- Expected kernel dimension on the independent side makes the fixed partial trace conditions onto. -/
theorem fixedPartialTrace_surjective_of_dimension {n p d : ℕ}
    (y : Fin n → K) (L : Submodule K (Fin n → K)) (P : PointCoordinates K n p)
    (hker : finrank K (fixedPartialTraceEvaluation y L P d).ker = fixedPartialTraceDimension L d p)
    (hbound : n * p + (n - finrank K L) ≤ finrank K (EulerRelations K n d)) :
    Function.Surjective (fixedPartialTraceEvaluation y L P d) := by
  let T := fixedPartialTraceEvaluation y L P d
  have htarget : finrank K ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L)) =
      n * p + (n - finrank K L) := by
    rw [Module.finrank_prod, L.finrank_quotient]
    simp [Module.finrank_pi_fintype, Nat.mul_comm]
  have hr := T.finrank_range_add_finrank_ker
  have hk : finrank K T.ker = finrank K (EulerRelations K n d) -
      (n * p + (n - finrank K L)) := by
    simpa only [T, fixedPartialTraceDimension, Nat.sub_sub] using hker
  rw [hk] at hr
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change finrank K T.range = finrank K ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L))
  rw [htarget]
  omega

/-- The independent inner construction uses the same whole-trace choice before selecting its scalar rows. -/
theorem exists_inner_independent [CharZero K] {n z p q d b : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, a (i, 0) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a (d + 1)))
    (haScalar : Function.Surjective (pointEvaluation K a (d + 1)))
    (hpos : 0 < finrank K (pointDegreePiece K a (d + 1)))
    (ystar : Fin n → K) (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hp : p + 2 ≤ N (n + 1) (d + 2))
    (h₀ : IdealGenerationAt K n (d + 2) p)
    (h₁ : IdealGenerationAt K n (d + 2) (p + 1))
    (h₂ : IdealGenerationAt K n (d + 2) (p + 2))
    (hdim : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) p = b)
    (hnext : fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) (p + 1) = 0)
    (htraceBound : n * p + (n - finrank K (Lstar.map dropLast)) ≤
      finrank K (EulerRelations K n (d + 2)))
    (hbudget : (n + 1) * finrank K (pointDegreePiece K a (d + 1)) ≤ p)
    (hq : q ≤ p)
    (hrows : q ≤ (n + 1) * finrank K (pointDegreePiece K a (d + 1)) - ((n + 1) - b)) :
    ∃ (P : PointCoordinates K n p) (y : Fin n → K) (s : Finset (Fin p)) (t : K),
      s.card = q ∧ t ≠ 0 ∧ Function.Surjective
        ((fixedConditionEvaluation (fun i => chartPoint K a i) (FractionalResidual.selectedPoints P s)
          (fixedPartialTraceEvaluation ystar (Lstar.map dropLast) P (d + 2))).prod
          (chartEvaluation (Fin.cons t (Fin.snoc y 1)))) := by
  have ha' : ∀ i, chartPoint K a i 0 ≠ 0 := by
    intro i
    simpa only [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
      chartPoint_castSucc] using ha i
  obtain ⟨E, hE, hinner⟩ := FractionalInner.generic_inner_independent a ha' hmul haScalar p q hbudget hq
  obtain ⟨P, y, hPE, hBdim, hB, hy⟩ := exists_lower_trace_choice a ha hmul hpos
    ystar Lstar hLstar hp h₀ h₁ h₂ hdim hnext E hE
  let T := fixedPartialTraceEvaluation ystar (Lstar.map dropLast) P (d + 2)
  have hker : finrank K T.ker = fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) p := by
    exact hBdim.trans hdim.symm
  have hT : Function.Surjective T := fixedPartialTrace_surjective_of_dimension
    ystar (Lstar.map dropLast) P hker htraceBound
  have hTon : ∀ f : T.ker, ∀ i, vectorEvaluation (chartPoint K P i) f.val = 0 := by
    intro f i
    exact ((mem_traceProblem P ystar Lstar hLstar f.val).mp f.property).1 i
  have hvalueDim : finrank K (traceImage T.ker (Fin.cons 0 (Fin.snoc y 1))) = b := by
    rw [finrank_traceImage_of_injective T.ker (Fin.snoc y 1) hB]
    exact hBdim
  have hspaceDim : q ≤ finrank K
      (residualPartialSpace a (d + 1) (Fin.snoc y 1) (traceImage T.ker (Fin.cons 0 (Fin.snoc y 1)))) := by
    rw [finrank_residualPartialSpace a (Fin.snoc y 1) _ hy, hvalueDim]
    exact hrows
  obtain ⟨s, hs, t, ht, hgood⟩ := hinner P hPE T (Fin.snoc y 1) (by simp) hT hTon hy hspaceDim
  exact ⟨P, y, s, t, hs, ht, hgood⟩

section ParameterSpace
open FractionalCompatibility

/-- Reindexing polynomial coordinates preserves polynomial dependence. -/
theorem polynomialFamily_reindex {ι κ V : Type*}
    [AddCommGroup V] [Module K V]
    (f : (ι → K) → V) (hf : IsPolynomialFamily f) (r : ι → κ) :
    IsPolynomialFamily (fun a : κ → K => f (fun i => a (r i))) := by
  intro ell
  obtain ⟨p, hp⟩ := hf ell
  refine ⟨rename r p, fun a => ?_⟩
  rw [eval_rename]
  exact hp (fun i => a (r i))

/-- The actual lower-level mixed Euler problem on the parameter space in Proposition 3.8. -/
def twoLevelEvaluation {n q z : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin n → K)) (a : JointCoordinates (K := K) n q z) (d : ℕ) :
    EulerRelations K (n + 1) d →ₗ[K]
      (Fin z → Fin (n + 1) → K) × ((Fin q → Fin n → K) × ((Fin n → K) ⧸ L)) :=
  (eulerTraceEvaluation (offCoordinates a) d).prod
    (((eulerTraceEvaluation (traceCoordinates a) d).comp (trace K (n + 1) d)).prod
      (L.mkQ.comp ((eulerTraceAt y d).comp (trace K (n + 1) d))))

/-- Every entry of the mixed problem is polynomial on the joint trace/full-point parameter space. -/
theorem twoLevelEvaluation_polynomial {n q z d : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin n → K)) :
    IsPolynomialFamily (fun a : JointCoordinates (K := K) n q z => twoLevelEvaluation y L a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have hoff := polynomialFamily_reindex (κ := JointIndex n q z)
    (fun a : PointCoordinates K (n + 1) z => eulerTraceEvaluation a d f)
    ((eulerTraceEvaluation_isPolynomialFamily (n + 1) z d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin z → Fin (n + 1) → K) f)) Sum.inr
  have htrace := polynomialFamily_reindex (κ := JointIndex n q z)
    (fun a : PointCoordinates K n q => eulerTraceEvaluation a d (trace K (n + 1) d f))
    ((eulerTraceEvaluation_isPolynomialFamily n q d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin q → Fin n → K) (trace K (n + 1) d f))) Sum.inl
  exact hoff.prod_mk (htrace.prod_mk
    (isPolynomialFamily_const (L.mkQ (eulerTraceAt y d (trace K (n + 1) d f)))))

/-- Reduced point values and full Euler values define the same vanishing conditions. -/
theorem reduced_full_conditions_iff {n p d : ℕ} (P : PointCoordinates K n p)
    (f : EulerRelations K n d) :
    eulerTraceEvaluation P d f = 0 ↔ ∀ i, vectorEvaluation (chartPoint K P i) f = 0 := by
  constructor
  · intro h i
    apply (full_euler_value_zero_iff (fun j => P (i, j)) f).mpr
    exact congrFun h i
  · intro h
    ext i j
    exact congrFun (h i) j.castSucc

/-- The joint-coordinate map has exactly the full-point and partial trace kernel. -/
theorem twoLevelEvaluation_kernel {n q z d : ℕ} (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (a : JointCoordinates (K := K) n q z) :
    (twoLevelEvaluation y (L.map dropLast) a (d + 1)).ker =
      fixedSpace (fun i => chartPoint K (offCoordinates a) i) FractionalRegroup.noPoints
        (traceProblem (d := d + 1) (traceCoordinates a) y L) := by
  ext f
  change (eulerTraceEvaluation (offCoordinates a) (d + 1) f,
      fixedPartialTraceEvaluation y (L.map dropLast) (traceCoordinates a) (d + 1)
        (trace K (n + 1) (d + 1) f)) = 0 ↔ _
  rw [Prod.mk_eq_zero, reduced_full_conditions_iff]
  constructor
  · rintro ⟨hoff, htrace⟩
    exact ⟨htrace, hoff, fun i => i.elim⟩
  · rintro ⟨htrace, hoff, _⟩
    exact ⟨hoff, htrace⟩

/-- The fixed partial space, followed by point traces, is the same trace problem. -/
theorem traceProblem_eq_tracePointSpace {n p d : ℕ}
    (P : PointCoordinates K n p) (y : Fin n → K)
    (L : Submodule K (Fin (n + 1) → K))
    (hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0) :
    traceProblem (d := d) P y L =
      FractionalRegroup.tracePointSpace
        (((L.map dropLast).mkQ).comp (eulerTraceAt y d)).ker P Finset.univ := by
  ext f
  rw [mem_traceProblem P y L hL]
  change ((∀ i, vectorEvaluation (chartPoint K P i) f = 0) ∧
      vectorEvaluation (Fin.snoc y 1) f ∈ L) ↔
    (((L.map dropLast).mkQ (eulerTraceAt y d f) = 0) ∧
      ∀ i ∈ Finset.univ, vectorEvaluation (chartPoint K P i) f = 0)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← full_partial_iff_reduced y L hL f]
  simp only [Finset.mem_univ, forall_true_left]
  exact and_comm

/-- The selected points and moving point give an ordinary joint-coordinate configuration. -/
def regroupedJoint {n p z : ℕ} (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y : Fin n → K) :
    JointCoordinates (K := K) n (p - s.card) (z + s.card + 1) :=
  Sum.elim (FractionalRegroupCoordinates.complementCoordinates P s)
    (FractionalRegroupCoordinates.fullCoordinates a P s t y)

/-- The two-level kernel agrees exactly with the inner fixed kernel plus its moving point. -/
theorem regroupedJoint_kernel {n p z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (t : K) (y ystar : Fin n → K)
    (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0) :
    (twoLevelEvaluation ystar (Lstar.map dropLast) (regroupedJoint a P s t y) (d + 1)).ker =
      fixedSpace (fun i => chartPoint K a i) (FractionalResidual.selectedPoints P s)
          (traceProblem (d := d + 1) P ystar Lstar) ⊓
        (vectorEvaluation (Fin.cons t (Fin.snoc y 1))).ker := by
  rw [twoLevelEvaluation_kernel ystar Lstar]
  change fixedSpace (fun i => chartPoint K (FractionalRegroupCoordinates.fullCoordinates a P s t y) i)
      FractionalRegroup.noPoints
      (traceProblem (d := d + 1) (FractionalRegroupCoordinates.complementCoordinates P s) ystar Lstar) = _
  rw [traceProblem_eq_tracePointSpace _ ystar Lstar hLstar,
    FractionalRegroupCoordinates.normalized_regrouped_space_eq,
    ← traceProblem_eq_tracePointSpace P ystar Lstar hLstar]
  rfl

/-- Injectivity on a fixed-condition space says exactly that the joint vanishing kernel is zero. -/
theorem fixedEvaluation_injective_iff {n d : ℕ} {O H : Type*}
    (off : O → Fin (n + 1) → K) (on : H → Fin (n + 1) → K)
    (B : Submodule K (Relations K n (d + 1))) (y : Fin (n + 1) → K) :
    Function.Injective (fixedEvaluation off on B y) ↔
      fixedSpace off on B ⊓ (vectorEvaluation y).ker = ⊥ := by
  constructor
  · intro hinj
    apply le_antisymm ?_ bot_le
    rintro f ⟨hfixed, heval⟩
    have hEval0 : fixedEvaluation off on B y (⟨f, hfixed⟩ : fixedSpace off on B) =
        fixedEvaluation off on B y 0 := by
      rw [map_zero]
      change vectorEvaluation y f = 0
      exact heval
    have hz : (⟨f, hfixed⟩ : fixedSpace off on B) = 0 := hinj hEval0
    change f = 0
    exact congrArg Subtype.val hz
  · intro hzero
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    apply Subtype.ext
    change f.val = 0
    change vectorEvaluation y f.val = 0 at hf
    have hmem : f.val ∈ fixedSpace off on B ⊓ (vectorEvaluation y).ker := ⟨f.property, hf⟩
    simpa only [hzero, Submodule.mem_bot] using hmem

/-- The inner injective move is an injective witness for the actual joint parameter family. -/
theorem regroupedJoint_injective {n p z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (P : PointCoordinates K n p)
    (s : Finset (Fin p)) (t : K) (y ystar : Fin n → K)
    (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hmove : Function.Injective (fixedEvaluation (fun i => chartPoint K a i)
      (FractionalResidual.selectedPoints P s) (traceProblem (d := d + 1) P ystar Lstar)
      (Fin.cons t (Fin.snoc y 1)))) :
    Function.Injective (twoLevelEvaluation ystar (Lstar.map dropLast)
      (regroupedJoint a P s t y) (d + 1)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [regroupedJoint_kernel a P s t y ystar Lstar hLstar]
  exact (fixedEvaluation_injective_iff _ _ _ _).mp hmove

/-- Regrouping preserves independence because the two actual condition spaces have equal dimension. -/
theorem regroupedJoint_surjective {n p z d : ℕ}
    (a : PointCoordinates K (n + 1) z) (ha : ∀ i, chartPoint K a i 0 ≠ 0)
    (P : PointCoordinates K n p) (s : Finset (Fin p)) (t : K) (y ystar : Fin n → K)
    (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hmove : Function.Surjective
      ((fixedConditionEvaluation (fun i => chartPoint K a i) (FractionalResidual.selectedPoints P s)
        (fixedPartialTraceEvaluation ystar (Lstar.map dropLast) P (d + 1))).prod
        (chartEvaluation (Fin.cons t (Fin.snoc y 1))))) :
    Function.Surjective (twoLevelEvaluation ystar (Lstar.map dropLast)
      (regroupedJoint a P s t y) (d + 1)) := by
  let T := fixedPartialTraceEvaluation ystar (Lstar.map dropLast) P (d + 1)
  let moved : Fin (n + 2) → K := Fin.cons t (Fin.snoc y 1)
  let A := (fixedConditionEvaluation (fun i => chartPoint K a i)
    (FractionalResidual.selectedPoints P s) T).prod (chartEvaluation moved)
  let F := twoLevelEvaluation ystar (Lstar.map dropLast) (regroupedJoint a P s t y) (d + 1)
  have hTon (b : T.ker) (i : s) :
      vectorEvaluation (fun j => FractionalResidual.selectedPoints P s i j.succ) b.val = 0 := by
    have hb := ((mem_traceProblem P ystar Lstar hLstar b.val).mp b.property).1 i.val
    exact hb
  have hchart : (chartEvaluation (d := d + 1) moved).ker = (vectorEvaluation moved).ker := by
    ext f
    exact chartEvaluation_eq_zero_iff moved (by simp [moved]) f
  have hker : A.ker = F.ker := by
    unfold A F
    rw [LinearMap.ker_prod, hchart, fixedConditionEvaluation_ker _ _ T ha (fun _ => rfl) hTon,
      regroupedJoint_kernel a P s t y ystar Lstar hLstar]
    rfl
  apply (surjective_iff_of_kernel_eq A F hker ?_).mp hmove
  have hs : s.card ≤ p := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  have hsplit : n * (p - s.card) + n * s.card = n * p := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hs]
  simp [Module.finrank_pi_fintype]
  ring_nf at hsplit ⊢
  omega

/-- A lower-level injective witness can be chosen simultaneously with the scalar completion. -/
theorem compatible_twoLevel_injective [Infinite K] {n p q z d : ℕ}
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed (d + 1)))
    (hcount : p + q = (n + (d + 1)).choose (d + 1))
    (a₀ : JointCoordinates (K := K) n q z)
    (ha₀ : Function.Injective (twoLevelEvaluation y L a₀ d)) :
    ∃ a : JointCoordinates (K := K) n q z,
      Function.Injective (twoLevelEvaluation y L a d) ∧
      Function.Bijective (pointEvaluation K (appendCoordinates fixed (traceCoordinates a)) (d + 1)) ∧
      (∀ i, offCoordinates a (i, 0) ≠ 0) := by
  obtain ⟨P, hP, hgood⟩ := injective_polynomial_principal_open
    (fun a => twoLevelEvaluation y L a d) (twoLevelEvaluation_polynomial y L) a₀ ha₀
  obtain ⟨a, ha, hscalar, hoff⟩ := compatible_scalar_completion_appended
    fixed hfixed hcount P ⟨a₀, hP⟩
  exact ⟨a, hgood a ha, hscalar, hoff⟩

/-- A lower-level independent witness has the same compatibility with scalar completion. -/
theorem compatible_twoLevel_surjective [Infinite K] {n p q z d : ℕ}
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (fixed : PointCoordinates K n p)
    (hfixed : Function.Surjective (pointEvaluation K fixed (d + 1)))
    (hcount : p + q = (n + (d + 1)).choose (d + 1))
    (a₀ : JointCoordinates (K := K) n q z)
    (ha₀ : Function.Surjective (twoLevelEvaluation y L a₀ d)) :
    ∃ a : JointCoordinates (K := K) n q z,
      Function.Surjective (twoLevelEvaluation y L a d) ∧
      Function.Bijective (pointEvaluation K (appendCoordinates fixed (traceCoordinates a)) (d + 1)) ∧
      (∀ i, offCoordinates a (i, 0) ≠ 0) := by
  obtain ⟨P, hP, hgood⟩ := rank_polynomial_principal_open
    (fun a => twoLevelEvaluation y L a d) (twoLevelEvaluation_polynomial y L) a₀
  have honto (a : JointCoordinates (K := K) n q z) (ha : eval a P ≠ 0) :
      Function.Surjective (twoLevelEvaluation y L a d) := by
    have h := hgood a ha
    rw [LinearMap.range_eq_top.mpr ha₀, finrank_top] at h
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) h))
  obtain ⟨a, ha, hscalar, hoff⟩ := compatible_scalar_completion_appended
    fixed hfixed hcount P ⟨a₀, hP⟩
  exact ⟨a, honto a ha, hscalar, hoff⟩

/-- The constructed inner injective move and scalar completion occur on one actual parameter space. -/
theorem compatible_inner_injective [Infinite K] {n a p q z d : ℕ}
    (ystar : Fin n → K) (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (off : PointCoordinates K (n + 1) z)
    (fixed : PointCoordinates K n a)
    (hfixed : Function.Surjective (pointEvaluation K fixed (d + 2)))
    (hcount : a + (p - q) = (n + (d + 2)).choose (d + 2))
    (hinner : ∃ (P : PointCoordinates K n p) (y : Fin n → K)
        (s : Finset (Fin p)) (t : K), s.card = q ∧ t ≠ 0 ∧
      Function.Injective (fixedEvaluation (fun i => chartPoint K off i)
        (FractionalResidual.selectedPoints P s) (traceProblem (d := d + 1) P ystar Lstar)
        (Fin.cons t (Fin.snoc y 1)))) :
    ∃ b : JointCoordinates (K := K) n (p - q) (z + q + 1),
      Function.Injective (twoLevelEvaluation ystar (Lstar.map dropLast) b (d + 1)) ∧
      Function.Bijective (pointEvaluation K (appendCoordinates fixed (traceCoordinates b)) (d + 2)) ∧
      (∀ i, offCoordinates b (i, 0) ≠ 0) := by
  obtain ⟨P, y, s, t, hs, _ht, hmove⟩ := hinner
  subst q
  exact compatible_twoLevel_injective ystar (Lstar.map dropLast) fixed hfixed hcount
    (regroupedJoint off P s t y) (regroupedJoint_injective off P s t y ystar Lstar hLstar hmove)

/-- The inner independent move has the same simultaneous scalar-completion property. -/
theorem compatible_inner_independent [Infinite K] {n a p q z d : ℕ}
    (ystar : Fin n → K) (Lstar : Submodule K (Fin (n + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (off : PointCoordinates K (n + 1) z) (hoff : ∀ i, chartPoint K off i 0 ≠ 0)
    (fixed : PointCoordinates K n a)
    (hfixed : Function.Surjective (pointEvaluation K fixed (d + 2)))
    (hcount : a + (p - q) = (n + (d + 2)).choose (d + 2))
    (hinner : ∃ (P : PointCoordinates K n p) (y : Fin n → K)
        (s : Finset (Fin p)) (t : K), s.card = q ∧ t ≠ 0 ∧
      Function.Surjective ((fixedConditionEvaluation (fun i => chartPoint K off i)
        (FractionalResidual.selectedPoints P s)
        (fixedPartialTraceEvaluation ystar (Lstar.map dropLast) P (d + 1))).prod
        (chartEvaluation (Fin.cons t (Fin.snoc y 1))))) :
    ∃ b : JointCoordinates (K := K) n (p - q) (z + q + 1),
      Function.Surjective (twoLevelEvaluation ystar (Lstar.map dropLast) b (d + 1)) ∧
      Function.Bijective (pointEvaluation K (appendCoordinates fixed (traceCoordinates b)) (d + 2)) ∧
      (∀ i, offCoordinates b (i, 0) ≠ 0) := by
  obtain ⟨P, y, s, t, hs, _ht, hmove⟩ := hinner
  subst q
  exact compatible_twoLevel_surjective ystar (Lstar.map dropLast) fixed hfixed hcount
    (regroupedJoint off P s t y) (regroupedJoint_surjective off hoff P s t y ystar Lstar hLstar hmove)

end ParameterSpace

end IdealGeneration.FractionalHyperplane
