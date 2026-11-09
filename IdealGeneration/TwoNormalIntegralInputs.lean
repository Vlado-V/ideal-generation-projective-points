module

public import IdealGeneration.TwoNormalMarkedOpen
public import IdealGeneration.TwoNormalAttachedInterpolation
public import IdealGeneration.TwoNormalWitness
public import IdealGeneration.TwoNormalSliceCokernel
public import IdealGeneration.PointDimensions
public import IdealGeneration.IntegralTraceNumerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Generic lower-degree inputs to the integral marked construction

The slice, trace, and off-slice conditions are witnessed independently.
All dimensions are those of the actual point ideals and Euler fibers.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoNormalTrace AttachedTrace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n b p q d : ℕ}

/-- Full scalar Hilbert rank on the source side gives injective evaluation. -/
theorem pointEvaluation_injective_of_fullHilbert (a : PointCoordinates K n p)
    (d : ℕ) (hp : N (n + 1) d ≤ p)
    (hpost : pointHilbertFunction K a d = min (N (n + 1) d) p) :
    Function.Injective (pointEvaluation K a d) := by
  have h := (pointEvaluation K a d).finrank_range_add_finrank_ker
  rw [← pointHilbertFunction_eq_rank, hpost, min_eq_left hp, finrank_chart_forms,
    ← N_chart n d] at h
  have hz : finrank K (pointEvaluation K a d).ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

/-- Transpose the coordinate-first presentation of the Euler fiber array. -/
def pointEulerFiberTranspose (a : PointCoordinates K n p) :
    (fiberMultiplication a).ker ≃ₗ[K] TraceFibers (chartPoint K a) where
  toFun f := ⟨fun i j => f.val j i, f.property⟩
  invFun f := ⟨fun j i => f.val i j, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two actual fiber evaluation conventions agree by transposition. -/
theorem traceFiberEvaluation_eq_pointEuler (a : PointCoordinates K n p) (d : ℕ) :
    traceFiberEvaluation (chartPoint K a) d =
      (pointEulerFiberTranspose a).toLinearMap.comp (pointEulerSquare a d).leftOnKernel := rfl

/-- The slice conditions imposed on its own general points. -/
structure IntegralSliceGood (a : PointCoordinates K (n + 1) b) (d : ℕ) : Prop where
  normal : ∀ i, chartPoint K a i (0 : Fin (n + 2)) ≠ 0
  multiplication : Function.Injective (pointMultiplication a (d + 1))
  scalar : Function.Surjective (pointEvaluation K a (d + 1))
  lowerScalar : Function.Injective (pointEvaluation K a d)
  projectedScalar : Function.Surjective (projectedEvaluation a (d + 1))
  dimension : finrank K (pointDegreePiece K a (d + 1)) = N (n + 2) (d + 1) - b

/-- Lower-degree ideal generation and the slice count bounds give a nonempty
open of all conditions on one slice. -/
theorem generic_integralSliceGood [CharZero K]
    (hn : 1 ≤ n) (d b : ℕ)
    (hR : N (n + 2) d ≤ b) (hL : b ≤ N (n + 2) (d + 1))
    (hM : b ≤ N (n + 1) (d + 1))
    (hcritical : ((N (n + 2) (d + 1) - b : ℕ) : ℚ) ≤ E (n + 2) (d + 1))
    (hG : IdealGenerationAt K (n + 1) (d + 1) b) :
    ∃ P : MvPolynomial (Fin b × Fin (n + 1)) K,
      (∃ a : PointCoordinates K (n + 1) b, eval a P ≠ 0) ∧
      ∀ a, eval a P ≠ 0 → IntegralSliceGood a d := by
  obtain ⟨D, hD, hgood⟩ := idealGenerationAt_injective_open (by omega : 1 ≤ n + 1)
    hL hcritical hG
  obtain ⟨P, hP, hproj⟩ := generic_pointHilbertFunction (K := K) hn b
  let j : (Fin b × Fin n) ↪ (Fin b × Fin (n + 1)) :=
    Function.Embedding.prodMap (Function.Embedding.refl _) (Fin.succEmb n)
  obtain ⟨hP', hgoodP⟩ := principalOpen_pullback j P hP
  let H := offHyperplanePolynomial (K := K) n b
  have hH : ∃ a : PointCoordinates K (n + 1) b, eval a H ≠ 0 := by
    refine ⟨fun _ => 1, ?_⟩
    simp [H, offHyperplanePolynomial]
  obtain ⟨a₁, haD, haP⟩ := principal_opens_meet D (rename j P) hD hP'
  have hDP : ∃ a : PointCoordinates K (n + 1) b, eval a (D * rename j P) ≠ 0 :=
    ⟨a₁, by simpa only [map_mul] using mul_ne_zero haD haP⟩
  obtain ⟨a₀, ha₀, haH⟩ := principal_opens_meet (D * rename j P) H hDP hH
  refine ⟨D * rename j P * H, ⟨a₀, by simpa only [map_mul] using mul_ne_zero ha₀ haH⟩, ?_⟩
  intro a ha
  have hparts : (eval a D ≠ 0 ∧ eval a (rename j P) ≠ 0) ∧ eval a H ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using ha
  obtain ⟨_, hpost, hmul⟩ := hgood a hparts.1.1
  have hpost' (e : ℕ) : pointHilbertFunction K a e = min (N (n + 2) e) b := by
    simpa only [N_chart (n + 1) e] using hpost e
  refine ⟨?_, hmul, ?_, pointEvaluation_injective_of_fullHilbert a d hR (hpost' d), ?_,
    pointDegreePiece_finrank a (hpost' (d + 1))⟩
  · have hnz := (eval_offHyperplanePolynomial_ne_zero_iff a).mp hparts.2
    intro i
    change chartPoint K a i (0 : Fin (n + 1)).castSucc ≠ 0
    simpa only [chartPoint_castSucc] using hnz i
  · apply pointEvaluation_surjective_of_hilbert_eq a
    rw [hpost', min_eq_right hL]
  · rw [projectedEvaluation_eq]
    apply pointEvaluation_surjective_of_hilbert_eq (projectedCoordinates a)
    have hpa : eval (projectedCoordinates a) P ≠ 0 := hgoodP a hparts.1.2
    have ht := (hproj (projectedCoordinates a) hpa).2 (d + 1)
    simpa only [← N_chart n (d + 1), min_eq_right hM] using ht

/-- The square integral trace and its two scalar evaluation conditions. -/
structure IntegralTraceGood (z : PointCoordinates K n p) (d : ℕ) : Prop where
  euler : Function.Bijective (traceFiberEvaluation (chartPoint K z) (d + 1 + 1))
  scalar : Function.Surjective (pointEvaluation K z (d + 1 + 1))
  lowerScalar : Function.Injective (pointEvaluation K z (d + 1))

/-- The integral critical trace count gives the square Euler isomorphism on
a nonempty principal open, together with scalar interpolation. -/
theorem generic_integralTraceGood [CharZero K]
    (hn : 1 ≤ n) (d p r₂ : ℕ)
    (htrace : E (n + 1) (d + 1 + 1) = (r₂ : ℚ))
    (hcount : p = N (n + 1) (d + 1 + 1) - r₂)
    (hlower : N (n + 1) (d + 1) ≤ p)
    (hG : IdealGenerationAt K n (d + 1 + 1) p) :
    ∃ P : MvPolynomial (Fin p × Fin n) K,
      (∃ z : PointCoordinates K n p, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → IntegralTraceGood z d := by
  let D := d + 1 + 1
  have htrace' : E (n + 2 - 1) D = (r₂ : ℚ) := by simpa [D] using htrace
  have hr₂ : r₂ ≤ N (n + 1) D := by
    have hc := (integral_trace_mem_cell (n + 2) D r₂ (by omega) (by dsimp [D]; omega) htrace').2
    have hc' : r₂ ≤ N (n + 1) D - N (n + 1) (D - 1) := by simpa using hc
    omega
  have hp : p ≤ N (n + 1) D := by rw [hcount]; exact Nat.sub_le _ _
  have hcrit : ((N (n + 1) D - p : ℕ) : ℚ) = E (n + 1) D := by
    rw [hcount, Nat.sub_sub_self hr₂]
    exact htrace.symm
  obtain ⟨P, hP, hgood⟩ := hG
  refine ⟨P, hP, fun z hz => ?_⟩
  obtain ⟨_, hpost, hmax⟩ := hgood z hz
  have hpost' (e : ℕ) : pointHilbertFunction K z e = min (N (n + 1) e) p := by
    simpa only [N_chart n e] using hpost e
  have hscalar : Function.Surjective (pointEvaluation K z D) := by
    apply pointEvaluation_surjective_of_hilbert_eq z
    rw [hpost', min_eq_right hp]
  have hMulI := pointMultiplication_injective_below_critical hn z hp (hpost' D)
    (hpost' (D + 1)) hmax (le_of_eq hcrit)
  have hMulS := pointMultiplication_surjective_above_critical hn z hp (hpost' D)
    (hpost' (D + 1)) hmax (le_of_eq hcrit.symm)
  have hEulerI : Function.Injective (pointEulerSquare z D).leftOnKernel :=
    (pointEulerSquare z D).injective_iff.mp ((pointMultiplication_injective_iff z D).mp hMulI)
  have hEulerS : Function.Surjective (pointEulerSquare z D).leftOnKernel :=
    ((pointEulerSquare z D).surjective_iff (formMultiplication_surjective (n + 1) D)
      (componentEvaluation_surjective z hscalar)).mp
        ((pointMultiplication_surjective_iff z D).mp hMulS)
  have heval : Function.Bijective (traceFiberEvaluation (chartPoint K z) D) := by
    rw [traceFiberEvaluation_eq_pointEuler]
    exact (pointEulerFiberTranspose z).bijective.comp ⟨hEulerI, hEulerS⟩
  exact ⟨heval, hscalar, pointEvaluation_injective_of_fullHilbert z (d + 1) hlower (hpost' _)⟩

/-- The off-slice ideal data in the two residual degrees. -/
structure IntegralOffSliceGood (x : PointCoordinates K (n + 2) q) (d g : ℕ) : Prop where
  sNonzero : ∀ i, chartPoint K x i (0 : Fin (n + 3)) ≠ 0
  tNonzero : ∀ i, chartPoint K x i (0 : Fin (n + 2)).succ ≠ 0
  scalar : Function.Surjective (pointEvaluation K x d)
  dimension : finrank K (pointDegreePiece K x d) = g
  nextDimension : finrank K (pointDegreePiece K x (d + 1)) = N (n + 3) (d + 1) - q
  trace : Function.Injective ((restrictTraceForm K (n + 1) d).comp (pointDegreePiece K x d).subtype)
  product : Function.Injective (traceProduct K (n + 1) d (pointDegreePiece K x d))

/-- The lower-dimensional degree-`d` injection supplies the genuine
restricted off-slice point ideal and its two scalar dimensions. -/
theorem generic_integralOffSliceGood [CharZero K]
    (hn : 1 ≤ n) (d q g : ℕ)
    (hg : g ≤ N (n + 1) d) (hcount : q + g = N (n + 3) d)
    (hcritical : (g : ℚ) ≤ E (n + 1) d)
    (hG : IdealGenerationAt K n d (N (n + 1) d - g)) :
    ∃ P : MvPolynomial (Fin q × Fin (n + 2)) K,
      (∃ x : PointCoordinates K (n + 2) q, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → IntegralOffSliceGood x d g := by
  let r := N (n + 1) d - g
  have hr : r ≤ N (n + 1) d := Nat.sub_le _ _
  have hcritical' : ((N (n + 1) d - r : ℕ) : ℚ) ≤ E (n + 1) d := by
    rw [show r = N (n + 1) d - g from rfl, Nat.sub_sub_self hg]
    exact hcritical
  obtain ⟨D, ⟨a, ha⟩, hgood⟩ := idealGenerationAt_injective_open hn hr hcritical' hG
  obtain ⟨_, hpost, hmul⟩ := hgood a ha
  have hpostd : pointHilbertFunction K a d = min (N (n + 1) d) r := by
    simpa only [N_chart n d] using hpost d
  have hscalar : Function.Surjective (pointEvaluation K a d) := by
    apply pointEvaluation_surjective_of_hilbert_eq a
    rwa [min_eq_right hr] at hpostd
  have hdimA : finrank K (pointDegreePiece K a d) = g := by
    rw [pointDegreePiece_finrank a hpostd, show r = N (n + 1) d - g from rfl,
      Nat.sub_sub_self hg]
  have hsize : finrank K (restrictTraceForm K (n + 1) d).ker + r = q := by
    rw [traceKernel_finrank, finrank_forms, finrank_forms]
    change (N (n + 3) d - N (n + 1) d) + (N (n + 1) d - g) = q
    have hm : N (n + 1) d ≤ N (n + 3) d := N_mono_variables d (by omega)
    omega
  have hgoodX := generic_twoNormal_point_ideal K n a hmul hscalar
  rw [hsize] at hgoodX
  obtain ⟨P, hP, hPgood⟩ := hgoodX
  obtain ⟨Q, hQ, hQgood⟩ := generic_pointHilbertFunction (K := K) (by omega : 1 ≤ n + 2) q
  obtain ⟨x₀, hxP, hxQ⟩ := principal_opens_meet P Q hP hQ
  refine ⟨P * Q, ⟨x₀, by simpa only [map_mul] using mul_ne_zero hxP hxQ⟩, ?_⟩
  intro x hx
  have hparts : eval x P ≠ 0 ∧ eval x Q ≠ 0 := by simpa using hx
  obtain ⟨_, hs, ht, hdim, hR, hT⟩ := hPgood x hparts.1
  obtain ⟨_, hpostX⟩ := hQgood x hparts.2
  have hq : q ≤ N (n + 3) d := by omega
  have hpostX' (e : ℕ) : pointHilbertFunction K x e = min (N (n + 3) e) q := by
    simpa only [N_chart (n + 2) e] using hpostX e
  refine ⟨hs, ht, ?_, hdim.trans hdimA, pointDegreePiece_finrank x (hpostX' (d + 1)), hR, hT⟩
  apply pointEvaluation_surjective_of_hilbert_eq x
  rw [hpostX', min_eq_right hq]

end IdealGeneration.TwoNormalIntegral
