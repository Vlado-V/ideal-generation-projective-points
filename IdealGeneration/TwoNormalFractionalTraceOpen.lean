module

public import IdealGeneration.TwoNormalFractionalMarkedParameters
public import IdealGeneration.TwoNormalSliceCokernel
public import IdealGeneration.PointDimensions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Joint rank open for the trace and its free projection -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalSlice TwoNormalIntegral
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p D : ℕ}

/-- Surjectivity of multiplication and scalar postulation give surjectivity
in the actual normalized trace fibers. -/
theorem traceFiberEvaluation_surjective_of_pointMultiplication [CharZero K]
    (a : PointCoordinates K n p)
    (hs : Function.Surjective (pointEvaluation K a D))
    (h : Function.Surjective (pointMultiplication a D)) :
    Function.Surjective (traceFiberEvaluation (chartPoint K a) D) := by
  have h' : Function.Surjective (pointEulerSquare a D).leftOnKernel :=
    (pointEulerSquare a D).surjective_iff (formMultiplication_surjective (n + 1) D)
      (componentEvaluation_surjective a hs) |>.mp ((pointMultiplication_surjective_iff a D).mp h)
  intro y
  let Y : (fiberMultiplication a).ker :=
    ⟨fun j i => y.val i j, y.property⟩
  obtain ⟨F, hF⟩ := h' Y
  refine ⟨F, Subtype.ext ?_⟩
  funext i j
  exact congrFun (congrFun (congrArg Subtype.val hF) j) i

/-- Injectivity of multiplication gives injectivity of full trace component evaluation. -/
theorem traceRelationEvaluation_injective_of_pointMultiplication
    (a : PointCoordinates K n p)
    (h : Function.Injective (pointMultiplication a D)) :
    Function.Injective (relationEvaluation (chartPoint K a) D) := by
  have he : Function.Injective (pointEulerSquare a D).leftOnKernel :=
    (pointEulerSquare a D).injective_iff.mp ((pointMultiplication_injective_iff a D).mp h)
  intro F G hFG
  apply he
  apply Subtype.ext
  funext j i
  exact congrFun (congrFun hFG i) j

variable {b q l : ℕ}

/-- The ordinary trace array, selected from the fractional marked parameters. -/
abbrev fractionalTraceCoordinates (c : FractionalParameters K n b q l) :=
  markedTraceCoordinates (c ∘ Sum.inl)

/-- The trace, its free augmentation, and the scalar ranks are simultaneously
available on one nonempty principal open of the marked parameters. -/
theorem fractional_trace_open [CharZero K]
    (hn : 1 ≤ n)
    (hp : b + (b + (q + l)) + 1 ≤ N (n + 1) D)
    (hprev : N (n + 1) (D - 1) ≤ b + (b + (q + l)))
    (hcritS : E (n + 1) D ≤ ((N (n + 1) D - (b + (b + (q + l))) : ℕ) : ℚ))
    (hcritI : ((N (n + 1) D - (b + (b + (q + l)) + 1) : ℕ) : ℚ) ≤ E (n + 1) D)
    (hS : IdealGenerationAt K n D (b + (b + (q + l))))
    (hI : IdealGenerationAt K n D (b + (b + (q + l)) + 1)) :
    ∃ P : MvPolynomial (FractionalIndex n b q l) K,
      (∃ c : FractionalParameters K n b q l, eval c P ≠ 0) ∧
      ∀ c, eval c P ≠ 0 →
        Function.Surjective (traceFiberEvaluation (chartPoint K (fractionalTraceCoordinates c)) D) ∧
        Function.Injective (relationEvaluation
          (chartPoint K (fractionalAugmentedTraceCoordinates c)) D) ∧
        Function.Surjective (pointEvaluation K (fractionalTraceCoordinates c) D) ∧
        Function.Injective (scalarEvaluation (chartPoint K (fractionalTraceCoordinates c)) (D - 1)) := by
  have hp' : b + (b + (q + l)) ≤ N (n + 1) D := by omega
  obtain ⟨S, hS₀, hSgood⟩ := idealGenerationAt_surjective_open hn hp' hcritS hS
  obtain ⟨I, hI₀, hIgood⟩ := idealGenerationAt_injective_open hn hp hcritI hI
  let eS := (markedTraceIndex n b q l).trans
    (Function.Embedding.inl : MarkedIndex n b q l ↪ FractionalIndex n b q l)
  let eI := fractionalAugmentedTraceIndex n b q l
  obtain ⟨hS₁, hSpull⟩ := principalOpen_pullback eS S hS₀
  obtain ⟨hI₁, hIpull⟩ := principalOpen_pullback eI I hI₀
  obtain ⟨c₀, hcS, hcI⟩ := principal_opens_meet (rename eS S) (rename eI I) hS₁ hI₁
  refine ⟨rename eS S * rename eI I, ⟨c₀, by simpa using mul_ne_zero hcS hcI⟩, ?_⟩
  intro c hc
  have hparts : eval c (rename eS S) ≠ 0 ∧ eval c (rename eI I) ≠ 0 := by simpa using hc
  obtain ⟨_, hpost, hmult⟩ := hSgood (fractionalTraceCoordinates c) (hSpull c hparts.1)
  have hscalar : Function.Surjective (pointEvaluation K (fractionalTraceCoordinates c) D) := by
    apply pointEvaluation_surjective_of_hilbert_eq
    simpa only [← N_chart n D, min_eq_right hp'] using hpost D
  have hscalarPrev : Function.Injective
      (pointEvaluation K (fractionalTraceCoordinates c) (D - 1)) := by
    have hdim : pointHilbertFunction K (fractionalTraceCoordinates c) (D - 1) =
        N (n + 1) (D - 1) := by
      simpa only [← N_chart n (D - 1), min_eq_left hprev] using hpost (D - 1)
    have hr : finrank K (pointEvaluation K (fractionalTraceCoordinates c) (D - 1)).range =
        finrank K (Forms K (n + 1) (D - 1)) := by
      rw [← pointHilbertFunction_eq_rank, hdim, finrank_chart_forms, ← N_chart]
    have hnull := (pointEvaluation K (fractionalTraceCoordinates c) (D - 1)).finrank_range_add_finrank_ker
    have hz : finrank K (pointEvaluation K (fractionalTraceCoordinates c) (D - 1)).ker = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
  exact ⟨traceFiberEvaluation_surjective_of_pointMultiplication _ hscalar hmult,
    traceRelationEvaluation_injective_of_pointMultiplication _
      (hIgood (fractionalAugmentedTraceCoordinates c) (hIpull c hparts.2)).2.2,
    hscalar, hscalarPrev⟩

end IdealGeneration.TwoNormalFractional
