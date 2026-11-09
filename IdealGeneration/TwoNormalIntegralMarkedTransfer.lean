module

public import IdealGeneration.TwoNormalIntegralAssembly

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Maximal Euler rank at a good integral marked configuration

The two-group interpolation count is transferred to the actual ambient
Euler kernel. If its rank is not already maximal, the ambient cokernel is
identified with both trace-product quotient codes, and the normal motion
has maximal rank on a nonempty principal open.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module MvPolynomial TwoNormalSlice TwoNormalTrace TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem span_rows_precomp_equiv {K V U ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (e : V ≃ₗ[K] U) (α : ι → Module.Dual K U)
    (hα : Submodule.span K (Set.range α) = ⊤) :
    Submodule.span K (Set.range (fun i => (α i).comp e.toLinearMap)) = ⊤ := by
  apply scalarRows_span_of_injective
  exact (scalarEvaluation_injective_of_span α hα).comp e.injective

variable {K : Type*} [Field K] {m b q p d : ℕ}

/-- The trace-product quotient coordinate of a trace point. -/
def traceProductCoordinate (a : PointCoordinates K m b)
    (z : Fin p → Fin m → K) (e : ℕ) (i : Fin p) : TraceProductQuotient a z e :=
  (traceProductCodeMap a z e).range.mkQ (Pi.single i 1)

/-- The geometric data at a marked configuration give either maximal rank
there or a genuine polynomial motion that attains maximal rank. -/
theorem integral_marked_fiber_transfer
    (a b' : PointCoordinates K m b) (x : PointCoordinates K (m + 1) q)
    (z : Fin p → Fin m → K)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (htrace : Function.Bijective (traceFiberEvaluation z (d + 1 + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a (d + 1)))
    (hscalarB : Function.Surjective (pointEvaluation K b' (d + 1)))
    (hmulA : Function.Injective (pointMultiplication a (d + 1)))
    (hmulB : Function.Injective (pointMultiplication b' (d + 1)))
    (hevalA : Function.Injective ((scalarEvaluation z (d + 1 + 1)).comp
      (tangentPointProductForm a (d + 1)).range.subtype))
    (hevalB : Function.Injective ((scalarEvaluation z (d + 1 + 1)).comp
      (tangentPointProductForm b' (d + 1)).range.subtype))
    (hsmallA : Function.Injective (pointEvaluation K a d))
    (hsmallB : Function.Injective (pointEvaluation K b' d))
    (hZ : Function.Injective (scalarEvaluation z (d + 1)))
    (hXtrace : Function.Injective ((restrictTraceForm K m d).comp
      (pointDegreePiece K x d).subtype))
    (hXproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d)))
    (hpureA : Function.Injective ((leftGroupEvaluation (residualPairSpace x d) a).comp
      (rightProjection (residualPairSpace x d)).ker.subtype))
    (hpureB : Function.Injective ((rightGroupEvaluation (residualPairSpace x d) b').comp
      (leftProjection (residualPairSpace x d)).ker.subtype))
    (hcodeA : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K (TraceProductQuotient a z (d + 1)) →
      LinearIndependent K (traceProductCoordinate a z (d + 1) ∘ f))
    (hcodeB : ∀ (r : ℕ) (f : Fin r ↪ Fin p), r ≤ finrank K (TraceProductQuotient b' z (d + 1)) →
      LinearIndependent K (traceProductCoordinate b' z (d + 1) ∘ f))
    (σ : ℤ)
    (hdiff : (finrank K (AmbientEuler K m d) : ℤ) -
      finrank K (AmbientFiberValues a b' z (chartPoint K x)) = σ)
    (hpairCount : (finrank K (twoGroupEvaluation (residualPairSpace x d) a b').ker : ℤ) =
      max 0 (2 * ((p - m * (finrank K (Forms K (m + 1) (d + 1)) - b) : ℕ) : ℤ) + σ)) :
    HasMaximalRank (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)) ∨
      ∃ (v u : Fin p → K), (∀ i, v i = 0 ∨ v i = 1) ∧ (∀ i, u i = 0 ∨ u i = 1) ∧
        ∃ P : MvPolynomial (Fin 1) K, eval 0 P ≠ 0 ∧
          ∀ ε : Fin 1 → K, ε 0 ≠ 0 → eval ε P ≠ 0 →
            HasMaximalRank (markedMovingEvaluation
              (ambientFixedEvaluation a b' z (chartPoint K x) (d + 1 + 1)) z
              (ambientTraceInclusion a b' z (chartPoint K x)) hz v u ε) := by
  let W := AmbientFiberValues a b' z (chartPoint K x)
  let A₀ := ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1)
  let : AddCommGroup (AmbientEuler K m d) := Module.addCommMonoidToAddCommGroup K
  let c := p - m * (finrank K (Forms K (m + 1) (d + 1)) - b)
  have htraceRaw : Function.Injective (relationEvaluation z (d + 1 + 1)) := by
    intro F G hFG
    apply htrace.1
    exact Subtype.ext hFG
  have hA := sliceEvaluation_injective a z (d + 1) ha htraceRaw hmulA hevalA
  have hB := sliceEvaluation_injective b' z (d + 1) hb htraceRaw hmulB hevalB
  let eKernel := residualPairAmbientFiberKernelEquiv K m a b' x z
    ha hb hxs hxt hA hB hXtrace hXproduct
  have hker : (finrank K A₀.ker : ℤ) = max 0 (2 * (c : ℤ) + σ) := by
    rw [← eKernel.finrank_eq]
    exact hpairCount
  rcases maximalRank_or_positive_cokernel A₀ c σ hdiff hker with hmax | ⟨_, _, hcoker⟩
  · exact Or.inl hmax
  let QA := TraceProductQuotient a z (d + 1)
  let QB := TraceProductQuotient b' z (d + 1)
  have hcA : finrank K QA = c := traceProductQuotient_finrank a z (d + 1) ha hscalarA hmulA hevalA
  have hcB : finrank K QB = c := traceProductQuotient_finrank b' z (d + 1) hb hscalarB hmulB hevalB
  let P := ambientCokernelTraceCodes a b' z (chartPoint K x) (d + 1) ha hb htrace hscalarA hscalarB
  have hP := ambientCokernelTraceCodes_surjective a b' z (chartPoint K x) (d + 1)
    ha hb htrace hscalarA hscalarB
  have heDim : finrank K (W ⧸ A₀.range) = finrank K (QA × QB) := by
    rw [hcoker, Module.finrank_prod, hcA, hcB]
    omega
  let eC : (W ⧸ A₀.range) ≃ₗ[K] (QA × QB) := LinearEquiv.ofBijective P
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := P) heDim).mpr hP, hP⟩
  let E := ambientFixedEvaluation a b' z (chartPoint K x) (d + 1 + 1)
  let I := ambientTraceInclusion a b' z (chartPoint K x)
  let A₁ := markedBaseEvaluation E z I
  have hbase : A₁ = A₀ := markedBaseEvaluation_eq_ambient a b' z (chartPoint K x)
  let eQ : (W ⧸ A₁.range) ≃ₗ[K] (W ⧸ A₀.range) :=
    Submodule.quotEquivOfEq _ _ (congrArg (fun f : AmbientEuler K m d →ₗ[K] W => f.range) hbase)
  let eK : A₁.ker ≃ₗ[K] A₀.ker := LinearEquiv.ofEq _ _
    (congrArg (fun f : AmbientEuler K m d →ₗ[K] W => f.ker) hbase)
  let e := eQ.trans eC
  let w₀ := ambientKernelCoefficients a b' x z ha hb hxs hxt hA hB
  let w := w₀.comp eK.toLinearMap
  have hw (F : A₁.ker) : residualEuler K m d (w F) = F.val :=
    ambientKernelCoefficients_reconstruct a b' x z ha hb hxs hxt hA hB (eK F)
  have hpair := residualPair_injective K m x hxs hXtrace hXproduct
  obtain ⟨hS₀, hT₀⟩ := ambientKernelCoefficients_spans a b' x z ha hb hxs hxt hA hB
    hpair hsmallA hsmallB hpureA hpureB hZ
  let : AddCommGroup A₀.ker := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup A₁.ker := Module.addCommMonoidToAddCommGroup K
  let : FiniteDimensional K A₀.ker :=
    FiniteDimensional.of_injective A₀.ker.subtype (Submodule.injective_subtype _)
  let : FiniteDimensional K A₁.ker := FiniteDimensional.of_injective eK.toLinearMap eK.injective
  have hS := span_rows_precomp_equiv eK (fun i : Fin p => (normalSCoefficient (z i)).comp w₀) hS₀
  have hT := span_rows_precomp_equiv eK (fun i : Fin p => (normalTCoefficient (z i)).comp w₀) hT₀
  have hunitA (i : Fin p) : e (A₁.range.mkQ (I (normalTraceFiberValues z (Pi.single i 1, 0)))) =
      (traceProductCoordinate a z (d + 1) i, 0) := by
    change P (Submodule.Quotient.mk (ambientNormalValues a b' z (chartPoint K x)
      (Pi.single i 1, 0))) = _
    exact ambientCokernelTraceCodes_normalClass a b' z (chartPoint K x) (d + 1)
      ha hb htrace hscalarA hscalarB _
  have hunitB (i : Fin p) : e (A₁.range.mkQ (I (normalTraceFiberValues z (0, Pi.single i 1)))) =
      (0, traceProductCoordinate b' z (d + 1) i) := by
    change P (Submodule.Quotient.mk (ambientNormalValues a b' z (chartPoint K x)
      (0, Pi.single i 1))) = _
    exact ambientCokernelTraceCodes_normalClass a b' z (chartPoint K x) (d + 1)
      ha hb htrace hscalarA hscalarB _
  exact Or.inr (exists_maximal_marked_motion E z I hz e w hw hS hT
    (traceProductCoordinate a z (d + 1)) (traceProductCoordinate b' z (d + 1))
    hcodeA hcodeB hunitA hunitB)

end IdealGeneration.TwoNormalIntegral
