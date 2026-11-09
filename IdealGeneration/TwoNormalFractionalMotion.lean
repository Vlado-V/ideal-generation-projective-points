module

public import IdealGeneration.TwoNormalFractionalResponse
public import IdealGeneration.TwoNormalFractionalKernelDimension
public import IdealGeneration.TwoNormalFractionalCokernel
public import IdealGeneration.TwoNormalIntegralMarkedTransfer

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Maximal rank at a fractional marked configuration -/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open Module MvPolynomial TwoNormalSlice TwoNormalTrace TwoNormalIntegral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d b q k : ℕ}

/-- Retraction to the special fiber fixes the normal-only response. -/
theorem lineFiberRemainder_fractionalKernel
    (a c : PointCoordinates K m b) (x : PointCoordinates K (m + 1) q)
    (z : Fin k → Fin m → K) (hc : SliceConditions a c z d)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (u v : Fin k → K) (f : AmbientKernel a c x z (d + 1 + 1)) :
    lineFiberRemainder (fun i => commonTracePoint (z i))
      (fun i => twoNormalVelocity (m := m) (u i) (v i)) hz (d + 1 + 1) 0 f.val =
      normalTraceFiberValues z
        (fun i => v i * firstNormalSource a c x z (d + 1 + 1) i f,
          fun i => u i * secondNormalSource a c x z (d + 1 + 1) i f) := by
  let y := fun i => commonTracePoint (z i)
  let speed := fun i => twoNormalVelocity (m := m) (u i) (v i)
  let N := normalTraceFiberValues z
    (fun i => v i * firstNormalSource a c x z (d + 1 + 1) i f,
      fun i => u i * secondNormalSource a c x z (d + 1 + 1) i f)
  have h : lineValueRemainder y speed (d + 1 + 1) 0 f.val = N.val := by
    funext i j
    change DifferentialLine.quotientLine (y i) (speed i) 0 (f.val.val j).val = N.val i j
    rw [DifferentialLine.quotientLine_zero]
    exact congrFun (normalFirstCoefficient_kernel a c x z hc i (u i) (v i) f) j
  change fiberRetraction y hz (lineValueRemainder y speed (d + 1 + 1) 0 f.val) = N
  rw [h]
  exact fiberRetraction_self y hz N

/-- The actual fractional Euler kernel and the two slice quotient codes
give a maximal-rank two-normal motion when their dimension count balances. -/
theorem fractional_marked_fiber_transfer
    (a c : PointCoordinates K m b) (x : PointCoordinates K (m + 1) (q + 1))
    (z : Fin k → Fin m → K)
    (hc : SliceConditions a c z d) (hs : SourceConditions a c x z d)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (htrace : Function.Surjective (traceFiberEvaluation z (d + 1 + 1)))
    (hscalarA : Function.Surjective (pointEvaluation K a (d + 1)))
    (hscalarB : Function.Surjective (pointEvaluation K c (d + 1)))
    (hX : Function.Surjective (normalFiberEvaluation K m a c x d))
    (hcodeA : ∀ (r : ℕ) (f : Fin r ↪ Fin k), r ≤ finrank K (TraceProductQuotient a z (d + 1)) →
      LinearIndependent K (traceProductCoordinate a z (d + 1) ∘ f))
    (hcodeB : ∀ (r : ℕ) (f : Fin r ↪ Fin k), r ≤ finrank K (TraceProductQuotient c z (d + 1)) →
      LinearIndependent K (traceProductCoordinate c z (d + 1) ∘ f))
    (hcount : (finrank K (traceFiberEvaluation z (d + 1 + 1)).ker : ℤ) +
        finrank K (pairEvaluation K m a c x d).ker -
        ((finrank K (AmbientEuler K m d) : ℤ) -
          finrank K (AmbientFiberValues a c z (chartPoint K x))) =
      (finrank K (TraceProductQuotient a z (d + 1)) : ℤ) +
        finrank K (TraceProductQuotient c z (d + 1))) :
    ∃ (v u : Fin k → K), (∀ i, v i = 0 ∨ v i = 1) ∧ (∀ i, u i = 0 ∨ u i = 1) ∧
      ∃ P : MvPolynomial (Fin 1) K, eval 0 P ≠ 0 ∧
        ∀ ε : Fin 1 → K, ε 0 ≠ 0 → eval ε P ≠ 0 →
          HasMaximalRank (markedMovingEvaluation
            (ambientFixedEvaluation a c z (chartPoint K x) (d + 1 + 1)) z
            (ambientTraceInclusion a c z (chartPoint K x)) hz v u ε) := by
  let D := d + 1 + 1
  let W := AmbientFiberValues a c z (chartPoint K x)
  let A₀ := ambientFiberEvaluation a c z (chartPoint K x) D
  let QA := TraceProductQuotient a z (d + 1)
  let QB := TraceProductQuotient c z (d + 1)
  let : AddCommGroup (AmbientEuler K m d) := Module.addCommMonoidToAddCommGroup K
  have hk := finrank_fractional_ambientKernel a c x z hc hs.normalS hs.normalT hX
  have hr := TwoGroup.rank_nullity_monoid A₀
  have hq := A₀.range.finrank_quotient_add_finrank
  have heDim : finrank K (W ⧸ A₀.range) = finrank K (QA × QB) := by
    rw [Module.finrank_prod]
    change finrank K A₀.ker = finrank K (traceFiberEvaluation z D).ker +
      finrank K (pairEvaluation K m a c x d).ker at hk
    have hk' : (finrank K A₀.ker : ℤ) = finrank K (traceFiberEvaluation z D).ker +
        finrank K (pairEvaluation K m a c x d).ker := by exact_mod_cast hk
    change finrank K A₀.range + finrank K A₀.ker = finrank K (AmbientEuler K m d) at hr
    change finrank K (W ⧸ A₀.range) + finrank K A₀.range = finrank K W at hq
    change (finrank K (traceFiberEvaluation z D).ker : ℤ) +
      finrank K (pairEvaluation K m a c x d).ker -
      ((finrank K (AmbientEuler K m d) : ℤ) - finrank K W) =
      (finrank K QA : ℤ) + finrank K QB at hcount
    omega
  let P := ambientCokernelTraceCodes_of_attached a c z (chartPoint K x) (d + 1)
    hc.attachedA hc.attachedB hc.normalA hc.normalB htrace hscalarA hscalarB
  have hP := ambientCokernelTraceCodes_surjective_of_attached a c z (chartPoint K x) (d + 1)
    hc.attachedA hc.attachedB hc.normalA hc.normalB htrace hscalarA hscalarB
  let eC : (W ⧸ A₀.range) ≃ₗ[K] (QA × QB) := LinearEquiv.ofBijective P
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := P) heDim).mpr hP, hP⟩
  let E := ambientFixedEvaluation a c z (chartPoint K x) D
  let I := ambientTraceInclusion a c z (chartPoint K x)
  let A₁ := markedBaseEvaluation E z I
  have hbase : A₁ = A₀ := markedBaseEvaluation_eq_ambient a c z (chartPoint K x)
  let eQ : (W ⧸ A₁.range) ≃ₗ[K] (W ⧸ A₀.range) :=
    Submodule.quotEquivOfEq _ _ (congrArg (fun f : AmbientEuler K m d →ₗ[K] W => f.range) hbase)
  let eK : A₁.ker ≃ₗ[K] AmbientKernel a c x z D := LinearEquiv.ofEq _ _
    ((congrArg (fun f : AmbientEuler K m d →ₗ[K] W => f.ker) hbase).trans
      (ambientEvaluation_ker_eq_fiber K m a c x z).symm)
  let e := eQ.trans eC
  let α := fun i : Fin k => (firstNormalSource a c x z D i).comp eK.toLinearMap
  let β := fun i : Fin k => (secondNormalSource a c x z D i).comp eK.toLinearMap
  let : AddCommGroup A₁.ker := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (AmbientKernel a c x z D) := Module.addCommMonoidToAddCommGroup K
  obtain ⟨hS, hT⟩ := normalSources_span a c x z hc hs
  have hα : Function.Injective (LinearMap.pi α) :=
    (scalarEvaluation_injective_of_span _ hS).comp eK.injective
  have hβ : Function.Injective (LinearMap.pi β) :=
    (scalarEvaluation_injective_of_span _ hT).comp eK.injective
  let : FiniteDimensional K A₁.ker := FiniteDimensional.of_injective _ hα
  have hunitA (i : Fin k) : e (A₁.range.mkQ (I (normalTraceFiberValues z (Pi.single i 1, 0)))) =
      (traceProductCoordinate a z (d + 1) i, 0) := by
    change P (Submodule.Quotient.mk (ambientNormalValues a c z (chartPoint K x)
      (Pi.single i 1, 0))) = _
    exact ambientCokernelTraceCodes_normalClass_of_attached a c z (chartPoint K x) (d + 1)
      hc.attachedA hc.attachedB hc.normalA hc.normalB htrace hscalarA hscalarB _
  have hunitB (i : Fin k) : e (A₁.range.mkQ (I (normalTraceFiberValues z (0, Pi.single i 1)))) =
      (0, traceProductCoordinate c z (d + 1) i) := by
    change P (Submodule.Quotient.mk (ambientNormalValues a c z (chartPoint K x)
      (0, Pi.single i 1))) = _
    exact ambientCokernelTraceCodes_normalClass_of_attached a c z (chartPoint K x) (d + 1)
      hc.attachedA hc.attachedB hc.normalA hc.normalB htrace hscalarA hscalarB _
  apply exists_maximal_marked_motion_of_response E z I hz e α β
    (scalarRows_span_of_injective _ hα) (scalarRows_span_of_injective _ hβ) _
    (traceProductCoordinate a z (d + 1)) (traceProductCoordinate c z (d + 1))
    hcodeA hcodeB hunitA hunitB
  intro v u F
  exact lineFiberRemainder_fractionalKernel a c x z hc hz u v (eK F)

end IdealGeneration.TwoNormalFractional
