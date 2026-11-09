module

public import IdealGeneration.QuadraticVariableTransport
public import IdealGeneration.QuadraticTracePostulation
public import IdealGeneration.ConeMiddleOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The paired flag and its marked cones in the finite coordinate spaces of the cone family. -/

noncomputable section
namespace IdealGeneration.QuadraticCanonicalConeConfiguration
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticLiftParameters
open QuadraticVariableTransport QuadraticTracePostulation QuadraticFlagFamily
open scoped Classical

variable {K P J E : Type*} [Field K]
variable {m p q : ℕ}

/-- The native trace variables have the prescribed cardinality. -/
def variableOrder [Fintype P] [Fintype J]
    (hm : Fintype.card (P × Bool) + Fintype.card J = m) : ((P × Bool) ⊕ J) ≃ Fin m :=
  Fintype.equivFinOfCardEq (by rwa [Fintype.card_sum])

/-- There is one cone for each base coordinate and two for each layer. -/
def coneOrder [Fintype P] [Fintype J]
    (hp : Fintype.card (P × Bool) + 2 * Fintype.card J = p) : ConeIndex P J ≃ Fin p :=
  Fintype.equivFinOfCardEq (by simpa [ConeIndex, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm] using hp)

/-- The trace order includes one point for each flag label and each extra probe. -/
def pointOrder [Fintype P] [Fintype J] [Fintype E]
    (hq : flagCount (Fintype.card (P × Bool)) (Fintype.card J) + Fintype.card E = q) :
    TraceLabel P J E ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rwa [card_traceLabel])

/-- The chosen cones have distinct marked flag supports. -/
theorem coneFlagLabel_injective (p₀ : P) : Function.Injective (coneFlagLabel (J := J) p₀) := by
  rintro (i | ⟨j, b⟩) (i' | ⟨j', b'⟩) h
  · exact congrArg Sum.inl (Sym2.diag_injective (Sum.inl.inj h))
  · cases b' <;> cases h
  · cases b <;> cases h
  · cases b <;> cases b'
    · exact congrArg (fun a => Sum.inr (a, false)) (Sum.inl.inj (Sum.inr.inj h))
    · cases h
    · cases h
    · exact congrArg (fun a => Sum.inr (a, true)) (congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj h)))

variable (D : QuadraticLiftParameters K P J) (e : ((P × Bool) ⊕ J) ≃ Fin m)
  (r : ConeIndex P J ≃ Fin p) (k : TraceLabel P J E ≃ Fin q)
  (extra : E → (P × Bool) ⊕ J → K)

/-- The cone heights are included in the normal coordinates of the explicit lifts. -/
def configuration : ConeConfiguration K 2 m p q where
  trace i := traceLabelPoint extra (k.symm i) ∘ e.symm
  normal i := D.coneNormalPoint (r.symm i) ∘ finTwoEquiv
  support i := k (.inl (coneFlagLabel D.distinguishedPair (r.symm i)))
  height _ := 1

@[simp] theorem configuration_trace (t : TraceLabel P J E) :
    (configuration D e r k extra).trace (k t) = traceLabelPoint extra t ∘ e.symm := by
  simp [configuration]

@[simp] theorem configuration_normal (z : ConeIndex P J) :
    (configuration D e r k extra).normal (r z) = D.coneNormalPoint z ∘ finTwoEquiv := by
  simp [configuration]

@[simp] theorem configuration_support (z : ConeIndex P J) :
    (configuration D e r k extra).support (r z) = k (.inl (coneFlagLabel D.distinguishedPair z)) := by
  simp [configuration]

@[simp] theorem configuration_height (i : Fin p) : (configuration D e r k extra).height i = 1 := rfl

theorem configuration_support_injective : Function.Injective (configuration D e r k extra).support := by
  intro i j h
  apply r.symm.injective
  apply coneFlagLabel_injective D.distinguishedPair
  exact Sum.inl.inj (k.injective h)

/-- Every extra trace label remains free as a support for an appended cone point. -/
theorem configuration_support_ne_extra (i : Fin p) (u : E) :
    (configuration D e r k extra).support i ≠ k (.inr u) := by
  obtain ⟨z, rfl⟩ := r.surjective i
  rw [configuration_support]
  exact fun h => Sum.inl_ne_inr (k.injective h)

/-- The embedded trace representatives have zero normal coordinates. -/
theorem configuration_tracePoint (t : TraceLabel P J E) :
    (configuration D e r k extra).tracePoint (k t) = pointOf e 0 (traceLabelPoint extra t) := by
  change Fin.append (fun _ : Fin 2 => (0 : K)) ((configuration D e r k extra).trace (k t)) =
    Fin.append ((0 : Bool → K) ∘ finTwoEquiv) (traceLabelPoint extra t ∘ e.symm)
  rw [configuration_trace]
  all_goals rfl

/-- The ordered cone points are exactly the representatives of the lift construction. -/
theorem configuration_compatible (z : ConeIndex P J) :
    (configuration D e r k extra).point (r z) = pointOf e (D.coneNormalPoint z) (D.coneTracePoint z) := by
  let C := configuration D e r k extra
  have ht : C.trace (C.support (r z)) = D.coneTracePoint z ∘ e.symm := by
    change (configuration D e r k extra).trace ((configuration D e r k extra).support (r z)) = _
    rw [configuration_support, configuration_trace]
    change flagLabelPoint (coneFlagLabel D.distinguishedPair z) ∘ e.symm = _
    rw [flagLabelPoint_coneFlagLabel]
  change Fin.append ((configuration D e r k extra).normal (r z))
      (fun j => (configuration D e r k extra).height (r z) * C.trace (C.support (r z)) j) =
    Fin.append (D.coneNormalPoint z ∘ finTwoEquiv) (D.coneTracePoint z ∘ e.symm)
  rw [configuration_normal, configuration_height, ht]
  simp only [one_mul]

/-- Every cone normal is nonzero, including both cones over each layer. -/
theorem coneNormalPoint_ne_zero (z : ConeIndex P J) : D.coneNormalPoint z ≠ 0 := by
  intro h
  have hs := congrFun h false
  have ht := congrFun h true
  rcases z with i | ⟨j, b⟩
  · exact D.baseHeight_ne i (by simpa [coneNormalPoint] using ht)
  · cases b
    · have h₁ : D.height₀ j * (D.normal₀ j).1 = 0 := by simpa [coneNormalPoint] using hs
      have h₂ : D.height₀ j * (D.normal₀ j).2 = 0 := by simpa [coneNormalPoint] using ht
      exact D.determinant_ne j (by simp [(mul_eq_zero.mp h₁).resolve_left (D.height₀_ne j),
        (mul_eq_zero.mp h₂).resolve_left (D.height₀_ne j)])
    · have h₁ : D.height₁ j * (D.normal₁ j).1 = 0 := by simpa [coneNormalPoint] using hs
      have h₂ : D.height₁ j * (D.normal₁ j).2 = 0 := by simpa [coneNormalPoint] using ht
      exact D.determinant_ne j (by simp [(mul_eq_zero.mp h₁).resolve_left (D.height₁_ne j),
        (mul_eq_zero.mp h₂).resolve_left (D.height₁_ne j)])

theorem configuration_normal_ne_zero (i : Fin p) : (configuration D e r k extra).normal i ≠ 0 := by
  obtain ⟨z, rfl⟩ := r.surjective i
  rw [configuration_normal]
  intro h
  apply coneNormalPoint_ne_zero D z
  funext b
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
    congrFun h (finTwoEquiv.symm b)

/-- Trace scalar interpolation survives the relabelling of both points and variables. -/
theorem configuration_traceEvaluation_surjective
    (h : Function.Surjective (traceLabelEvaluation extra)) :
    Function.Surjective (ConeParameterSpace.traceEvaluation
      (ConeParameterSpace.encode (configuration D e r k extra)) 2) := by
  intro v
  obtain ⟨f, hf⟩ := h (v ∘ k)
  refine ⟨⟨rename e f.val, f.property.rename_isHomogeneous⟩, ?_⟩
  funext i
  obtain ⟨t, rfl⟩ := k.surjective i
  change eval ((configuration D e r k extra).trace (k t)) (rename e f.val) = v (k t)
  rw [configuration_trace, eval_rename]
  have hcomp : (traceLabelPoint extra t ∘ e.symm) ∘ e = traceLabelPoint extra t := by
    funext j
    simp
  rw [hcomp]
  exact congrFun hf t

/-- Each trace representative is nonzero when the trace values interpolate independently. -/
theorem configuration_trace_ne_zero (h : Function.Surjective (traceLabelEvaluation extra))
    (i : Fin q) : (configuration D e r k extra).trace i ≠ 0 := by
  obtain ⟨t, rfl⟩ := k.surjective i
  rw [configuration_trace]
  intro hz
  apply point_ne_zero_of_quadraticEvaluation_surjective (traceLabelPoint extra) h t
  funext j
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using congrFun hz (e j)

/-- Trace interpolation and normal interpolation give the scalar ranks for the middle-rank open. -/
theorem configuration_fullEvaluation
    (h : Function.Surjective (traceLabelEvaluation extra))
    (hnormal : Function.Surjective (ConeMiddleFamily.normalEvaluation
      (configuration D e r k extra).support (ConeParameterSpace.encode (configuration D e r k extra)) 2)) :
    ConeMiddleFamily.FullEvaluation (configuration D e r k extra).support
      (ConeParameterSpace.encode (configuration D e r k extra)) 2 := by
  refine ConeMiddleFamily.fullEvaluation_of_degree _ _ _ ?_ hnormal
    (configuration_traceEvaluation_surjective D e r k extra h)
  intro i
  rw [ConeParameterSpace.configuration_encode]
  exact (configuration D e r k extra).point_ne_zero i (configuration_normal_ne_zero D e r k extra i)

section Canonical

variable [CharZero K] [Fintype P] [DecidableEq J]

/-- The first normal coordinate is nonzero at every cone of the canonical family. -/
theorem canonical_configuration_s_ne_zero (p₀ : P) (layers : Bool → J) (i : Fin p) :
    (configuration (parameters K p₀ layers) e r k extra).point i
      (normalIndex (m := m) false) ≠ 0 := by
  obtain ⟨z, rfl⟩ := r.surjective i
  rw [configuration_compatible (parameters K p₀ layers) e r k extra z, pointOf_normal]
  rcases z with i | ⟨j, b⟩
  · change 1 * (naturalSlope p₀ i : K) ≠ 0
    rw [one_mul, Nat.cast_ne_zero]
    unfold naturalSlope
    split <;> omega
  · cases b <;> by_cases hj : j = layers true <;> norm_num [coneNormalPoint, parameters, hj]

end Canonical
end IdealGeneration.QuadraticCanonicalConeConfiguration
