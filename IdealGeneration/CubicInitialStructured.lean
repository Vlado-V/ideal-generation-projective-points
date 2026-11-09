module

public import IdealGeneration.CubicInitialGeometry
public import IdealGeneration.CubicInitialStructuredData
public import IdealGeneration.CubicSupportedConfiguration
public import IdealGeneration.ConeReindex

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Realize the checked C.2 representatives in the supported cubic graph family. -/

noncomputable section
namespace IdealGeneration.CubicInitial
open CubicSupported ConeParameterSpace

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

theorem vertex_slopes_ne :
    ∀ i : Fin 10, slope (vertexConeIndex i 0) ≠ slope (vertexConeIndex i 1) := by decide +kernel

theorem edge_slopes_ne :
    ∀ e : Edge 10, B5.single e = false →
      slope (edgeConeIndex e 0) ≠ slope (edgeConeIndex e 1) := by decide +kernel

theorem heights_ne : ∀ i : Fin 108, height i ≠ 0 := by decide +kernel

theorem scales_ne : ∀ e : Edge 10, edgeScale e ≠ 0 := by decide +kernel

/-- Initial primitive parameters with the two C.2 single edges. -/
def initialGraph (K : Type*) [Field K] [CharZero K] : CubicSupported.Parameters K 10 where
  single := B5.single
  vertexSlope i j := slope (vertexConeIndex i j)
  vertexHeight i j := height (vertexConeIndex i j)
  edgeSlope e j := slope (edgeConeIndex e j)
  edgeHeight e j := height (edgeConeIndex e j)
  edgeLambda e := edgeScale e
  vertexSlope_ne i := by exact_mod_cast vertex_slopes_ne i
  vertexHeight_ne i j := by exact_mod_cast heights_ne (vertexConeIndex i j)
  edgeSlope_ne e he := by exact_mod_cast edge_slopes_ne e he
  edgeHeight_ne e j := by exact_mod_cast heights_ne (edgeConeIndex e j)
  edgeLambda_ne e := by exact_mod_cast scales_ne e

/-- The 110 free trace points in the initial C.2 configuration. -/
def initialFree (K : Type*) [Field K] (i : Fin 110) (j : Fin 10) : K :=
  traceCoordinate (freeTraceIndex i) j

private theorem vertex_trace_values :
    ∀ i j : Fin 10, traceCoordinate (vertexTraceIndex i) j = if j = i then 1 else 0 := by
  decide +kernel

private theorem edge_trace_values :
    ∀ (e : Edge 10) (j : Fin 10), traceCoordinate (edgeTraceIndex e) j =
      (if j = e.val.1 then 1 else 0) + (if j = e.val.2 then edgeScale e else 0) := by
  decide +kernel

private theorem edge_trace_index :
    ∀ i : Fin 45, edgeTraceIndex (edgeOrder i) = (i.natAdd 10).castAdd 110 := by decide +kernel

private theorem vertex_cone_index :
    ∀ i : Fin 20, vertexConeIndex (vertexSlotOf i).1 (vertexSlotOf i).2 =
      i.castAdd 88 := by decide +kernel

private theorem edge_cone_index :
    ∀ i : Fin 88, edgeConeIndex (edgeSlotOf i).1 (edgeSlotOf i).2 =
      i.natAdd 20 := by decide +kernel

private theorem vertex_cone_support :
    ∀ i : Fin 20, support (i.castAdd 88) = vertexTraceIndex (vertexSlotOf i).1 := by decide +kernel

private theorem edge_cone_support :
    ∀ i : Fin 88, support (i.natAdd 20) = edgeTraceIndex (edgeSlotOf i).1 := by decide +kernel

private theorem edge_slot_valid :
    ∀ i : Fin 88, B5.single (edgeSlotOf i).1 = false ∨ (edgeSlotOf i).2 = 0 := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

private theorem trace_vertex (i : Fin 10) :
    (initialGraph K).traceRepresentative (initialFree K) (.inl (.inl i)) =
      (configuration support (parameters K)).trace (vertexTraceIndex i) := by
  funext j
  rw [configuration_trace, vertex_trace_values]
  change vertexSupport i (1 : K) j = _
  by_cases h : j = i <;> simp [vertexSupport, h]

private theorem trace_edge (e : Edge 10) :
    (initialGraph K).traceRepresentative (initialFree K) (.inl (.inr e)) =
      (configuration support (parameters K)).trace (edgeTraceIndex e) := by
  funext j
  rw [configuration_trace, edge_trace_values, Nat.cast_add]
  change edgeSupport e (1 : K) (edgeScale e : K) j = _
  by_cases h₁ : j = e.val.1 <;> by_cases h₂ : j = e.val.2 <;>
    simp [edgeSupport, vertexSupport, h₁, h₂]

private theorem trace_free (i : Fin 110) :
    (initialGraph K).traceRepresentative (initialFree K) (.inr i) =
      (configuration support (parameters K)).trace (freeTraceIndex i) := rfl

/-- Every listed trace representative occurs in the structured family. -/
theorem initial_trace_coverage (i : Fin 165) :
    ∃ j, ((initialGraph K).toConeConfiguration (initialFree K)).trace j =
      (configuration support (parameters K)).trace i := by
  refine Fin.addCases (motive := fun r : Fin (55 + 110) =>
    ∃ j, ((initialGraph K).toConeConfiguration (initialFree K)).trace j =
      (configuration support (parameters K)).trace r) ?_ ?_ i
  · intro j
    refine Fin.addCases (motive := fun j : Fin (10 + 45) =>
      ∃ k, ((initialGraph K).toConeConfiguration (initialFree K)).trace k =
        (configuration support (parameters K)).trace (j.castAdd 110)) ?_ ?_ j
    · intro a
      refine ⟨traceLabelEquiv 10 110 (.inl (.inl a)), ?_⟩
      rw [(initialGraph K).toConeConfiguration_trace]
      exact trace_vertex a
    · intro a
      refine ⟨traceLabelEquiv 10 110 (.inl (.inr (edgeOrder a))), ?_⟩
      rw [(initialGraph K).toConeConfiguration_trace, trace_edge, edge_trace_index]
  · intro a
    refine ⟨traceLabelEquiv 10 110 (.inr a), ?_⟩
    rw [(initialGraph K).toConeConfiguration_trace]
    exact trace_free a

private theorem configuration_cone_point
    (a : (initialGraph K).ConeLabel) (i : Fin 108)
    (hn : (initialGraph K).coneNormal a = fun j => (normalCoordinate i j : K))
    (hh : (initialGraph K).coneHeight a = (height i : K))
    (ht : (initialGraph K).traceRepresentative (initialFree K)
      ((initialGraph K).coneSupportLabel a) =
        (configuration support (parameters K)).trace (support i)) :
    ((initialGraph K).toConeConfiguration (initialFree K)).point ((initialGraph K).coneLabelEquiv a)
      = (configuration support (parameters K)).point i := by
  funext j
  unfold ConeConfiguration.point
  have hn' : ((initialGraph K).toConeConfiguration (initialFree K)).normal
      ((initialGraph K).coneLabelEquiv a) = (initialGraph K).coneNormal a := by
    simp [CubicSupported.Parameters.toConeConfiguration]
  have hh' : ((initialGraph K).toConeConfiguration (initialFree K)).height
      ((initialGraph K).coneLabelEquiv a) = (initialGraph K).coneHeight a := by
    simp [CubicSupported.Parameters.toConeConfiguration]
  rw [hn', hh', (initialGraph K).toConeConfiguration_support,
    (initialGraph K).toConeConfiguration_trace, hn, hh, ht]
  rfl

/-- Every listed cone representative occurs in the structured family. -/
theorem initial_cone_coverage (i : Fin 108) :
    ∃ j, ((initialGraph K).toConeConfiguration (initialFree K)).point j =
      (configuration support (parameters K)).point i := by
  refine Fin.addCases (motive := fun r : Fin (20 + 88) =>
    ∃ j, ((initialGraph K).toConeConfiguration (initialFree K)).point j =
      (configuration support (parameters K)).point r) ?_ ?_ i
  · intro v
    let a : (initialGraph K).ConeLabel := .inl (vertexSlotOf v)
    refine ⟨(initialGraph K).coneLabelEquiv a, configuration_cone_point a _ ?_ ?_ ?_⟩
    · funext j
      fin_cases j <;> simp [a, CubicSupported.Parameters.coneNormal, initialGraph,
        vertex_cone_index, normalCoordinate, slope]
    · change (height (vertexConeIndex (vertexSlotOf v).1 (vertexSlotOf v).2) : K) = _
      rw [vertex_cone_index]
    · rw [vertex_cone_support]
      exact trace_vertex (vertexSlotOf v).1
  · intro e
    let a : (initialGraph K).ConeLabel := .inr ⟨edgeSlotOf e, edge_slot_valid e⟩
    refine ⟨(initialGraph K).coneLabelEquiv a, configuration_cone_point a _ ?_ ?_ ?_⟩
    · funext j
      fin_cases j <;> simp [a, CubicSupported.Parameters.coneNormal, initialGraph,
        edge_cone_index, normalCoordinate, slope]
    · change (height (edgeConeIndex (edgeSlotOf e).1 (edgeSlotOf e).2) : K) = _
      rw [edge_cone_index]
    · rw [edge_cone_support]
      exact trace_edge (edgeSlotOf e).1

/-- The literal C.2 middle witness is a witness in the initial supported family. -/
theorem structured_middle_injective
    (h : Function.Injective ((configuration support (parameters K)).middleMultiplication 3)) :
    Function.Injective (((initialGraph K).toConeConfiguration (initialFree K)).middleMultiplication 3) :=
  ConeConfiguration.middle_injective_of_representative_coverage _ _
    initial_cone_coverage initial_trace_coverage h

end IdealGeneration.CubicInitial
