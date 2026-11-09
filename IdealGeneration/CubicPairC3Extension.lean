module

public import IdealGeneration.CubicPairC3Actual

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Extending the primitive C.3 parameters while keeping the earlier pool fixed. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicPair CubicMixedLocality

variable {k : ℕ}

/-- The four lift centers in the ambient graph. -/
def c3CenterEmbedding (j : Fin k) : Fin 4 ↪ Fin ((10 + 2 * k) + 2) :=
  (Fin.natAddEmb 3).trans (pairC3AmbientEmbedding j)

/-- The C.3 edges whose parameters are used by a lift center. -/
abbrev C3IncidentEdge := {e : Edge 7 // 3 ≤ e.val.2.val}

/-- The embedding of the C.3 edges used by the four lifts. -/
def c3IncidentEdgeEmbedding (j : Fin k) : C3IncidentEdge ↪ Edge ((10 + 2 * k) + 2) where
  toFun e := pairC3Edge j e.val
  inj' a b hab := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (pairC3AmbientEmbedding j).injective (congrArg (fun e => e.val.1) hab)
    · exact (pairC3AmbientEmbedding j).injective (congrArg (fun e => e.val.2) hab)

private theorem extend_has_property {α β γ : Type*} (e : α ↪ β) (new : α → γ) (old : β → γ)
    (p : β → γ → Prop) (hnew : ∀ a, p (e a) (new a)) (hold : ∀ b, p b (old b)) (b : β) :
    p b (Function.extend e new old b) := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [e.injective.extend_apply]
    exact hnew a
  · rw [Function.extend_apply' _ _ _ hb]
    exact hold b

/-- Install only the four C.3 vertex data and their incident edge data. -/
def withC3Parameters (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (hQ : ∀ e, Q.single e = single e) (j : Fin k) : Parameters ℚ ((10 + 2 * k) + 2) where
  single := Q.single
  vertexSlope := Function.extend (c3CenterEmbedding j) (c3Parameters.vertexSlope ∘ centerIndex) Q.vertexSlope
  vertexHeight := Function.extend (c3CenterEmbedding j) (c3Parameters.vertexHeight ∘ centerIndex) Q.vertexHeight
  edgeSlope := Function.extend (c3IncidentEdgeEmbedding j) (c3Parameters.edgeSlope ∘ Subtype.val) Q.edgeSlope
  edgeHeight := Function.extend (c3IncidentEdgeEmbedding j) (c3Parameters.edgeHeight ∘ Subtype.val) Q.edgeHeight
  edgeLambda := Function.extend (c3IncidentEdgeEmbedding j) (c3Parameters.edgeLambda ∘ Subtype.val) Q.edgeLambda
  vertexSlope_ne := extend_has_property (c3CenterEmbedding j)
    (c3Parameters.vertexSlope ∘ centerIndex) Q.vertexSlope (fun _ a => a 0 ≠ a 1)
    (fun c => c3Parameters.vertexSlope_ne (centerIndex c)) Q.vertexSlope_ne
  vertexHeight_ne := extend_has_property (c3CenterEmbedding j)
    (c3Parameters.vertexHeight ∘ centerIndex) Q.vertexHeight (fun _ a => ∀ d, a d ≠ 0)
    (fun c => c3Parameters.vertexHeight_ne (centerIndex c)) Q.vertexHeight_ne
  edgeSlope_ne := extend_has_property (c3IncidentEdgeEmbedding j)
    (c3Parameters.edgeSlope ∘ Subtype.val) Q.edgeSlope (fun e a => Q.single e = false → a 0 ≠ a 1)
    (fun e he => c3Parameters.edgeSlope_ne e.val (by
      change Q.single (pairC3Edge j e.val) = false at he
      rwa [hQ, pairC3Edge_single] at he)) Q.edgeSlope_ne
  edgeHeight_ne := extend_has_property (c3IncidentEdgeEmbedding j)
    (c3Parameters.edgeHeight ∘ Subtype.val) Q.edgeHeight (fun _ a => ∀ d, a d ≠ 0)
    (fun e => c3Parameters.edgeHeight_ne e.val) Q.edgeHeight_ne
  edgeLambda_ne := extend_has_property (c3IncidentEdgeEmbedding j)
    (c3Parameters.edgeLambda ∘ Subtype.val) Q.edgeLambda (fun _ a => a ≠ 0)
    (fun e => c3Parameters.edgeLambda_ne e.val) Q.edgeLambda_ne

@[simp] theorem withC3Parameters_single (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (hQ : ∀ e, Q.single e = single e) (j : Fin k) (e : Edge ((10 + 2 * k) + 2)) :
    (withC3Parameters Q hQ j).single e = Q.single e := rfl

/-- The installed data give the precise primitive agreement required for C.3. -/
theorem agreesWithC3_withC3Parameters (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (hQ : ∀ e, Q.single e = single e) (j : Fin k) : AgreesWithC3 (withC3Parameters Q hQ j) j := by
  intro c
  constructor
  · exact ((c3CenterEmbedding j).injective.extend_apply
      (c3Parameters.vertexSlope ∘ centerIndex) Q.vertexSlope c).symm
  · exact ((c3CenterEmbedding j).injective.extend_apply
      (c3Parameters.vertexHeight ∘ centerIndex) Q.vertexHeight c).symm
  · intro e he
    have horder := e.property
    have he' : 3 ≤ e.val.2.val := by
      rcases he with h | h
      · have hc : 3 ≤ e.val.1.val := by rw [h]; simp [centerIndex]
        omega
      · rw [h]
        simp [centerIndex]
    let a : C3IncidentEdge := ⟨e, he'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change c3Parameters.single e = Q.single (pairC3Edge j e)
      rw [hQ, pairC3Edge_single]
    · exact ((c3IncidentEdgeEmbedding j).injective.extend_apply
        (c3Parameters.edgeLambda ∘ Subtype.val) Q.edgeLambda a).symm
    · exact ((c3IncidentEdgeEmbedding j).injective.extend_apply
        (c3Parameters.edgeSlope ∘ Subtype.val) Q.edgeSlope a).symm
    · exact ((c3IncidentEdgeEmbedding j).injective.extend_apply
        (c3Parameters.edgeHeight ∘ Subtype.val) Q.edgeHeight a).symm

private theorem c3CenterEmbedding_lower (j : Fin k) (c : Fin 4) :
    10 + 2 * j.val ≤ (c3CenterEmbedding j c).val := by
  have hj := j.isLt
  fin_cases c
  · change 10 + 2 * j.val ≤ 10 + 2 * j.val
    omega
  · change 10 + 2 * j.val ≤ 11 + 2 * j.val
    omega
  · change 10 + 2 * j.val ≤ 10 + 2 * k + 0
    omega
  · change 10 + 2 * j.val ≤ 10 + 2 * k + 1
    omega

private theorem c3IncidentEdgeEmbedding_lower (j : Fin k) (e : C3IncidentEdge) :
    10 + 2 * j.val ≤ (c3IncidentEdgeEmbedding j e).val.2.val := by
  have hi := e.val.val.2.isLt
  have he := e.property
  let c : Fin 4 := ⟨e.val.val.2.val - 3, by omega⟩
  have hc : centerIndex c = e.val.val.2 := by
    apply Fin.ext
    change 3 + (e.val.val.2.val - 3) = e.val.val.2.val
    omega
  change 10 + 2 * j.val ≤ (pairC3Ambient j e.val.val.2).val
  rw [← hc]
  exact c3CenterEmbedding_lower j c

/-- Installing C.3 preserves all earlier vertex data, including the initial pool. -/
theorem withC3Parameters_vertex_eq_of_earlier (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (hQ : ∀ e, Q.single e = single e) (j : Fin k) {i : Fin ((10 + 2 * k) + 2)}
    (hi : i.val < 10 + 2 * j.val) :
    (withC3Parameters Q hQ j).vertexSlope i = Q.vertexSlope i ∧
      (withC3Parameters Q hQ j).vertexHeight i = Q.vertexHeight i := by
  have hoff : i ∉ Set.range (c3CenterEmbedding j) := by
    rintro ⟨c, rfl⟩
    exact (not_lt_of_ge (c3CenterEmbedding_lower j c)) hi
  exact ⟨Function.extend_apply' (c3Parameters.vertexSlope ∘ centerIndex) Q.vertexSlope i hoff,
    Function.extend_apply' (c3Parameters.vertexHeight ∘ centerIndex) Q.vertexHeight i hoff⟩

/-- Installing C.3 preserves every edge contained in the earlier coordinates. -/
theorem withC3Parameters_edge_eq_of_earlier (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (hQ : ∀ e, Q.single e = single e) (j : Fin k) {e : Edge ((10 + 2 * k) + 2)}
    (he : e.val.2.val < 10 + 2 * j.val) :
    (withC3Parameters Q hQ j).edgeSlope e = Q.edgeSlope e ∧
      (withC3Parameters Q hQ j).edgeHeight e = Q.edgeHeight e ∧
      (withC3Parameters Q hQ j).edgeLambda e = Q.edgeLambda e := by
  have hoff : e ∉ Set.range (c3IncidentEdgeEmbedding j) := by
    rintro ⟨a, rfl⟩
    exact (not_lt_of_ge (c3IncidentEdgeEmbedding_lower j a)) he
  exact ⟨Function.extend_apply' (c3Parameters.edgeSlope ∘ Subtype.val) Q.edgeSlope e hoff,
    Function.extend_apply' (c3Parameters.edgeHeight ∘ Subtype.val) Q.edgeHeight e hoff,
    Function.extend_apply' (c3Parameters.edgeLambda ∘ Subtype.val) Q.edgeLambda e hoff⟩

/-- The installed C.3 primitive data make the actual pair core nonsingular. -/
theorem actual_pairCoreMatrix_det_ne_zero_withC3Parameters
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e) (j : Fin k)
    (faceParameter : PairFullFace k j → ℚ) (hface : ∀ F, faceParameter F ≠ 0) :
    (pairCoreMatrix (actualB7Data (withC3Parameters Q hQ j))
      (c3PairBlockData ℚ j faceParameter hface)).det ≠ 0 :=
  actual_pairCoreMatrix_det_ne_zero_of_agreesWithC3 _ j (agreesWithC3_withC3Parameters Q hQ j) _ hface

end IdealGeneration.CubicSupported.B5
