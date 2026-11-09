module

public import IdealGeneration.CubicB11PoolTransport
public import IdealGeneration.CubicSupportedRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Installing a pool witness while retaining all old cone parameters. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicMixedLocality

variable {K : Type*} [Field K] {k : ℕ}

/-- The full edge image of the initial pool and its two extension vertices. -/
def poolExtendedEdge (k : ℕ) (e : Edge 12) : Edge ((10 + 2 * k) + 2) :=
  edgeImage (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) e

private theorem poolExtendedEmbedding_val (k : ℕ) (i : Fin 12) :
    (poolExtendedEmbedding k i).val = if i.val < 10 then i.val else i.val + 2 * k := rfl

/-- The restriction of the larger graph to the pool and the new pair is the base graph. -/
theorem poolExtendedEdge_single (k : ℕ) (e : Edge 12) : single (poolExtendedEdge k e) = single e := by
  apply Bool.eq_iff_iff.mpr
  rw [single_eq_true, single_eq_true]
  have he : e.val.1.val < e.val.2.val := e.property
  have h₁ := e.val.1.isLt
  have h₂ := e.val.2.isLt
  simp only [poolExtendedEdge, edgeImage_fst, edgeImage_snd, poolExtendedEmbedding_val]
  split_ifs <;> unfold singleLabels <;> omega

/-- The two vertex parameters copied from the base witness. -/
def poolNewVertexEmbedding (k : ℕ) : Fin 2 ↪ Fin ((10 + 2 * k) + 2) :=
  (Fin.natAddEmb 10).trans (poolExtendedEmbedding k)

@[simp] theorem poolNewVertexEmbedding_apply (k : ℕ) (b : Fin 2) :
    poolNewVertexEmbedding k b = Fin.natAdd (10 + 2 * k) b := poolExtendedEmbedding_new k b

/-- The edges of the base witness involving at least one new vertex. -/
abbrev PoolNewEdge := {e : Edge 12 // 10 ≤ e.val.2.val}

/-- Only edges incident to a new vertex can be patched. -/
def poolNewEdgeEmbedding (k : ℕ) : PoolNewEdge ↪ Edge ((10 + 2 * k) + 2) where
  toFun e := poolExtendedEdge k e.val
  inj' a b hab := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (poolExtendedEmbedding k).injective (congrArg (fun e => e.val.1) hab)
    · exact (poolExtendedEmbedding k).injective (congrArg (fun e => e.val.2) hab)

private theorem poolNewVertexEmbedding_lower (k : ℕ) (b : Fin 2) :
    10 + 2 * k ≤ (poolNewVertexEmbedding k b).val := by
  rw [poolNewVertexEmbedding_apply]
  change 10 + 2 * k ≤ 10 + 2 * k + b.val
  omega

private theorem poolNewEdgeEmbedding_lower (k : ℕ) (e : PoolNewEdge) :
    10 + 2 * k ≤ (poolNewEdgeEmbedding k e).val.2.val := by
  change 10 + 2 * k ≤ (poolExtendedEmbedding k e.val.val.2).val
  rw [poolExtendedEmbedding_val, ite_eq_right (not_lt.mpr e.property)]
  have he := e.property
  omega

private theorem extend_valid {α β γ : Type*} (e : α ↪ β) (new : α → γ) (old : β → γ)
    (p : β → γ → Prop) (hnew : ∀ a, p (e a) (new a)) (hold : ∀ b, p b (old b)) (b : β) :
    p b (Function.extend e new old b) := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [e.injective.extend_apply]
    exact hnew a
  · rw [Function.extend_apply' _ _ _ hb]
    exact hold b

variable (S : Parameters K 12) (L : Parameters K ((10 + 2 * k) + 2))

private theorem poolNewEdge_single (hS : ∀ e, S.single e = single e)
    (hL : ∀ e, L.single e = single e) (e : PoolNewEdge) :
    S.single e.val = L.single (poolNewEdgeEmbedding k e) :=
  (hS e.val).trans ((poolExtendedEdge_single k e.val).symm.trans (hL _).symm)

/-- Copy the two new vertices and the selected new edges from the pool witness. -/
def withPoolParameters (hS : ∀ e, S.single e = single e)
    (hL : ∀ e, L.single e = single e) : Parameters K ((10 + 2 * k) + 2) where
  single := L.single
  vertexSlope := Function.extend (poolNewVertexEmbedding k)
    (fun b => S.vertexSlope (Fin.natAdd 10 b)) L.vertexSlope
  vertexHeight := Function.extend (poolNewVertexEmbedding k)
    (fun b => S.vertexHeight (Fin.natAdd 10 b)) L.vertexHeight
  edgeSlope := Function.extend (poolNewEdgeEmbedding k) (S.edgeSlope ∘ Subtype.val) L.edgeSlope
  edgeHeight := Function.extend (poolNewEdgeEmbedding k) (S.edgeHeight ∘ Subtype.val) L.edgeHeight
  edgeLambda := Function.extend (poolNewEdgeEmbedding k) (S.edgeLambda ∘ Subtype.val) L.edgeLambda
  vertexSlope_ne := extend_valid (poolNewVertexEmbedding k)
    (fun b => S.vertexSlope (Fin.natAdd 10 b)) L.vertexSlope (fun _ a => a 0 ≠ a 1)
    (fun b => S.vertexSlope_ne (Fin.natAdd 10 b)) L.vertexSlope_ne
  vertexHeight_ne := extend_valid (poolNewVertexEmbedding k)
    (fun b => S.vertexHeight (Fin.natAdd 10 b)) L.vertexHeight (fun _ a => ∀ d, a d ≠ 0)
    (fun b => S.vertexHeight_ne (Fin.natAdd 10 b)) L.vertexHeight_ne
  edgeSlope_ne := extend_valid (poolNewEdgeEmbedding k) (S.edgeSlope ∘ Subtype.val) L.edgeSlope
    (fun e a => L.single e = false → a 0 ≠ a 1)
    (fun e he => S.edgeSlope_ne e.val ((poolNewEdge_single S L hS hL e).trans he)) L.edgeSlope_ne
  edgeHeight_ne := extend_valid (poolNewEdgeEmbedding k) (S.edgeHeight ∘ Subtype.val) L.edgeHeight
    (fun _ a => ∀ d, a d ≠ 0) (fun e => S.edgeHeight_ne e.val) L.edgeHeight_ne
  edgeLambda_ne := extend_valid (poolNewEdgeEmbedding k) (S.edgeLambda ∘ Subtype.val) L.edgeLambda
    (fun _ a => a ≠ 0) (fun e => S.edgeLambda_ne e.val) L.edgeLambda_ne

variable (hS : ∀ e, S.single e = single e) (hL : ∀ e, L.single e = single e)

@[simp] theorem withPoolParameters_single (e : Edge ((10 + 2 * k) + 2)) :
    (withPoolParameters S L hS hL).single e = L.single e := rfl

/-- Vertex data outside the patched image remain unchanged. -/
theorem withPoolParameters_vertex_eq_off {i : Fin ((10 + 2 * k) + 2)}
    (hi : i ∉ Set.range (poolNewVertexEmbedding k)) :
    (withPoolParameters S L hS hL).vertexSlope i = L.vertexSlope i ∧
      (withPoolParameters S L hS hL).vertexHeight i = L.vertexHeight i :=
  ⟨Function.extend_apply' (fun b : Fin 2 => S.vertexSlope (Fin.natAdd 10 b)) L.vertexSlope i hi,
    Function.extend_apply' (fun b : Fin 2 => S.vertexHeight (Fin.natAdd 10 b)) L.vertexHeight i hi⟩

/-- Edge data outside the patched image remain unchanged. -/
theorem withPoolParameters_edge_eq_off {e : Edge ((10 + 2 * k) + 2)}
    (he : e ∉ Set.range (poolNewEdgeEmbedding k)) :
    (withPoolParameters S L hS hL).edgeLambda e = L.edgeLambda e ∧
      (withPoolParameters S L hS hL).edgeSlope e = L.edgeSlope e ∧
      (withPoolParameters S L hS hL).edgeHeight e = L.edgeHeight e :=
  ⟨Function.extend_apply' _ _ _ he, Function.extend_apply' _ _ _ he, Function.extend_apply' _ _ _ he⟩

/-- Every old vertex retains its original slope and height parameters. -/
theorem withPoolParameters_vertex_eq_of_old {i : Fin ((10 + 2 * k) + 2)}
    (hi : i.val < 10 + 2 * k) :
    (withPoolParameters S L hS hL).vertexSlope i = L.vertexSlope i ∧
      (withPoolParameters S L hS hL).vertexHeight i = L.vertexHeight i := by
  apply withPoolParameters_vertex_eq_off
  rintro ⟨b, rfl⟩
  exact (not_lt_of_ge (poolNewVertexEmbedding_lower k b)) hi

/-- Every edge contained in the old graph retains its original parameters. -/
theorem withPoolParameters_edge_eq_of_old {e : Edge ((10 + 2 * k) + 2)}
    (he : e.val.2.val < 10 + 2 * k) :
    (withPoolParameters S L hS hL).edgeLambda e = L.edgeLambda e ∧
      (withPoolParameters S L hS hL).edgeSlope e = L.edgeSlope e ∧
      (withPoolParameters S L hS hL).edgeHeight e = L.edgeHeight e := by
  apply withPoolParameters_edge_eq_off
  rintro ⟨e, rfl⟩
  exact (not_lt_of_ge (poolNewEdgeEmbedding_lower k e)) he

/-- Agreement on the initial ten vertices and their internal edges. -/
structure PoolPrefixAgreement : Prop where
  vertex_eq (c : Fin 12) (hc : c.val < 10) :
    S.vertexSlope c = L.vertexSlope (poolExtendedEmbedding k c) ∧
      S.vertexHeight c = L.vertexHeight (poolExtendedEmbedding k c)
  edge_eq (e : Edge 12) (he : e.val.2.val < 10) :
    S.edgeLambda e = L.edgeLambda (poolExtendedEdge k e) ∧
      S.edgeSlope e = L.edgeSlope (poolExtendedEdge k e) ∧
      S.edgeHeight e = L.edgeHeight (poolExtendedEdge k e)

private theorem withPoolParameters_agrees_vertex (hold : PoolPrefixAgreement S L) (c : Fin 12) :
    S.vertexSlope c = (withPoolParameters S L hS hL).vertexSlope (poolExtendedEmbedding k c) ∧
      S.vertexHeight c = (withPoolParameters S L hS hL).vertexHeight (poolExtendedEmbedding k c) := by
  refine Fin.addCases (m := 10) (n := 2) (fun i => ?_) (fun b => ?_) c
  · have hi : (poolExtendedEmbedding k (Fin.castAdd 2 i)).val < 10 + 2 * k := by
      rw [poolExtendedEmbedding_old]
      change i.val < 10 + 2 * k
      have hi := i.isLt
      omega
    have h₀ := hold.vertex_eq (Fin.castAdd 2 i) i.isLt
    have h₁ := withPoolParameters_vertex_eq_of_old S L hS hL hi
    exact ⟨h₀.1.trans h₁.1.symm, h₀.2.trans h₁.2.symm⟩
  · exact ⟨((poolNewVertexEmbedding k).injective.extend_apply
      (fun b => S.vertexSlope (Fin.natAdd 10 b)) L.vertexSlope b).symm,
      ((poolNewVertexEmbedding k).injective.extend_apply
        (fun b => S.vertexHeight (Fin.natAdd 10 b)) L.vertexHeight b).symm⟩

/-- The patched cone agrees with the base witness at every lift center. -/
theorem agreesAt_withPoolParameters (hold : PoolPrefixAgreement S L) (c : Fin 12) :
    AgreesAt S (withPoolParameters S L hS hL)
      (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) c := by
  obtain ⟨hs, hh⟩ := withPoolParameters_agrees_vertex S L hS hL hold c
  refine ⟨hs, hh, ?_⟩
  intro e _
  have hsingle : S.single e = L.single (poolExtendedEdge k e) :=
    (hS e).trans ((poolExtendedEdge_single k e).symm.trans (hL _).symm)
  refine ⟨hsingle, ?_⟩
  by_cases he : e.val.2.val < 10
  · have he' : (poolExtendedEdge k e).val.2.val < 10 + 2 * k := by
      change (poolExtendedEmbedding k e.val.2).val < 10 + 2 * k
      rw [poolExtendedEmbedding_val, ite_eq_left he]
      omega
    have h₀ := hold.edge_eq e he
    have h₁ := withPoolParameters_edge_eq_of_old S L hS hL he'
    exact ⟨h₀.1.trans h₁.1.symm, h₀.2.1.trans h₁.2.1.symm, h₀.2.2.trans h₁.2.2.symm⟩
  · let a : PoolNewEdge := ⟨e, not_lt.mp he⟩
    exact ⟨((poolNewEdgeEmbedding k).injective.extend_apply
      (S.edgeLambda ∘ Subtype.val) L.edgeLambda a).symm,
      ((poolNewEdgeEmbedding k).injective.extend_apply
        (S.edgeSlope ∘ Subtype.val) L.edgeSlope a).symm,
      ((poolNewEdgeEmbedding k).injective.extend_apply
        (S.edgeHeight ∘ Subtype.val) L.edgeHeight a).symm⟩

/-- Patching the pool witness preserves compatibility with any old cone. -/
theorem withPoolParameters_compatible {P : Parameters K (10 + 2 * k)} (h : Compatible P L) :
    Compatible P (withPoolParameters S L hS hL) where
  single_eq := h.single_eq
  vertexSlope_eq i d := (congrFun (withPoolParameters_vertex_eq_of_old S L hS hL
    (i := Fin.castAdd 2 i) i.isLt).1 d).trans (h.vertexSlope_eq i d)
  vertexHeight_eq i d := (congrFun (withPoolParameters_vertex_eq_of_old S L hS hL
    (i := Fin.castAdd 2 i) i.isLt).2 d).trans (h.vertexHeight_eq i d)
  edgeSlope_eq e d := (congrFun (withPoolParameters_edge_eq_of_old S L hS hL
    (e := oldEdge _ e) e.val.2.isLt).2.1 d).trans (h.edgeSlope_eq e d)
  edgeHeight_eq e d := (congrFun (withPoolParameters_edge_eq_of_old S L hS hL
    (e := oldEdge _ e) e.val.2.isLt).2.2 d).trans (h.edgeHeight_eq e d)
  edgeLambda_eq e := (withPoolParameters_edge_eq_of_old S L hS hL
    (e := oldEdge _ e) e.val.2.isLt).1.trans (h.edgeLambda_eq e)

end IdealGeneration.CubicSupported.B5
