module

public import IdealGeneration.CubicB7RootData
public import IdealGeneration.CubicInitialStructured
public import IdealGeneration.CubicSupportedRestriction
public import IdealGeneration.CubicB11PoolTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The initial and extended C.2 certificates share their old cone parameters. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B7Root

open CubicInitial B5 CubicMixedLocality

set_option maxRecDepth 100000 in
private theorem root_old_vertex_values :
    ∀ (i : Fin 10) (d : Fin 2),
      slope (vertexConeIndex i d) = slopeNat (Fin.castAdd 2 i) (Fin.castAdd 2 i) d ∧
      height (vertexConeIndex i d) = heightNat (Fin.castAdd 2 i) (Fin.castAdd 2 i) d := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem root_old_edge_values :
    ∀ (e : Edge 10) (d : Fin 2),
      slope (edgeConeIndex e d) = slopeNat (Fin.castAdd 2 e.val.1) (Fin.castAdd 2 e.val.2) d ∧
      height (edgeConeIndex e d) = heightNat (Fin.castAdd 2 e.val.1) (Fin.castAdd 2 e.val.2) d := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem root_old_edge_scales :
    ∀ (e : Edge 10), edgeScale e = lambdaNat (Fin.castAdd 2 e.val.1) (Fin.castAdd 2 e.val.2) := by
  decide +kernel

/-- The two finite C.2 constructions retain exactly the same old primitive data. -/
theorem initialCompatible (K : Type*) [Field K] [CharZero K] :
    Compatible (initialGraph K) (parametersCharZero K) where
  single_eq _ := rfl
  vertexSlope_eq i d := congrArg (fun a : ℕ => (a : K)) (root_old_vertex_values i d).1.symm
  vertexHeight_eq i d := congrArg (fun a : ℕ => (a : K)) (root_old_vertex_values i d).2.symm
  edgeSlope_eq e d := congrArg (fun a : ℕ => (a : K)) (root_old_edge_values e d).1.symm
  edgeHeight_eq e d := congrArg (fun a : ℕ => (a : K)) (root_old_edge_values e d).2.symm
  edgeLambda_eq e := congrArg (fun a : ℕ => (a : K)) (root_old_edge_scales e).symm

variable {K : Type*} [Field K] [CharZero K]

/-- The initial-pool primitive data are retained at each stage of the pair construction. -/
def AgreesInitialPool {k : ℕ} (P : Parameters K (10 + 2 * k)) : Prop :=
  ∀ i, AgreesAt (initialGraph K) P (poolOldEmbedding k) (poolOldEmbedding_strictMono k) i

theorem initialGraph_agreesInitialPool : AgreesInitialPool (k := 0) (initialGraph K) := by
  intro i
  constructor
  · rfl
  · rfl
  · intro e _
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A compatible extension keeps the initial pool agreement. -/
theorem AgreesInitialPool.extend {k : ℕ} {P : Parameters K (10 + 2 * k)}
    {Q : Parameters K ((10 + 2 * k) + 2)}
    (hP : AgreesInitialPool P) (h : Compatible P Q) :
    AgreesInitialPool (k := k + 1) Q := by
  intro i
  have hv : poolOldEmbedding (k + 1) i = Fin.castAdd 2 (poolOldEmbedding k i) := Fin.ext rfl
  constructor
  · rw [hv]
    funext d
    rw [h.vertexSlope_eq]
    exact congrFun (hP i).vertexSlope_eq d
  · rw [hv]
    funext d
    rw [h.vertexHeight_eq]
    exact congrFun (hP i).vertexHeight_eq d
  · intro e hi
    have he : edgeImage (poolOldEmbedding (k + 1)) (poolOldEmbedding_strictMono (k + 1)) e =
        oldEdge (10 + 2 * k) (edgeImage (poolOldEmbedding k) (poolOldEmbedding_strictMono k) e) :=
      Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
    rw [he]
    obtain ⟨hs, hl, hv, hh⟩ := (hP i).edge_eq e hi
    refine ⟨hs.trans (h.single_eq _).symm, hl.trans (h.edgeLambda_eq _).symm, ?_, ?_⟩
    · funext d
      rw [h.edgeSlope_eq]
      exact congrFun hv d
    · funext d
      rw [h.edgeHeight_eq]
      exact congrFun hh d

end IdealGeneration.CubicSupported.B7Root
