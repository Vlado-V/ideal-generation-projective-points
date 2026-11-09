module

public import IdealGeneration.CubicB11Values
public import IdealGeneration.CubicPureLocality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Transporting the initial-pool probes and columns to every later pair step. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicMixedLocality

/-- Retain each of the ten initial trace coordinates. -/
def poolOldEmbedding (k : ℕ) : Fin 10 ↪ Fin (10 + 2 * k) :=
  Fin.castLEEmb (by omega)

private def poolExtendedIndex (k : ℕ) (i : Fin 12) : Fin ((10 + 2 * k) + 2) :=
  ⟨if i.val < 10 then i.val else i.val + 2 * k, by split_ifs <;> omega⟩

private theorem poolExtendedIndex_strictMono (k : ℕ) : StrictMono (poolExtendedIndex k) := by
  intro i j hij
  have h : i.val < j.val := hij
  change (if i.val < 10 then i.val else i.val + 2 * k) <
    (if j.val < 10 then j.val else j.val + 2 * k)
  split_ifs <;> omega

/-- Retain the pool and send its two extension coordinates to the current new pair. -/
def poolExtendedEmbedding (k : ℕ) : Fin 12 ↪ Fin ((10 + 2 * k) + 2) :=
  ⟨poolExtendedIndex k, (poolExtendedIndex_strictMono k).injective⟩

theorem poolExtendedEmbedding_strictMono (k : ℕ) : StrictMono (poolExtendedEmbedding k) :=
  poolExtendedIndex_strictMono k

@[simp] theorem poolExtendedEmbedding_old (k : ℕ) (i : Fin 10) :
    poolExtendedEmbedding k (Fin.castAdd 2 i) = Fin.castAdd 2 (poolOldEmbedding k i) := by
  apply Fin.ext
  change (if i.val < 10 then i.val else i.val + 2 * k) = i.val
  simp [i.isLt]

@[simp] theorem poolExtendedEmbedding_new (k : ℕ) (b : Fin 2) :
    poolExtendedEmbedding k (Fin.natAdd 10 b) = Fin.natAdd (10 + 2 * k) b := by
  apply Fin.ext
  change (if 10 + b.val < 10 then 10 + b.val else 10 + b.val + 2 * k) = 10 + 2 * k + b.val
  split_ifs <;> omega

theorem poolOldEmbedding_strictMono (k : ℕ) : StrictMono (poolOldEmbedding k) :=
  fun _ _ h => h

private theorem poolNeighbor_iff (k : ℕ) (b : Fin 2) (i : Fin 10) :
    neighbor b (poolOldEmbedding k i) ↔ neighbor b i := by
  fin_cases b <;> change singleLabels i.val ((10 + 2 * k) + _) ↔ singleLabels i.val (10 + _) <;>
    unfold singleLabels <;> omega

private def poolOldEdge (k : ℕ) (e : Edge 10) : Edge (10 + 2 * k) :=
  edgeImage (poolOldEmbedding k) (poolOldEmbedding_strictMono k) e

private theorem poolOldEdge_fst (k : ℕ) (e : Edge 10) :
    (poolOldEdge k e).val.1 = poolOldEmbedding k e.val.1 := rfl

private theorem poolOldEdge_snd (k : ℕ) (e : Edge 10) :
    (poolOldEdge k e).val.2 = poolOldEmbedding k e.val.2 := rfl

private theorem poolOldEdge_single (k : ℕ) (e : Edge 10) :
    single (poolOldEdge k e) = single e := rfl

/-- The lower columns from the initial pool remain the same graph labels at later steps. -/
def embedPoolColumn (k : ℕ) : B7Column 10 → B7Column (10 + 2 * k)
  | .localColumn b (.inl e) => .localColumn b (.inl ⟨poolOldEdge k e.val,
      (poolOldEdge_single k e.val).trans e.property⟩)
  | .localColumn b (.inr (i, j)) => .localColumn b (.inr
      (⟨poolOldEmbedding k i.val, (poolNeighbor_iff k b i.val).mpr i.property⟩,
        poolOldEmbedding k j))
  | .motion b i q => .motion b (poolOldEmbedding k i) q
  | .extra b i u => .extra b ⟨poolOldEmbedding k i.val, (poolNeighbor_iff k b i.val).mpr i.property⟩ u
  | .remaining b u q => .remaining b u q

/-- Embedding a pool column never changes its owner. -/
theorem embedPoolColumn_owner (k : ℕ) (c : B7Column 10) :
    b7Owner (embedPoolColumn k c) = none := by
  cases c with
  | localColumn b c =>
      rcases c with e | ⟨i, j⟩
      · change faceOwner (localFace (.inl _ : LocalColumn (10 + 2 * k) b)) = none
        rw [localFace_old, faceOwner_eq_none]
        intro v hv
        have he : v = poolOldEmbedding k e.val.val.1 ∨ v = poolOldEmbedding k e.val.val.2 := by
          simpa [faceVertices, poolOldEdge, edgeImage] using hv
        rcases he with rfl | rfl
        · exact e.val.val.1.isLt
        · exact e.val.val.2.isLt
      · change faceOwner (monomialFace (poolOldEmbedding k i.val) (poolOldEmbedding k j)) = none
        rw [faceOwner_eq_none]
        intro v hv
        unfold monomialFace at hv
        split at hv
        · simp only [faceVertices, Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact i.val.isLt
          · exact j.isLt
        · split at hv
          · simp only [faceVertices, Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact j.isLt
            · exact i.val.isLt
          · simp only [faceVertices, Finset.mem_singleton] at hv
            subst v
            exact i.val.isLt
  | motion b i q => exact (vertexOwner_eq_none _).mpr i.isLt
  | extra b i u => exact (vertexOwner_eq_none _).mpr i.val.isLt
  | remaining b u q => rfl

section Values

open CubicPureLocality
open QuadraticTraceRestriction (extendPoint extendPoint_embedded extendPoint_off sum_over_embedding)

variable {K : Type*} [Field K] {k : ℕ}
variable {P : Parameters K 12} {L : Parameters K ((10 + 2 * k) + 2)}
variable (agree : ∀ c, AgreesAt P L (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) c)

include agree in
private theorem oldLinearValue_pool (c : Fin 12) (a : Fin 3 → K) (y : Fin 10 → K) (r : Fin 2) :
    oldLinearValue L (poolExtendedEmbedding k c) a (extendPoint K (poolOldEmbedding k) y) r =
      oldLinearValue P c a y r := by
  unfold oldLinearValue
  rw [sum_over_embedding (poolOldEmbedding k) _ (fun j hj => by
    rw [extendPoint_off K (poolOldEmbedding k) y hj, mul_zero])]
  apply Finset.sum_congr rfl
  intro i _
  rw [extendPoint_embedded, ← poolExtendedEmbedding_old]
  rw [← congrFun (mixedLinear_eq_of_agreesAt (agree c) a (Fin.castAdd 2 i)) r]

include agree in
private theorem oldPureValue_pool (a : Fin 4 → K) (y : Fin 10 → K) (r : Fin 2) :
    oldPureValue L a (extendPoint K (poolOldEmbedding k) y) r = oldPureValue P a y r := by
  unfold oldPureValue
  dsimp only
  rw [sum_over_embedding (poolOldEmbedding k) _ (fun j hj => by
    simp [extendPoint_off K (poolOldEmbedding k) y hj])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_over_embedding (poolOldEmbedding k) _ (fun j hj => by
    rw [extendPoint_off K (poolOldEmbedding k) y hj, mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [extendPoint_embedded, extendPoint_embedded, ← poolExtendedEmbedding_old,
    ← poolExtendedEmbedding_old]
  rw [← pureCubic_upperCoefficient_eq a (Fin.castAdd 2 i) (Fin.castAdd 2 j) r
    (agree (Fin.castAdd 2 i)) (agree (Fin.castAdd 2 j))]

include agree in
private theorem oldRemainingValue_pool (c : Fin 12) (u : Fin 2) (a : Fin 3 → K)
    (y : Fin 10 → K) (r : Fin 2) :
    oldRemainingValue L (poolExtendedEmbedding k c) u a (extendPoint K (poolOldEmbedding k) y) r =
      oldRemainingValue P c u a y r := by
  unfold oldRemainingValue
  rw [oldPureValue_pool agree]
  congr 1
  rw [sum_over_embedding (poolOldEmbedding k) _ (fun j hj => by
    rw [extendPoint_off K (poolOldEmbedding k) y hj, zero_mul])]
  apply Finset.sum_congr rfl
  intro i _
  rw [extendPoint_embedded, ← poolExtendedEmbedding_old]
  rw [← mixedLinear_eq_of_agreesAt (agree c) a (Fin.castAdd 2 i), oldLinearValue_pool agree]

private theorem oldSlopeEdge_pool (e : Edge 10) :
    edgeImage (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) (oldSlopeEdge e) =
      oldSlopeEdge (poolOldEdge k e) := by
  apply Subtype.ext
  exact Prod.ext (poolExtendedEmbedding_old k e.val.1) (poolExtendedEmbedding_old k e.val.2)

private theorem newSlopeEdge_pool (b : Fin 2) (i : Fin 10) :
    edgeImage (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) (newSlopeEdge b i) =
      newSlopeEdge b (poolOldEmbedding k i) := by
  apply Subtype.ext
  exact Prod.ext (poolExtendedEmbedding_old k i) (poolExtendedEmbedding_new k b)

include agree in
private theorem poolSlope_eq (e : Edge 12) :
    P.edgeSlope e = L.edgeSlope (edgeImage (poolExtendedEmbedding k) (poolExtendedEmbedding_strictMono k) e) :=
  ((agree e.val.1).edge_eq e (Or.inl rfl)).2.2.1

include agree in
/-- Every actual pool entry is invariant under agreement on the pool and current new pair. -/
theorem b7Value_poolTransport (y : Fin 10 → K) (w : Fin 2 → K) (r : Fin 2) (c : B7Column 10) :
    b7Value (actualB7Data L) (extendPoint K (poolOldEmbedding k) y) w r (embedPoolColumn k c) =
      b7Value (actualB7Data P) y w r c := by
  rw [b7Value_actual_eq_oldValue, b7Value_actual_eq_oldValue]
  cases c with
  | localColumn b c =>
      rcases c with e | ⟨i, j⟩
      · simp only [embedPoolColumn, b7OldValue, localValue, localEndpoints, localSlopeEdge,
          poolOldEdge_fst, poolOldEdge_snd, extendPoint_embedded]
        rw [← oldSlopeEdge_pool, ← poolSlope_eq agree]
      · simp only [embedPoolColumn, b7OldValue, localValue, localEndpoints, localSlopeEdge,
          extendPoint_embedded]
        rw [← newSlopeEdge_pool, ← poolSlope_eq agree]
  | motion b i q =>
      simp only [embedPoolColumn, b7OldValue, extendPoint_embedded]
      rw [← poolExtendedEmbedding_new, ← poolExtendedEmbedding_old,
        oldLinearValue_pool agree, oldLinearValue_pool agree]
  | extra b i u =>
      simp only [embedPoolColumn, b7OldValue, extendPoint_embedded]
      have hs : crossNormal L b (poolOldEmbedding k i.val) = crossNormal P b i.val := by
        unfold crossNormal
        change ![L.edgeSlope (newSlopeEdge b (poolOldEmbedding k i.val)) 0, -1] =
          ![P.edgeSlope (newSlopeEdge b i.val) 0, -1]
        rw [← newSlopeEdge_pool, ← poolSlope_eq agree]
      rw [hs, ← poolExtendedEmbedding_new, oldLinearValue_pool agree]
  | remaining b u q =>
      simp only [embedPoolColumn, b7OldValue]
      rw [← poolExtendedEmbedding_new, oldRemainingValue_pool agree]

end Values
end IdealGeneration.CubicSupported.B5
