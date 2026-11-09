module

public import IdealGeneration.TripleNormalBaseColumns
public import IdealGeneration.TripleNormalBaseEdgeExpansion
public import IdealGeneration.TripleNormalNewBaseRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Convert the normalized interpolation columns to the actual base coefficient test. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open EdgeOrder NormalizedEdgeColumns BaseEdgeExpansion Matrix MvPolynomial

variable {K : Type*} [Field K] {N : ℕ}

private abbrev BaseTable (K : Type*) (N : ℕ) :=
  Fin (N + 3 + 3 + 4) → Fin (N + 3 + 3) → K

private def oldNewEdge (i : Fin (N + 3)) (b : Fin 3) : Edge N :=
  Fin.addCases (fun j => .inl (j, b)) (fun r => rootEdge r b) i

@[simp] private theorem oldNewEdge_endpoints (i : Fin (N + 3)) (b : Fin 3) :
    edgeEndpoints (oldNewEdge i b) = (i.castAdd 3, b.natAdd (N + 3)) := by
  refine Fin.addCases (fun j => ?_) (fun r => ?_) i <;>
    simp [oldNewEdge, edgeEndpoints, rootEdge, nonrootBaseIndex, rootBaseIndex, newEdgeBaseIndex]

private def rawBaseInput (u : Fin 3 → Fin 3 → K) (ρ : BaseTable K N) : RawInput K N :=
  (u, fun e k =>
    if k = 0 then ρ ((edgeEndpoints e).2.castAdd 4) (edgeEndpoints e).1
    else ρ ((edgeEndpoints e).1.castAdd 4) (edgeEndpoints e).2)

private def edgePointValue (y : Fin (N + 3 + 3) → K) (a : Fin 3) : Output K N →ₗ[K] K where
  toFun f := ∑ e, y (edgeEndpoints e).1 * y (edgeEndpoints e).2 * f e a
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    change (∑ e : Edge N, y (edgeEndpoints e).1 * y (edgeEndpoints e).2 * (c * f e a)) =
      c * ∑ e : Edge N, y (edgeEndpoints e).1 * y (edgeEndpoints e).2 * f e a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

private theorem eval_edgeQuadric_eq_edgePointValue (y : Fin (N + 3 + 3) → K)
    (a : Fin 3) (f : Output K N) :
    eval y (edgeQuadric edgeEndpoints f a) = edgePointValue y a f := by
  change eval y (edgeQuadric edgeEndpoints f a) =
    ∑ e, y (edgeEndpoints e).1 * y (edgeEndpoints e).2 * f e a
  rw [edgeQuadric, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [map_mul, eval_C, eval_X]
  ring

private theorem rawBaseInput_zero (u : Fin 3 → Fin 3 → K) (ρ : BaseTable K N)
    (hold : ∀ i j : Fin (N + 3), ρ ((i.castAdd 3).castAdd 4) (j.castAdd 3) = 0)
    (hdiag : ∀ b : Fin 3, ρ ((b.natAdd (N + 3)).castAdd 4) (b.natAdd (N + 3)) = 0)
    (h : rawBaseInput u ρ = 0) :
    u = 0 ∧ ∀ j : Fin (N + 3 + 3), ρ (j.castAdd 4) = 0 := by
  have hp (e : Edge N) (k : Fin 2) : (rawBaseInput u ρ).2 e k = 0 :=
    congrFun (congrFun (congrArg Prod.snd h) e) k
  refine ⟨congrArg Prod.fst h, fun j => ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · refine Fin.addCases (fun i => hold j i) (fun c => ?_) i
    simpa [rawBaseInput] using hp (oldNewEdge j c) 1
  · refine Fin.addCases (fun i => ?_) (fun c => ?_) i
    · simpa [rawBaseInput] using hp (oldNewEdge i b) 0
    · rcases lt_trichotomy b c with hbc | hbc | hcb
      · let e : TriangleEdge := ⟨(b, c), hbc⟩
        simpa [rawBaseInput, edgeEndpoints, e, newEdgeBaseIndex] using hp (.inr (.inl e)) 1
      · subst c
        exact hdiag b
      · let e : TriangleEdge := ⟨(c, b), hcb⟩
        simpa [rawBaseInput, edgeEndpoints, e, newEdgeBaseIndex] using hp (.inr (.inl e)) 0

private theorem edgePointValue_rawBaseInput (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (u : Fin 3 → Fin 3 → K) (ρ : BaseTable K N)
    (hold : ∀ i j : Fin (N + 3), ρ ((i.castAdd 3).castAdd 4) (j.castAdd 3) = 0)
    (hdiag : ∀ b : Fin 3, ρ ((b.natAdd (N + 3)).castAdd 4) (b.natAdd (N + 3)) = 0)
    (y : Fin (N + 3 + 3) → K) (a : Fin 3) :
    edgePointValue y a (rawCoefficient ω t v (rawBaseInput u ρ)) = newBaseValue ω t v u ρ y a := by
  let W : Fin (N + 3 + 3) → Fin 3 → K := fun i => conicVector (Fin.append t v i)
  let A : Fin (N + 3 + 3) → Fin 3 → Fin 3 → K :=
    fun i b => baseLiftCoefficient ω (Fin.append t v i) (newMotionQuadric v u b)
  have hA (b : Fin 3) : A (b.natAdd (N + 3)) b a = 0 := by
    simpa [A, newMotionQuadric] using congrFun
      (baseLiftCoefficient_motionQuadratic_diagonal ω (v b) hω (u b)) a
  have hnon (i : Fin N) (b : Fin 3) :
      rawCoefficient ω t v (rawBaseInput u ρ) (.inl (i, b)) a =
        oldNewCoefficient W A ρ (i.castAdd 3) b a := by
    have he := congrFun (rawCoefficient_nonroot ω t v (rawBaseInput u ρ) i b) a
    simpa [rawBaseInput, edgeEndpoints, nonrootBaseIndex, newEdgeBaseIndex, oldNewCoefficient,
      W, A, newMotionQuadric] using he
  have hroot (r b : Fin 3) :
      rawCoefficient ω t v (rawBaseInput u ρ) (rootEdge r b) a =
        oldNewCoefficient W A ρ (r.natAdd N) b a := by
    have he := congrFun (rawCoefficient_root ω t v (rawBaseInput u ρ) r b) a
    simpa [rawBaseInput, edgeEndpoints, rootEdge, rootBaseIndex, newEdgeBaseIndex,
      oldNewCoefficient, rootParameters, W, A, newMotionQuadric] using he
  have htriangle (e : TriangleEdge) :
      rawCoefficient ω t v (rawBaseInput u ρ) (.inr (.inl e)) a =
        triangleCoefficient W A ρ e a := by
    have he := congrFun (rawCoefficient_triangle ω t v (rawBaseInput u ρ) e) a
    simpa [rawBaseInput, edgeEndpoints, newEdgeBaseIndex, triangleCoefficient, W, A,
      newMotionQuadric, sub_sub] using he
  change edgePointValue y a (rawCoefficient ω t v (rawBaseInput u ρ)) =
    -(∑ b : Fin 3, y (b.natAdd (N + 3)) * ∑ i, y i * A i b a) +
      ∑ j, y j * ∑ i, y i * (ρ (j.castAdd 4) i * W i a)
  rw [base_edge_expansion W A ρ y a hold hA]
  simp only [hdiag, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  change (∑ e, y (edgeEndpoints e).1 * y (edgeEndpoints e).2 *
    rawCoefficient ω t v (rawBaseInput u ρ) e a) = _
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, edgeEndpoints, nonrootBaseIndex,
    rootBaseIndex, newEdgeBaseIndex, hnon, htriangle] 
  rw [Fin.sum_univ_add]
  simp_rw [show ∀ r b, rawCoefficient ω t v (rawBaseInput u ρ) (.inr (.inr (r,b))) a =
    oldNewCoefficient W A ρ (r.natAdd N) b a from hroot]
  abel

variable [CharZero K]
  (ω : K) (t : Fin (N + 3) → K) (v : Fin 3 → K)
  (hω : IsPrimitiveRoot ω 3) (hroots : ∀ r, rootParameters t r ≠ 0)
  (hinj : Function.Injective (rootParameters t))
  (hq : ∀ r b, chordFactor (rootParameters t r) (v b) ≠ 0)

local notation "E" => recoverEquiv ω t v hω hroots hinj hq
local notation "L" => normalizedCoefficient ω t v hω hroots hinj hq

/-- Injectivity of the normalized interpolation matrix is the actual base
rank needed by the new-source kernel test. -/
theorem newBaseRank_of_groupedBaseColumn_injective (hN : 5 ≤ N)
    (free : Fin (2 * (N + 3) + 5) × Fin (N + 3 + 3) → K)
    (hi : Function.Injective
      (freeTraceMatrix (groupedFreePointIndex N) groupedEvalCoordinate
        (fun j => edgeQuadric edgeEndpoints (groupedBaseColumn ω t v hω hroots hinj hq hN j))
        free).mulVec) :
    NewBaseRank ω t v free := by
  intro u ρ hold hdiag heval
  let raw := rawBaseInput u ρ
  let x := (E).symm raw
  let c := groupedBaseCoordinates hN x
  have hsum : ∑ j, c j • groupedBaseColumn ω t v hω hroots hinj hq hN j =
      rawCoefficient ω t v raw := by
    calc
      _ = L (∑ j, c j • groupedBaseBasis hN j) := by
        simp only [map_sum, map_smul, groupedBaseColumn]
      _ = L x := congrArg (L) (groupedBaseBasis_expansion hN x)
      _ = _ := by
        change rawCoefficient ω t v ((E) x) = _
        rw [LinearEquiv.apply_symm_apply]
  have hM : (freeTraceMatrix (groupedFreePointIndex N) groupedEvalCoordinate
      (fun j => edgeQuadric edgeEndpoints (groupedBaseColumn ω t v hω hroots hinj hq hN j))
      free).mulVec c = 0 := by
    funext i
    let y : Fin (N + 3 + 3) → K := fun j => free (groupedFreePointIndex N i, j)
    let a := groupedEvalCoordinate i
    let φ := edgePointValue y a
    have hsum' := congrArg (φ) hsum
    simp only [map_sum, map_smul, smul_eq_mul] at hsum'
    change (∑ j, eval y
      (edgeQuadric edgeEndpoints (groupedBaseColumn ω t v hω hroots hinj hq hN j) a) * c j) = 0
    simp_rw [eval_edgeQuadric_eq_edgePointValue, mul_comm _ (c _)]
    rw [show (∑ j, c j * edgePointValue y a
        (groupedBaseColumn ω t v hω hroots hinj hq hN j)) =
        edgePointValue y a (rawCoefficient ω t v raw) from hsum']
    change edgePointValue y a (rawCoefficient ω t v (rawBaseInput u ρ)) = 0
    rw [edgePointValue_rawBaseInput ω t v hω u ρ hold hdiag]
    exact heval (groupedFreePointIndex N i) a
  have hc : c = 0 := hi (by simpa only [Matrix.mulVec_zero] using hM)
  have hx : x = 0 := by
    rw [← groupedBaseBasis_expansion hN x]
    change (∑ j, c j • groupedBaseBasis hN j) = 0
    simp [hc]
  have hraw : raw = 0 := by
    have he : (E) x = raw := (E).apply_symm_apply raw
    rw [← he, hx, map_zero]
  exact rawBaseInput_zero u ρ hold hdiag hraw

include hω hroots hinj hq in
/-- The actual new base rank holds on a nonempty principal open. -/
theorem newBaseRank_principal_open (hN : 5 ≤ N)
    (hparams : Function.Injective (Fin.append t v))
    (hchords : ∀ g, (chordMatrix t v (orderedChordTriple hN (nonrootEmbedding N) g)).det ≠ 0) :
    ∃ P : MvPolynomial (Fin (2 * (N + 3) + 5) × Fin (N + 3 + 3)) K,
      (∃ a, MvPolynomial.eval a P ≠ 0) ∧
      ∀ a, MvPolynomial.eval a P ≠ 0 → NewBaseRank ω t v a := by
  obtain ⟨P, hP, hPg⟩ := groupedBaseColumn_principal_open ω t v hω hroots hinj hq hN hparams hchords
  exact ⟨P, hP, fun a ha =>
    newBaseRank_of_groupedBaseColumn_injective ω t v hω hroots hinj hq hN a (hPg a ha)⟩

end IdealGeneration.TripleNormal
