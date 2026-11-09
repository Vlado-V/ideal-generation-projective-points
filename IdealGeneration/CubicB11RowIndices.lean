module

public import IdealGeneration.CubicPairCoreColumns
public import IdealGeneration.CubicB4RankTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The B.5 lower rows come in pairs at actual moving trace probes. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open B4

variable {K : Type*} [Field K] {k : ℕ} {I J : Type*}

/-- The probe labels of the pool and all of the old pairs. -/
abbrev B11PointIndex (I : Type*) (k : ℕ) :=
  I ⊕ (Σ j : Fin k, Fin 13 ⊕ PairFullFace k j)

/-- The scalar row labels of the literal block matrix. -/
abbrev B11ScalarIndex (J : Type*) (k : ℕ) :=
  J ⊕ (Σ j : Fin k, PairBlockIndex k j)

/-- Group the two scalar components of each pool, core, and full-face probe. -/
def b11RowPointEquiv (poolIndex : J ≃ I × Fin 2) :
    B11ScalarIndex J k ≃ B11PointIndex I k × Fin 2 where
  toFun
    | .inl j => (.inl (poolIndex j).1, (poolIndex j).2)
    | .inr ⟨j, .inl r⟩ => (.inr ⟨j, .inl (pairCoreRowEquiv r).1⟩, (pairCoreRowEquiv r).2)
    | .inr ⟨j, .inr (r, F)⟩ => (.inr ⟨j, .inr F⟩, r)
  invFun
    | (.inl i, r) => .inl (poolIndex.symm (i, r))
    | (.inr ⟨j, .inl i⟩, r) => .inr ⟨j, .inl (pairCoreRowEquiv.symm (i, r))⟩
    | (.inr ⟨j, .inr F⟩, r) => .inr ⟨j, .inr (r, F)⟩
  left_inv := by
    rintro (j | ⟨j, r | ⟨r, F⟩⟩)
    · change Sum.inl (poolIndex.symm (poolIndex j)) = _
      rw [Equiv.symm_apply_apply]
    · change Sum.inr (⟨j, Sum.inl (pairCoreRowEquiv.symm (pairCoreRowEquiv r))⟩ :
        Σ j : Fin k, PairBlockIndex k j) = _
      rw [Equiv.symm_apply_apply]
    · rfl
  right_inv := by
    rintro ⟨i | ⟨j, i | F⟩, r⟩
    · have hi := poolIndex.apply_symm_apply (i, r)
      simp [hi]
    · have hi := pairCoreRowEquiv.apply_symm_apply (i, r)
      simp [hi]
    · rfl

variable (D : ∀ j : Fin k, PairBlockData K k j)
variable (poolPoint : I → Fin (10 + 2 * k) → K) (poolWeight : I → Fin 2 → K)

/-- The trace-coordinate part of each actual moving probe. -/
def b11Point : B11PointIndex I k → Fin (10 + 2 * k) → K
  | .inl i => poolPoint i
  | .inr ⟨j, .inl i⟩ => (D j).point i
  | .inr ⟨j, .inr F⟩ => faceProbe F.val.2 ((D j).faceParameter F)

/-- The new-coordinate weights of each actual moving probe. -/
def b11Weight : B11PointIndex I k → Fin 2 → K
  | .inl i => poolWeight i
  | .inr ⟨j, .inl i⟩ => (D j).weight i
  | .inr ⟨_, .inr F⟩ => pureDirection F.val.1

/-- The column order of the assembled B.11 matrix. -/
def b11Column (R : PoolBlockData K (10 + 2 * k) J) :
    B11ScalarIndex J k → B7Column (10 + 2 * k) :=
  Sum.elim R.column (fun j => pairColumn (D j.fst) j.snd)

/-- The scalar row order of the assembled B.11 matrix. -/
def b11Probe (R : PoolBlockData K (10 + 2 * k) J) :
    B11ScalarIndex J k → B11Probe K (10 + 2 * k) :=
  Sum.elim R.probe (fun j => pairProbe (D j.fst) j.snd)

variable (poolIndex : J ≃ I × Fin 2)

theorem b11Probe_eq_point_components (R : PoolBlockData K (10 + 2 * k) J)
    (hpool : ∀ j, R.probe j = ⟨poolPoint (poolIndex j).1, poolWeight (poolIndex j).1, (poolIndex j).2⟩)
    (r : B11ScalarIndex J k) :
    b11Probe D R r = ⟨b11Point D poolPoint ((b11RowPointEquiv poolIndex) r).1,
      b11Weight D poolWeight ((b11RowPointEquiv poolIndex) r).1, ((b11RowPointEquiv poolIndex) r).2⟩ := by
  rcases r with r | ⟨j, r | ⟨r, F⟩⟩
  · exact hpool r
  · rfl
  · rfl

variable [Fintype I]

/-- Number of actual moving free supports in the pool-and-pair arrangement. -/
abbrev b11PointCount (I : Type*) [Fintype I] (k : ℕ) := Fintype.card (B11PointIndex I k)

def b11NearIndex : B11ScalarIndex J k ≃ Fin (b11PointCount I k) × Fin 2 :=
  (b11RowPointEquiv poolIndex).trans (Equiv.prodCongr (Fintype.equivFin _) (Equiv.refl _))

def b11NearPoint : Fin (b11PointCount I k) → Fin (10 + 2 * k) → K :=
  fun i => b11Point D poolPoint ((Fintype.equivFin (B11PointIndex I k)).symm i)

def b11NearWeight : Fin (b11PointCount I k) → Fin 2 → K :=
  fun i => b11Weight D poolWeight ((Fintype.equivFin (B11PointIndex I k)).symm i)

/-- B.4's paired-probe entry order gives exactly the B.5 matrix. -/
theorem b11Matrix_eq_nearEnumeration (P : B7Data K (10 + 2 * k))
    (R : PoolBlockData K (10 + 2 * k) J)
    (hpool : ∀ j, R.probe j = ⟨poolPoint (poolIndex j).1, poolWeight (poolIndex j).1, (poolIndex j).2⟩) :
    b11Matrix P R D = Matrix.of (fun i j => probeEntry P
      (nearEnumeration (b11NearPoint D poolPoint) (b11NearWeight D poolWeight) (b11NearIndex poolIndex) i)
      (b11Column D R j)) := by
  ext i j
  change probeEntry P (b11Probe D R i) (b11Column D R j) = _
  rw [b11Probe_eq_point_components D poolPoint poolWeight poolIndex R hpool]
  simp [nearEnumeration, b11NearIndex, b11NearPoint, b11NearWeight]


private theorem b7Owner_lt (c : B7Column (10 + 2 * k)) (j : ℕ)
    (hj : b7Owner c = some j) : j < k := by
  have hv (i : Fin (10 + 2 * k)) (h : vertexOwner i = some j) : j < k := by
    have hi := i.isLt
    rcases (vertexOwner_eq_some i j).mp h with hh | hh <;> omega
  cases c with
  | localColumn b c =>
      obtain ⟨i, _, hi⟩ := exists_vertex_of_faceOwner (localFace c) j hj
      exact hv i hi
  | motion b i q => exact hv i hj
  | extra b i u => exact hv i.val hj
  | remaining b u q => simp [b7Owner] at hj

omit [Fintype I] in
/-- Nonsingularity and pool coverage certify the exact enumeration of all B.7 columns. -/
def b11ColumnEquiv [Fintype J] [DecidableEq J] (P : B7Data K (10 + 2 * k))
    (R : PoolBlockData K (10 + 2 * k) J)
    (hD : ∀ j, (D j).coreColumn = canonicalPairCoreColumn j)
    (hpool : ∀ c, b7Owner c = none → c ∈ Set.range R.column)
    (hdet : (b11Matrix P R D).det ≠ 0) :
    B11ScalarIndex J k ≃ B7Column (10 + 2 * k) :=
  Equiv.ofBijective (b11Column D R) ⟨by
    intro i j hij
    apply (Matrix.linearIndependent_cols_of_det_ne_zero hdet).injective
    funext r
    change probeEntry P (b11Probe D R r) (b11Column D R i) =
      probeEntry P (b11Probe D R r) (b11Column D R j)
    rw [hij], by
    intro c
    cases hc : b7Owner c with
    | none =>
        obtain ⟨i, hi⟩ := hpool c hc
        exact ⟨.inl i, hi⟩
    | some j =>
        let i : Fin k := ⟨j, b7Owner_lt c j hc⟩
        obtain ⟨r, hr⟩ := (mem_range_pairColumn_iff (D i) (hD i) c).mpr hc
        exact ⟨.inr ⟨i, r⟩, hr⟩⟩

end IdealGeneration.CubicSupported.B5
