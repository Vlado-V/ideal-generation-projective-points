module

public import IdealGeneration.CubicFaceAssignment
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Evaluation-block assembly for Appendix B.5

The local columns are the actual weighted monomials from (B.7). Motion and
extra columns carry their required vertex factor. Their lift-dependent
coefficients and the last family are inputs. The matrix is formed by evaluating
these columns, so proper-face and star contributions at full-face rows remain
in the lower-left block.
-/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

/-- The five families in (B.7), with a direction label on each column. -/
inductive B7Column (m : ℕ) where
  | localColumn (b : Fin 2) (c : LocalColumn m b)
  | motion (b : Fin 2) (i : Fin m) (q : Fin 3)
  | extra (b : Fin 2) (i : {i : Fin m // neighbor b i}) (u : Fin 2)
  | remaining (b u : Fin 2) (q : Fin 3)

/-- The pool owns the last family; a local column is owned by its exact face. -/
def b7Owner {m : ℕ} : B7Column m → Option ℕ
  | .localColumn _ c => faceOwner (localFace c)
  | .motion _ i _ => vertexOwner i
  | .extra _ i _ => vertexOwner i.val
  | .remaining _ _ _ => none

/-- The coefficient functions left after extracting the prescribed coordinate factors. -/
structure B7Data (K : Type*) [Field K] (m : ℕ) where
  cones : Parameters K (m + 2)
  motion : Fin 2 → Fin m → Fin 3 → (Fin m → K) → Fin 2 → K
  extra : Fin 2 → Fin m → Fin 2 → (Fin m → K) → Fin 2 → K
  remaining : Fin 2 → Fin 2 → Fin 3 → (Fin m → K) → Fin 2 → K

variable {K : Type*} [Field K] {m k : ℕ}

/-- The weighted normal-component value of a (B.7) column. -/
def b7Value (P : B7Data K m) (y : Fin m → K) (w : Fin 2 → K) (r : Fin 2) : B7Column m → K
  | .localColumn _ c => localValue P.cones c y w r
  | .motion b i q => w b * y i * P.motion b i q y r
  | .extra b i u => w b * y i.val * P.extra b i.val u y r
  | .remaining b u q => w b * P.remaining b u q y r

/-- Every pair column has a coordinate factor from its owning pair. -/
theorem b7Value_zero_of_owner (P : B7Data K m) (c : B7Column m) {j : ℕ}
    (hc : b7Owner c = some j) (y : Fin m → K)
    (hy : ∀ i, vertexOwner i = some j → y i = 0)
    (w : Fin 2 → K) (r : Fin 2) : b7Value P y w r c = 0 := by
  cases c with
  | localColumn b c => exact localValue_zero_of_owner P.cones c hc y hy w r
  | motion b i q => simp [b7Value, hy i hc]
  | extra b i u => simp [b7Value, hy i.val hc]
  | remaining b u q => simp [b7Owner] at hc

/-- An evaluation row consists of a trace point, direction weights and a normal component. -/
structure B11Probe (K : Type*) (m : ℕ) where
  point : Fin m → K
  weight : Fin 2 → K
  component : Fin 2

def probeEntry (P : B7Data K m) (r : B11Probe K m) (c : B7Column m) : K :=
  b7Value P r.point r.weight r.component c

/-- A full face of direction `b` assigned to pair `j`. -/
abbrev PairFullFace (k : ℕ) (j : Fin k) :=
  {p : Fin 2 × Face (10 + 2 * k) //
    faceOwner p.2 = some j.val ∧ (faceLocalColumns p.1 p.2).card = 2}

instance (j : Fin k) : Fintype (PairFullFace k j) := Fintype.ofFinite _

instance (j : Fin k) : DecidableEq (PairFullFace k j) := Classical.decEq _

/-- Enumerate the two exact-face columns of a full face. -/
def fullFaceEnumeration {j : Fin k} (F : PairFullFace k j) :
    Fin 2 ≃ {c : LocalColumn (10 + 2 * k) F.val.1 // c ∈ faceLocalColumns F.val.1 F.val.2} :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans F.property.2)).symm

def fullFaceColumn {j : Fin k} (F : PairFullFace k j) (i : Fin 2) :
    LocalColumn (10 + 2 * k) F.val.1 := (fullFaceEnumeration F i).val

@[simp] theorem fullFaceColumn_mem {j : Fin k} (F : PairFullFace k j) (i : Fin 2) :
    fullFaceColumn F i ∈ faceLocalColumns F.val.1 F.val.2 := (fullFaceEnumeration F i).property

@[simp] theorem fullFaceColumn_face {j : Fin k} (F : PairFullFace k j) (i : Fin 2) :
    localFace (fullFaceColumn F i) = F.val.2 :=
  (mem_faceLocalColumns _ _).mp (fullFaceColumn_mem F i)

theorem fullFaceColumn_injective {j : Fin k} (F : PairFullFace k j) :
    Function.Injective (fullFaceColumn F) :=
  fun _ _ h => (fullFaceEnumeration F).injective (Subtype.ext h)

private theorem fullFaceColumn_vec {j : Fin k} (F : PairFullFace k j) (i : Fin 2) :
    ![fullFaceColumn F 0, fullFaceColumn F 1] i = fullFaceColumn F i := by
  fin_cases i <;> rfl

/-- The twenty-six rows are the two components at each of thirteen points. -/
def pairCoreRowEquiv : Fin 26 ≃ Fin 13 × Fin 2 where
  toFun i := (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
  invFun p := ⟨2 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  left_inv i := by
    apply Fin.ext
    change 2 * (i.val / 2) + i.val % 2 = i.val
    omega
  right_inv p := by
    have hp := p.2.isLt
    apply Prod.ext <;> apply Fin.ext
    · change (2 * p.1.val + p.2.val) / 2 = p.1.val
      omega
    · change (2 * p.1.val + p.2.val) % 2 = p.2.val
      omega

/-- The core columns and points of a pair, together with its full-face probes. -/
structure PairBlockData (K : Type*) [Field K] (k : ℕ) (j : Fin k) where
  point : Fin 13 → Fin (10 + 2 * k) → K
  weight : Fin 13 → Fin 2 → K
  supported : ∀ r i, i ∉ pairSupport j → point r i = 0
  coreColumn : Fin 26 → B7Column (10 + 2 * k)
  coreOwner : ∀ c, b7Owner (coreColumn c) = some j.val
  faceParameter : PairFullFace k j → K
  faceParameter_ne : ∀ F, faceParameter F ≠ 0

/-- The initial-pool rows and columns, whose internal determinant comes from C.2. -/
structure PoolBlockData (K : Type*) [Field K] (m : ℕ) (ι : Type*) where
  probe : ι → B11Probe K m
  column : ι → B7Column m
  supported : ∀ r i, 10 ≤ i.val → (probe r).point i = 0
  columnPool : ∀ c, b7Owner (column c) = none

/-- The pair core precedes the two rows and columns of each full face. -/
abbrev PairBlockIndex (k : ℕ) (j : Fin k) := Fin 26 ⊕ (Fin 2 × PairFullFace k j)

instance (j : Fin k) : DecidableEq (PairBlockIndex k j) :=
  inferInstanceAs (DecidableEq (Fin 26 ⊕ (Fin 2 × PairFullFace k j)))

variable {j : Fin k}

def pairCoreProbe (D : PairBlockData K k j) (r : Fin 26) : B11Probe K (10 + 2 * k) :=
  ⟨D.point (pairCoreRowEquiv r).1, D.weight (pairCoreRowEquiv r).1, (pairCoreRowEquiv r).2⟩

def pairFullFaceProbe (D : PairBlockData K k j) (r : Fin 2 × PairFullFace k j) :
    B11Probe K (10 + 2 * k) :=
  ⟨faceProbe r.2.val.2 (D.faceParameter r.2), pureDirection r.2.val.1, r.1⟩

def pairFullFaceColumn (c : Fin 2 × PairFullFace k j) : B7Column (10 + 2 * k) :=
  .localColumn c.2.val.1 (fullFaceColumn c.2 c.1)

def pairProbe (D : PairBlockData K k j) : PairBlockIndex k j → B11Probe K (10 + 2 * k) :=
  Sum.elim (pairCoreProbe D) (pairFullFaceProbe D)

def pairColumn (D : PairBlockData K k j) : PairBlockIndex k j → B7Column (10 + 2 * k) :=
  Sum.elim D.coreColumn pairFullFaceColumn

theorem pairColumn_owner (D : PairBlockData K k j) (c : PairBlockIndex k j) :
    b7Owner (pairColumn D c) = some j.val := by
  rcases c with c | ⟨i, F⟩
  · exact D.coreOwner c
  · change faceOwner (localFace (fullFaceColumn F i)) = some j.val
    rw [fullFaceColumn_face]
    exact F.property.1

/-- Every row of a later pair vanishes on the earlier pair's coordinates. -/
theorem pairProbe_zero_of_earlier (D : PairBlockData K k j) (r : PairBlockIndex k j)
    {l : ℕ} (hl : l < j.val) (i : Fin (10 + 2 * k)) (hi : vertexOwner i = some l) :
    (pairProbe D r).point i = 0 := by
  rcases r with r | ⟨r, F⟩
  · exact D.supported _ i (not_mem_pairSupport_of_earlier j hi hl)
  · apply faceProbe_eq_zero_of_not_mem
    intro hm
    exact (not_le_of_gt hl) (faceOwner_le_vertexOwner F.val.2 F.property.1 hm hi)

/-- The pair core does not see a full-face column. -/
theorem coreProbe_kills_fullFace (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j)
    (r : Fin 26) (c : Fin 2 × PairFullFace k j) :
    probeEntry P (pairCoreProbe D r) (pairFullFaceColumn c) = 0 := by
  rcases c with ⟨i, F⟩
  apply localValue_full_face_zero_on_pairSupport P.cones (fullFaceColumn F i) _ j
    (D.point (pairCoreRowEquiv r).1) (D.supported _) _ _
  rw [fullFaceColumn_face]
  exact F.property.2

/-- The diagonal pivot matrix of a full face. -/
def pivotMatrix (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j)
    (F : PairFullFace k j) : Matrix (Fin 2) (Fin 2) K :=
  fullFaceMinor P.cones (fullFaceColumn F 0) (fullFaceColumn F 1) F.val.2 (D.faceParameter F)

/-- Evaluating full-face columns at the full-face probes is block diagonal. -/
theorem fullFaceProbeEntry_eq_blockDiagonal (P : B7Data K (10 + 2 * k))
    (D : PairBlockData K k j) (r c : Fin 2 × PairFullFace k j) :
    probeEntry P (pairFullFaceProbe D r) (pairFullFaceColumn c) =
      Matrix.blockDiagonal (pivotMatrix P D) r c := by
  rcases r with ⟨i, F⟩
  rcases c with ⟨t, G⟩
  by_cases hFG : F = G
  · subst G
    rw [Matrix.blockDiagonal_apply_eq]
    simp only [probeEntry, pairFullFaceProbe, pairFullFaceColumn, b7Value, pivotMatrix,
      fullFaceMinor, fullFaceColumn_vec]
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hFG]
    by_cases hdir : G.val.1 = F.val.1
    · have hface : G.val.2 ≠ F.val.2 := by
        intro h
        exact hFG (Subtype.ext (Prod.ext hdir.symm h.symm))
      apply localValue_full_face_off_diagonal P.cones (fullFaceColumn G t) F.val.2
        (D.faceParameter_ne F)
      · rw [fullFaceColumn_face]
        exact G.property.2
      · rwa [fullFaceColumn_face]
    · exact localValue_wrong_direction P.cones (fullFaceColumn G t)
        (faceProbe F.val.2 (D.faceParameter F)) hdir i

/-- The pair-core evaluation block `E_j`. -/
def pairCoreMatrix (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j) :
    Matrix (Fin 26) (Fin 26) K := fun r c => probeEntry P (pairCoreProbe D r) (D.coreColumn c)

/-- The entire evaluated diagonal block of one pair. -/
def pairMatrix (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j) :
    Matrix (PairBlockIndex k j) (PairBlockIndex k j) K :=
  fun r c => probeEntry P (pairProbe D r) (pairColumn D c)

/-- Proper-face and star columns at the full-face rows stay in the lower-left
block. Only the opposite off-diagonal block is required to vanish. -/
theorem pairMatrix_eq_blocks (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j) :
    pairMatrix P D = Matrix.fromBlocks (pairCoreMatrix P D) 0
      (Matrix.of fun r c => probeEntry P (pairFullFaceProbe D r) (D.coreColumn c))
      (Matrix.blockDiagonal (pivotMatrix P D)) := by
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · exact coreProbe_kills_fullFace P D r c
  · rfl
  · exact fullFaceProbeEntry_eq_blockDiagonal P D r c

/-- The determinant of the pair block is its core determinant times the local pivots. -/
theorem det_pairMatrix (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j) :
    (pairMatrix P D).det = (pairCoreMatrix P D).det * ∏ F, (pivotMatrix P D F).det := by
  rw [pairMatrix_eq_blocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_blockDiagonal]

/-- A block-triangular matrix on a dependent sum has the determinant of its
literal diagonal restrictions as factors. -/
private theorem det_sigma_blocks {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {I : α → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : Matrix (Σ a, I a) (Σ a, I a) K) (hM : M.BlockTriangular Sigma.fst) :
    M.det = ∏ a : α, (M.submatrix (Sigma.mk a) (Sigma.mk a)).det := by
  rw [hM.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  let e : {i : Σ a, I a // i.fst = a} ≃ I a := {
    toFun i := i.property ▸ i.val.2
    invFun i := ⟨⟨a, i⟩, rfl⟩
    left_inv := by
      rintro ⟨⟨b, i⟩, h⟩
      change b = a at h
      subst b
      rfl
    right_inv := fun _ => rfl }
  rw [← Matrix.det_reindex_self e (M.toSquareBlock Sigma.fst a)]
  rfl

/-- The evaluated matrix on all pair rows and columns. -/
def allPairMatrix (P : B7Data K (10 + 2 * k)) (D : ∀ j : Fin k, PairBlockData K k j) :
    Matrix (Σ j : Fin k, PairBlockIndex k j) (Σ j : Fin k, PairBlockIndex k j) K :=
  fun r c => probeEntry P (pairProbe (D r.fst) r.snd) (pairColumn (D c.fst) c.snd)

/-- Later pair rows annihilate earlier pair columns. In increasing pair order
this is upper block triangular, or lower block triangular in reverse order. -/
theorem allPairMatrix_blockTriangular (P : B7Data K (10 + 2 * k))
    (D : ∀ j : Fin k, PairBlockData K k j) :
    (allPairMatrix P D).BlockTriangular Sigma.fst := by
  intro r c h
  exact b7Value_zero_of_owner P _ (pairColumn_owner (D c.fst) c.snd) _
    (fun i hi => pairProbe_zero_of_earlier (D r.fst) r.snd h i hi) _ _

/-- The matrix on the pool rows and pool columns. -/
def poolMatrix {ι : Type*} (P : B7Data K m) (R : PoolBlockData K m ι) : Matrix ι ι K :=
  fun r c => probeEntry P (R.probe r) (R.column c)

/-- The complete supported evaluation matrix assembled from the pool and pairs. -/
def b11Matrix {ι : Type*} (P : B7Data K (10 + 2 * k))
    (R : PoolBlockData K (10 + 2 * k) ι) (D : ∀ j : Fin k, PairBlockData K k j) :
    Matrix (ι ⊕ (Σ j : Fin k, PairBlockIndex k j))
      (ι ⊕ (Σ j : Fin k, PairBlockIndex k j)) K :=
  fun r c => probeEntry P
    (Sum.elim R.probe (fun j => pairProbe (D j.fst) j.snd) r)
    (Sum.elim R.column (fun j => pairColumn (D j.fst) j.snd) c)

/-- The pool rows annihilate every pair column. -/
theorem b11Matrix_eq_blocks {ι : Type*} (P : B7Data K (10 + 2 * k))
    (R : PoolBlockData K (10 + 2 * k) ι) (D : ∀ j : Fin k, PairBlockData K k j) :
    b11Matrix P R D = Matrix.fromBlocks (poolMatrix P R) 0
      (Matrix.of fun r c => probeEntry P (pairProbe (D r.fst) r.snd) (R.column c)) (allPairMatrix P D) := by
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · apply b7Value_zero_of_owner P _ (pairColumn_owner (D c.fst) c.snd) _ _ _ _
    intro i hi
    have hv := (vertexOwner_eq_some i c.fst.val).mp hi
    exact R.supported r i (by omega)
  · rfl
  · rfl

/-- Equation (B.10) on the matched evaluation indexing. Its proof uses actual
zero entries from face and pair supports. -/
theorem det_b11Matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : B7Data K (10 + 2 * k)) (R : PoolBlockData K (10 + 2 * k) ι)
    (D : ∀ j : Fin k, PairBlockData K k j) :
    (b11Matrix P R D).det = (poolMatrix P R).det *
      ∏ j, ((pairCoreMatrix P (D j)).det * ∏ F, (pivotMatrix P (D j) F).det) := by
  rw [b11Matrix_eq_blocks, Matrix.det_fromBlocks_zero₁₂,
    det_sigma_blocks (allPairMatrix P D) (allPairMatrix_blockTriangular P D)]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact det_pairMatrix P (D j)

/-- Distinct single-edge slopes make every actual local pivot nonsingular. -/
theorem pivotMatrix_det_ne_zero (P : B7Data K (10 + 2 * k)) (D : PairBlockData K k j)
    (F : PairFullFace k j)
    (hτ : Set.InjOn (fun e : Edge ((10 + 2 * k) + 2) => P.cones.edgeSlope e 0)
      {e | single e = true}) : (pivotMatrix P D F).det ≠ 0 := by
  apply det_fullFaceMinor_ne_zero _ _ _ _ (D.faceParameter_ne F)
    (fullFaceColumn_mem F 0) (fullFaceColumn_mem F 1)
  intro h
  have hcols : fullFaceColumn F 0 = fullFaceColumn F 1 :=
    eq_of_localFace_eq_of_localSlopeEdge_eq (by simp)
      (hτ (single_localSlopeEdge _) (single_localSlopeEdge _) h.symm)
  exact zero_ne_one (fullFaceColumn_injective F hcols)

/-- The assembled `B11` is nonsingular when its two finite certificate types
and the single-slope conditions are nonsingular. -/
theorem det_b11Matrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : B7Data K (10 + 2 * k)) (R : PoolBlockData K (10 + 2 * k) ι)
    (D : ∀ j : Fin k, PairBlockData K k j)
    (hR : (poolMatrix P R).det ≠ 0) (hE : ∀ j, (pairCoreMatrix P (D j)).det ≠ 0)
    (hτ : Set.InjOn (fun e : Edge ((10 + 2 * k) + 2) => P.cones.edgeSlope e 0)
      {e | single e = true}) : (b11Matrix P R D).det ≠ 0 := by
  rw [det_b11Matrix]
  apply mul_ne_zero hR
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply mul_ne_zero (hE j)
  apply Finset.prod_ne_zero_iff.mpr
  intro F _
  exact pivotMatrix_det_ne_zero P (D j) F hτ

end IdealGeneration.CubicSupported.B5
