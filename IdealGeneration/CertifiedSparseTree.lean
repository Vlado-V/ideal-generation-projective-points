module

public import IdealGeneration.CertifiedSparseRow

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Balanced accumulators for sparse matrix certificates

Each update descends through one branch of a fixed-depth binary tree. Natural
column labels are read from their low bits, so updates require no array access
or dependent index casts. Equality of the resulting trees checks their leaves
structurally.
-/

namespace CertifiedRank

universe u v

/-- A complete binary tree with `2 ^ depth` scalar leaves. -/
@[reducible] def RowTree (R : Type u) : Nat → Type u
  | 0 => R
  | depth + 1 => RowTree R depth × RowTree R depth

/-- Read a leaf, using one low-order bit at each level. -/
def treeGet {R : Type*} : (depth : Nat) → RowTree R depth → Nat → R
  | 0, value, _ => value
  | depth + 1, children, index =>
    if index % 2 = 0 then treeGet depth children.1 (index / 2)
    else treeGet depth children.2 (index / 2)

/-- Add at a leaf while retaining the sibling at every level. -/
def treeAdd {R : Type*} [Add R] :
    (depth : Nat) → RowTree R depth → Nat → R → RowTree R depth
  | 0, value, _, coefficient => value + coefficient
  | depth + 1, children, index, coefficient =>
    if index % 2 = 0 then
      (treeAdd depth children.1 (index / 2) coefficient, children.2)
    else
      (children.1, treeAdd depth children.2 (index / 2) coefficient)

/-- A constant zero tree. -/
def treeZero {R : Type*} [Zero R] : (depth : Nat) → RowTree R depth
  | 0 => 0
  | depth + 1 => (treeZero depth, treeZero depth)

/-- Apply a scalar operation once to each leaf. -/
def treeMap {R S : Type*} (f : R → S) :
    (depth : Nat) → RowTree R depth → RowTree S depth
  | 0, value => f value
  | depth + 1, children => (treeMap f depth children.1, treeMap f depth children.2)

theorem treeGet_zero {R : Type*} [Zero R] (depth index : Nat) :
    treeGet depth (treeZero (R := R) depth) index = 0 := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih => simp [treeGet, treeZero, ih]

theorem treeGet_map {R S : Type*} (f : R → S) (depth : Nat)
    (tree : RowTree R depth) (index : Nat) :
    treeGet depth (treeMap f depth tree) index = f (treeGet depth tree index) := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih =>
    by_cases h : index % 2 = 0 <;> simp [treeGet, treeMap, h, ih]

/-- Bounded labels identify leaves uniquely. -/
theorem treeGet_add {R : Type*} [AddMonoid R] (depth : Nat)
    (tree : RowTree R depth) (index query : Nat) (coefficient : R)
    (hi : index < 2 ^ depth) (hq : query < 2 ^ depth) :
    treeGet depth (treeAdd depth tree index coefficient) query =
      treeGet depth tree query + if index = query then coefficient else 0 := by
  induction depth generalizing index query with
  | zero =>
    have hi0 : index = 0 := by simpa using hi
    have hq0 : query = 0 := by simpa using hq
    simp [treeGet, treeAdd, hi0, hq0]
  | succ depth ih =>
    have hi' : index / 2 < 2 ^ depth := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa only [pow_succ] using hi
    have hq' : query / 2 < 2 ^ depth := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      simpa only [pow_succ] using hq
    by_cases hi0 : index % 2 = 0 <;> by_cases hq0 : query % 2 = 0
    · have heq : index / 2 = query / 2 ↔ index = query := by omega
      simpa [treeGet, treeAdd, hi0, hq0, heq] using
        ih tree.1 (index / 2) (query / 2) hi' hq'
    · have hne : index ≠ query := by omega
      simp [treeGet, treeAdd, hi0, hq0, hne]
    · have hne : index ≠ query := by omega
      simp [treeGet, treeAdd, hi0, hq0, hne]
    · have heq : index / 2 = query / 2 ↔ index = query := by omega
      simpa [treeGet, treeAdd, hi0, hq0, heq] using
        ih tree.2 (index / 2) (query / 2) hi' hq'

variable {R : Type*} [Semiring R] {n : Nat}

/-- Fold sparse entries into a balanced accumulator. -/
def treeAccumulate (depth : Nat) (row : SparseRow n R) (tree : RowTree R depth) :
    RowTree R depth :=
  row.foldl (fun current entry => treeAdd depth current entry.1.val entry.2) tree

theorem treeAccumulate_get (depth : Nat) (hn : n ≤ 2 ^ depth)
    (row : SparseRow n R) (tree : RowTree R depth) (query : Fin n) :
    treeGet depth (treeAccumulate depth row tree) query.val =
      treeGet depth tree query.val + rowValue row query := by
  induction row generalizing tree with
  | nil => simp [treeAccumulate, rowValue]
  | cons entry row ih =>
    change treeGet depth (treeAccumulate depth row
      (treeAdd depth tree entry.1.val entry.2)) query.val = _
    rw [ih, treeGet_add depth tree entry.1.val query.val entry.2
      (entry.1.isLt.trans_le hn) (query.isLt.trans_le hn)]
    simp only [rowValue, List.map_cons, List.sum_cons, Fin.ext_iff, add_assoc]

/-- A sparse row stored in a padded balanced tree. -/
def treeRow (depth : Nat) (row : SparseRow n R) : RowTree R depth :=
  treeAccumulate depth row (treeZero depth)

theorem treeRow_get (depth : Nat) (hn : n ≤ 2 ^ depth)
    (row : SparseRow n R) (query : Fin n) :
    treeGet depth (treeRow depth row) query.val = rowValue row query := by
  rw [treeRow, treeAccumulate_get depth hn, treeGet_zero, zero_add]

/-- Compute the natural product row and reduce its leaves once. -/
def treeProductResidues (p depth : Nat) (row : SparseRow n Nat)
    (A : Fin n → SparseRow n Nat) : RowTree Nat depth :=
  treeMap (fun value => value % p) depth (treeRow depth (multiplyRow row A))

def treeRowResidues (p depth : Nat) (row : SparseRow n Nat) : RowTree Nat depth :=
  treeMap (fun value => value % p) depth (treeRow depth row)

/-- A structural tree equality certifies every entry of the product row. -/
theorem checked_tree_product_row (p depth : Nat) (hn : n ≤ 2 ^ depth)
    (row : SparseRow n Nat) (A : Fin n → SparseRow n Nat) (target : SparseRow n Nat)
    (h : treeProductResidues p depth row A = treeRowResidues p depth target)
    (query : Fin n) :
    (∑ k, ((rowValue row k : Nat) : ZMod p) * ((rowValue (A k) query : Nat) : ZMod p)) =
      ((rowValue target query : Nat) : ZMod p) := by
  have hq := congrArg (fun tree : RowTree Nat depth =>
    ((treeGet depth tree query.val : Nat) : ZMod p)) h
  simp only [treeProductResidues, treeRowResidues, treeGet_map,
    treeRow_get depth hn, ZMod.natCast_mod] at hq
  have hm := congrArg (fun value : Nat => (value : ZMod p)) (multiplyRow_get row A query)
  simp only [rowVector_get, Nat.cast_sum, Nat.cast_mul] at hm
  exact hm.symm.trans hq

/-- The balanced checker proves the same matrix identity as `checked_product`. -/
theorem checked_tree_product (p depth : Nat) (hn : n ≤ 2 ^ depth)
    (L U target : Fin n → SparseRow n Nat)
    (h : ∀ i, treeProductResidues p depth (L i) U = treeRowResidues p depth (target i)) :
    residueMatrix p L * residueMatrix p U = residueMatrix p target := by
  ext i j
  exact checked_tree_product_row p depth hn (L i) U (target i) (h i) j

end CertifiedRank
