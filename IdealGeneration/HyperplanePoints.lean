module

public import IdealGeneration.Points
public import IdealGeneration.HyperplanePolynomial
public import IdealGeneration.HyperplaneAlgebra
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Point configurations on and off a coordinate hyperplane

The trace has `m` affine coordinates. Its embedding into an ambient chart
with `m+1` affine coordinates prepends the zero normal coordinate.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {m p q d : ℕ}

/-- Embed trace points into the coordinate hyperplane `x₀ = 0`. -/
def embedHyperplanePoints (b : PointCoordinates K m q) :
    PointCoordinates K (m + 1) q :=
  fun ij => (@Fin.cons m (fun _ => K) 0 (fun j => b (ij.1, j))) ij.2

/-- An ordered union of ambient points and embedded trace points. -/
def hyperplaneConfiguration (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) : PointCoordinates K (m + 1) (p + q) :=
  fun ij => Fin.addCases (fun i => a (i, ij.2))
    (fun i => embedHyperplanePoints b (i, ij.2)) ij.1

@[simp] theorem embedHyperplanePoints_zero (b : PointCoordinates K m q) (i : Fin q) :
    embedHyperplanePoints b (i, 0) = 0 := by
  simp [embedHyperplanePoints]

@[simp] theorem embedHyperplanePoints_succ (b : PointCoordinates K m q)
    (i : Fin q) (j : Fin m) : embedHyperplanePoints b (i, j.succ) = b (i, j) := by
  simp [embedHyperplanePoints]

@[simp] theorem hyperplaneConfiguration_left (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (i : Fin p) (j : Fin (m + 1)) :
    hyperplaneConfiguration a b (i.castAdd q, j) = a (i, j) := by
  simp [hyperplaneConfiguration]

@[simp] theorem hyperplaneConfiguration_right (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (i : Fin q) (j : Fin (m + 1)) :
    hyperplaneConfiguration a b (i.natAdd p, j) = embedHyperplanePoints b (i, j) := by
  simp [hyperplaneConfiguration]

/-- Embedding the affine trace and normalizing its last coordinate commute. -/
theorem chartPoint_embedHyperplanePoints (b : PointCoordinates K m q) (i : Fin q) :
    chartPoint K (embedHyperplanePoints b) i = Fin.cons 0 (chartPoint K b i) := by
  change (Fin.snoc (@Fin.cons m (fun _ => K) 0 (fun j => b (i, j))) 1 : Fin (m + 2) → K) =
    @Fin.cons (m + 1) (fun _ => K) 0 (Fin.snoc (fun j => b (i, j)) 1)
  exact (Fin.cons_snoc_eq_snoc_cons 0 (fun j => b (i, j)) 1).symm

@[simp] theorem chartPoint_hyperplaneConfiguration_left
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q) (i : Fin p) :
    chartPoint K (hyperplaneConfiguration a b) (i.castAdd q) = chartPoint K a i := by
  simp [chartPoint, hyperplaneConfiguration]

@[simp] theorem chartPoint_hyperplaneConfiguration_right
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q) (i : Fin q) :
    chartPoint K (hyperplaneConfiguration a b) (i.natAdd p) =
      Fin.cons 0 (chartPoint K b i) := by
  rw [← chartPoint_embedHyperplanePoints]
  simp [chartPoint, hyperplaneConfiguration]

/-- Evaluation of an extended trace polynomial agrees with trace evaluation. -/
theorem eval_rename_at_embedded_point (b : PointCoordinates K m q)
    (i : Fin q) (f : Poly K (m + 1)) :
    eval (chartPoint K (embedHyperplanePoints b) i) (rename Fin.succ f) =
      eval (chartPoint K b i) f := by
  rw [eval_rename, chartPoint_embedHyperplanePoints]
  congr 1

/-- The normal-coordinate multiple of a form. -/
def hyperplaneNormalMul (f : Forms K (m + 2) d) : Forms K (m + 2) (d + 1) :=
  ⟨X 0 * f.val, by
    simpa [Nat.add_comm] using (isHomogeneous_X (R := K) (0 : Fin (m + 2))).mul f.property⟩

@[simp] theorem hyperplaneNormalMul_val (f : Forms K (m + 2) d) :
    (hyperplaneNormalMul f).val = X 0 * f.val := rfl

/-- A nonzero normal coordinate allows cancellation of that coordinate in vanishing conditions. -/
theorem off_hyperplane_normal_vanishing_iff (a : PointCoordinates K (m + 1) p)
    (ha : ∀ i, a (i, 0) ≠ 0) (f : Poly K (m + 2)) :
    (∀ i, eval (chartPoint K a i) (X 0 * f) = 0) ↔
      (∀ i, eval (chartPoint K a i) f = 0) := by
  have hz (i : Fin p) : chartPoint K a i 0 = a (i, 0) := by
    change chartPoint K a i (Fin.castSucc 0) = _
    exact chartPoint_castSucc a i 0
  simp only [map_mul, eval_X, hz, mul_eq_zero, ha, false_or]

/-- All normal-coordinate multiples vanish on the embedded trace. -/
theorem eval_normal_mul_at_embedded_point (b : PointCoordinates K m q)
    (i : Fin q) (f : Poly K (m + 2)) :
    eval (chartPoint K (embedHyperplanePoints b) i) (X 0 * f) = 0 := by
  rw [map_mul, eval_X, chartPoint_embedHyperplanePoints]
  simp

/-- Vanishing on the union means vanishing on both groups. -/
theorem mem_hyperplaneConfiguration_piece_iff
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (f : Forms K (m + 2) d) :
    f ∈ pointDegreePiece K (hyperplaneConfiguration a b) d ↔
      f ∈ pointDegreePiece K a d ∧ f ∈ pointDegreePiece K (embedHyperplanePoints b) d := by
  simp only [mem_pointDegreePiece]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (i.castAdd q),
      fun i => by simpa only [chartPoint_hyperplaneConfiguration_right,
        ← chartPoint_embedHyperplanePoints] using h (i.natAdd p)⟩
  · rintro ⟨ha, hb⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using ha j
    · simpa only [chartPoint_hyperplaneConfiguration_right,
        ← chartPoint_embedHyperplanePoints] using hb j

/-- Normal multiplication places every residual equation in the union ideal. -/
theorem normalMul_mem_union (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (f : Forms K (m + 2) d)
    (hf : f ∈ pointDegreePiece K a d) :
    hyperplaneNormalMul f ∈ pointDegreePiece K (hyperplaneConfiguration a b) (d + 1) := by
  rw [mem_hyperplaneConfiguration_piece_iff]
  constructor
  · apply (mem_pointDegreePiece a _).mpr
    intro i
    change eval (chartPoint K a i) (X 0 * f.val) = 0
    rw [map_mul, (mem_pointDegreePiece a f).mp hf i, mul_zero]
  · apply (mem_pointDegreePiece (embedHyperplanePoints b) _).mpr
    intro i
    exact eval_normal_mul_at_embedded_point b i f.val

/-- Off the hyperplane, union membership of a normal multiple recovers the residual equation. -/
theorem normalMul_mem_union_iff (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (ha : ∀ i, a (i, 0) ≠ 0)
    (f : Forms K (m + 2) d) :
    hyperplaneNormalMul f ∈ pointDegreePiece K (hyperplaneConfiguration a b) (d + 1) ↔
      f ∈ pointDegreePiece K a d := by
  constructor
  · intro hf
    have hfa := ((mem_hyperplaneConfiguration_piece_iff a b _).mp hf).1
    apply (mem_pointDegreePiece a f).mpr
    exact (off_hyperplane_normal_vanishing_iff a ha f.val).mp
      ((mem_pointDegreePiece a _).mp hfa)
  · exact normalMul_mem_union a b f

/-- Residual equations map to union equations by multiplication with the normal coordinate. -/
def normalMulToUnion (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (d : ℕ) :
    pointDegreePiece K a d →ₗ[K] pointDegreePiece K (hyperplaneConfiguration a b) (d + 1) where
  toFun f := ⟨hyperplaneNormalMul f.val, normalMul_mem_union a b f.val f.property⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_smul_comm _ _ _

@[simp] theorem normalMulToUnion_val (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (f : pointDegreePiece K a d) :
    (normalMulToUnion a b d f).val.val = X 0 * f.val.val := rfl

/-- The residual normal-multiplication map is injective. -/
theorem normalMulToUnion_injective (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (d : ℕ) : Function.Injective (normalMulToUnion a b d) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero 0)
    (congrArg (fun x : pointDegreePiece K (hyperplaneConfiguration a b) (d + 1) => x.val.val) h)

/-- Scalar interpolation on the trace and in one lower degree off the hyperplane
combines to scalar interpolation on the specialized configuration. -/
theorem pointEvaluation_hyperplaneConfiguration_surjective
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d))
    (htrace : Function.Surjective (pointEvaluation K b (d + 1))) :
    Function.Surjective (pointEvaluation K (hyperplaneConfiguration a b) (d + 1)) := by
  intro y
  obtain ⟨t, ht⟩ := htrace (fun j => y (j.natAdd p))
  let t' : Forms K (m + 2) (d + 1) :=
    ⟨rename Fin.succ t.val, t.property.rename_isHomogeneous⟩
  let z : Fin p → K := fun i =>
    (y (i.castAdd q) - eval (chartPoint K a i) t'.val) / chartPoint K a i 0
  obtain ⟨g, hg⟩ := hoff z
  refine ⟨t' + hyperplaneNormalMul g, ?_⟩
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hx : chartPoint K a j 0 ≠ 0 := by
      change chartPoint K a j (Fin.castSucc (0 : Fin (m + 1))) ≠ 0
      simpa only [chartPoint_castSucc] using ha j
    have hgj : eval (chartPoint K a j) g.val = z j := congrFun hg j
    change eval (chartPoint K (hyperplaneConfiguration a b) (j.castAdd q))
      (t'.val + X 0 * g.val) = _
    rw [chartPoint_hyperplaneConfiguration_left, map_add, map_mul, eval_X, hgj]
    dsimp [z]
    field_simp [hx]
    ring
  · have htj : eval (chartPoint K b j) t.val = y (j.natAdd p) := congrFun ht j
    change eval (chartPoint K (hyperplaneConfiguration a b) (j.natAdd p))
      (t'.val + X 0 * g.val) = _
    rw [chartPoint_hyperplaneConfiguration_right, ← chartPoint_embedHyperplanePoints]
    rw [map_add, eval_normal_mul_at_embedded_point, add_zero]
    exact (eval_rename_at_embedded_point b j t.val).trans htj

/-- Restrict a union equation to its trace equation. -/
def unionRestriction (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (d : ℕ) :
    pointDegreePiece K (hyperplaneConfiguration a b) d →ₗ[K] pointDegreePiece K b d where
  toFun f := ⟨restrictForm K (m + 1) d f.val, by
    apply (mem_pointDegreePiece b _).mpr
    intro i
    change eval (chartPoint K b i) (hyperplaneRestrict K (m + 1) f.val.val) = 0
    rw [eval_hyperplaneRestrict, ← chartPoint_embedHyperplanePoints]
    exact (mem_pointDegreePiece (embedHyperplanePoints b) f.val).mp
      ((mem_hyperplaneConfiguration_piece_iff a b f.val).mp f.property).2 i⟩
  map_add' f g := by
    apply Subtype.ext
    exact (restrictForm K (m + 1) d).map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (restrictForm K (m + 1) d).map_smul c f.val

@[simp] theorem unionRestriction_val (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (f : pointDegreePiece K (hyperplaneConfiguration a b) d) :
    (unionRestriction a b d f).val.val = hyperplaneRestrict K (m + 1) f.val.val := rfl

/-- The trace of every residual normal multiple vanishes. -/
@[simp] theorem unionRestriction_normalMulToUnion
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (f : pointDegreePiece K a d) :
    unionRestriction a b (d + 1) (normalMulToUnion a b d f) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  change hyperplaneRestrict K (m + 1) (X 0 * f.val.val) = 0
  simp

/-- The residual-to-union-to-trace sequence is exact at the union. -/
theorem normalMulToUnion_range_eq_ker_unionRestriction
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0) :
    (normalMulToUnion a b d).range = (unionRestriction a b (d + 1)).ker := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    exact unionRestriction_normalMulToUnion a b g
  · intro f hf
    have hzero : restrictForm K (m + 1) (d + 1) f.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K (m + 1) f.val).mp hzero
    have hgf : hyperplaneNormalMul g = f.val := Subtype.ext hg.symm
    have hgmem : g ∈ pointDegreePiece K a d :=
      (normalMul_mem_union_iff a b ha g).mp (hgf.symm ▸ f.property)
    exact ⟨⟨g, hgmem⟩, Subtype.ext hgf⟩

/-- Independent residual scalar conditions make union restriction onto its trace ideal. -/
theorem unionRestriction_surjective (a : PointCoordinates K (m + 1) p)
    (b : PointCoordinates K m q) (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (unionRestriction a b (d + 1)) := by
  intro t
  let t' := extendForm K (m + 1) (d + 1) t.val
  let z : Fin p → K := fun i => eval (chartPoint K a i) t'.val / chartPoint K a i 0
  obtain ⟨g, hg⟩ := hoff z
  let f : Forms K (m + 2) (d + 1) := t' - hyperplaneNormalMul g
  have hf : f ∈ pointDegreePiece K (hyperplaneConfiguration a b) (d + 1) := by
    rw [mem_hyperplaneConfiguration_piece_iff]
    constructor
    · apply (mem_pointDegreePiece a f).mpr
      intro i
      have hx : chartPoint K a i 0 ≠ 0 := by
        change chartPoint K a i (Fin.castSucc (0 : Fin (m + 1))) ≠ 0
        simpa only [chartPoint_castSucc] using ha i
      have hgi : eval (chartPoint K a i) g.val = z i := congrFun hg i
      change eval (chartPoint K a i) (t'.val - X 0 * g.val) = 0
      rw [map_sub, map_mul, eval_X, hgi]
      dsimp [z]
      field_simp [hx]
      ring
    · apply (mem_pointDegreePiece (embedHyperplanePoints b) f).mpr
      intro i
      change eval (chartPoint K (embedHyperplanePoints b) i)
        (rename Fin.succ t.val.val - X 0 * g.val) = 0
      rw [map_sub, eval_normal_mul_at_embedded_point, sub_zero, eval_rename_at_embedded_point]
      exact (mem_pointDegreePiece b t.val).mp t.property i
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  change restrictForm K (m + 1) (d + 1) (t' - hyperplaneNormalMul g) = t.val
  rw [map_sub]
  have hnormal : restrictForm K (m + 1) (d + 1) (hyperplaneNormalMul g) = 0 := by
    apply Subtype.ext
    change hyperplaneRestrict K (m + 1) (X 0 * g.val) = 0
    simp
  rw [hnormal, sub_zero]
  exact restrictForm_extendForm K (m + 1) t.val

/-- Restriction of off-hyperplane equations to the full trace form space. -/
def offRestriction (a : PointCoordinates K (m + 1) p) (d : ℕ) :
    pointDegreePiece K a d →ₗ[K] Forms K (m + 1) d :=
  (restrictForm K (m + 1) d).comp (pointDegreePiece K a d).subtype

/-- Scalar interpolation off the hyperplane makes unrestricted trace lifting possible. -/
theorem offRestriction_surjective (a : PointCoordinates K (m + 1) p)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (offRestriction a (d + 1)) := by
  intro t
  let t' := extendForm K (m + 1) (d + 1) t
  let z : Fin p → K := fun i => eval (chartPoint K a i) t'.val / chartPoint K a i 0
  obtain ⟨g, hg⟩ := hoff z
  let f : Forms K (m + 2) (d + 1) := t' - hyperplaneNormalMul g
  have hf : f ∈ pointDegreePiece K a (d + 1) := by
    apply (mem_pointDegreePiece a f).mpr
    intro i
    have hx : chartPoint K a i 0 ≠ 0 := by
      change chartPoint K a i (Fin.castSucc (0 : Fin (m + 1))) ≠ 0
      simpa only [chartPoint_castSucc] using ha i
    have hgi : eval (chartPoint K a i) g.val = z i := congrFun hg i
    change eval (chartPoint K a i) (t'.val - X 0 * g.val) = 0
    rw [map_sub, map_mul, eval_X, hgi]
    dsimp [z]
    field_simp [hx]
    ring
  refine ⟨⟨f, hf⟩, ?_⟩
  change restrictForm K (m + 1) (d + 1) (t' - hyperplaneNormalMul g) = t
  rw [map_sub]
  have hnormal : restrictForm K (m + 1) (d + 1) (hyperplaneNormalMul g) = 0 := by
    apply Subtype.ext
    change hyperplaneRestrict K (m + 1) (X 0 * g.val) = 0
    simp
  rw [hnormal, sub_zero]
  exact restrictForm_extendForm K (m + 1) t

/-- The kernel of off-hyperplane restriction consists of normal multiples of residual equations. -/
theorem offRestriction_eq_zero_iff (a : PointCoordinates K (m + 1) p)
    (ha : ∀ i, a (i, 0) ≠ 0) (f : pointDegreePiece K a (d + 1)) :
    offRestriction a (d + 1) f = 0 ↔
      ∃ g : pointDegreePiece K a d, f.val.val = X 0 * g.val.val := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K (m + 1) f.val).mp hf
    have hgmem : g ∈ pointDegreePiece K a d := by
      apply (mem_pointDegreePiece a g).mpr
      apply (off_hyperplane_normal_vanishing_iff a ha g.val).mp
      intro i
      rw [← hg]
      exact (mem_pointDegreePiece a f.val).mp f.property i
    exact ⟨⟨g, hgmem⟩, hg⟩
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    change hyperplaneRestrict K (m + 1) f.val.val = 0
    rw [hg]
    simp

/-- Every polynomial equation of the union is an equation of its off-hyperplane group. -/
theorem pointPolynomialPiece_hyperplane_le_off
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q) (d : ℕ) :
    pointPolynomialPiece (hyperplaneConfiguration a b) d ≤ pointPolynomialPiece a d := by
  rintro f ⟨g, hg, rfl⟩
  exact ⟨g, ((mem_hyperplaneConfiguration_piece_iff a b g).mp hg).1, rfl⟩

/-- Restricting union equations gives trace equations. -/
theorem pointPolynomialPiece_restrict_hyperplane_le
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q) (d : ℕ) :
    (pointPolynomialPiece (hyperplaneConfiguration a b) d).map
      (hyperplaneRestrict K (m + 1)).toLinearMap ≤ pointPolynomialPiece b d := by
  rintro f ⟨g, ⟨g', hg', rfl⟩, rfl⟩
  exact ⟨(unionRestriction a b d ⟨g', hg'⟩).val,
    (unionRestriction a b d ⟨g', hg'⟩).property, rfl⟩

/-- Under residual interpolation, the polynomial image of union restriction is the trace ideal piece. -/
theorem pointPolynomialPiece_restrict_hyperplane_eq
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    (pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1)).map
      (hyperplaneRestrict K (m + 1)).toLinearMap = pointPolynomialPiece b (d + 1) := by
  apply le_antisymm (pointPolynomialPiece_restrict_hyperplane_le a b (d + 1))
  rintro f ⟨g, hg, rfl⟩
  obtain ⟨h, hh⟩ := unionRestriction_surjective a b ha hoff ⟨g, hg⟩
  refine ⟨h.val.val, ⟨h.val, h.property, rfl⟩, ?_⟩
  exact congrArg (fun z : pointDegreePiece K b (d + 1) => z.val.val) hh

/-- Normal multiples of residual polynomial equations vanish on the whole union. -/
theorem normal_mul_mem_pointPolynomialPiece_hyperplane
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    {f : Poly K (m + 2)} (hf : f ∈ pointPolynomialPiece a d) :
    X 0 * f ∈ pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1) := by
  rcases hf with ⟨g, hg, rfl⟩
  exact ⟨hyperplaneNormalMul g, normalMul_mem_union a b g hg, rfl⟩

/-- The polynomial kernel of union restriction is exactly the normal multiple of the residual piece. -/
theorem pointPolynomialPiece_hyperplane_kernel
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0) {f : Poly K (m + 2)}
    (hf : f ∈ pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1))
    (hzero : hyperplaneRestrict K (m + 1) f = 0) :
    ∃ g ∈ pointPolynomialPiece a d, f = X 0 * g := by
  rcases hf with ⟨g, hg, rfl⟩
  have hrestr : restrictForm K (m + 1) (d + 1) g = 0 := Subtype.ext hzero
  obtain ⟨w, hw⟩ := (restrictForm_eq_zero_iff K (m + 1) g).mp hrestr
  have hwg : hyperplaneNormalMul w = g := Subtype.ext hw.symm
  have hwmem : w ∈ pointDegreePiece K a d :=
    (normalMul_mem_union_iff a b ha w).mp (hwg.symm ▸ hg)
  exact ⟨w.val, ⟨w, hwmem, rfl⟩, hw⟩

/-- The same normal-division statement for the off-hyperplane ideal alone. -/
theorem pointPolynomialPiece_off_kernel
    (a : PointCoordinates K (m + 1) p) (ha : ∀ i, a (i, 0) ≠ 0)
    {f : Poly K (m + 2)} (hf : f ∈ pointPolynomialPiece a (d + 1))
    (hzero : hyperplaneRestrict K (m + 1) f = 0) :
    ∃ g ∈ pointPolynomialPiece a d, f = X 0 * g := by
  rcases hf with ⟨g, hg, rfl⟩
  have hrestr : offRestriction a (d + 1) ⟨g, hg⟩ = 0 := Subtype.ext hzero
  obtain ⟨w, hw⟩ := (offRestriction_eq_zero_iff a ha ⟨g, hg⟩).mp hrestr
  exact ⟨w.val.val, ⟨w.val, w.property, rfl⟩, hw⟩

/-- Residual scalar interpolation makes the image of off-point ideal restriction all trace forms. -/
theorem pointPolynomialPiece_off_restrict_eq
    (a : PointCoordinates K (m + 1) p) (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    (pointPolynomialPiece a (d + 1)).map (hyperplaneRestrict K (m + 1)).toLinearMap =
      Forms K (m + 1) (d + 1) := by
  apply le_antisymm
  · rintro f ⟨g, ⟨g', _, rfl⟩, rfl⟩
    exact hyperplaneRestrict_homogeneous K (m + 1) g'.property
  · intro f hf
    obtain ⟨g, hg⟩ := offRestriction_surjective a ha hoff ⟨f, hf⟩
    exact ⟨g.val.val, ⟨g.val, g.property, rfl⟩, congrArg Subtype.val hg⟩

/-- A linear lift of all trace equations into the specialized union ideal. -/
theorem exists_linear_union_lift
    (a : PointCoordinates K (m + 1) p) (b : PointCoordinates K m q)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d)) :
    ∃ L : pointPolynomialPiece b (d + 1) →ₗ[K] Poly K (m + 2),
      (∀ t, hyperplaneRestrict K (m + 1) (L t) = t.val) ∧
      L.range ≤ pointPolynomialPiece (hyperplaneConfiguration a b) (d + 1) := by
  have : Module.Free K (pointDegreePiece K b (d + 1)) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (pointDegreePiece K b (d + 1))
  have : Module.Projective K (pointDegreePiece K b (d + 1)) := by
    with_unfolding_all infer_instance
  obtain ⟨s, hs⟩ := (unionRestriction a b (d + 1)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (unionRestriction_surjective a b ha hoff))
  let e := pointPolynomialPieceEquiv b (d + 1)
  let L : pointPolynomialPiece b (d + 1) →ₗ[K] Poly K (m + 2) :=
    (Forms K (m + 2) (d + 1)).subtype.comp
      ((pointDegreePiece K (hyperplaneConfiguration a b) (d + 1)).subtype.comp
        (s.comp e.symm.toLinearMap))
  refine ⟨L, ?_, ?_⟩
  · intro t
    have ht : (e.symm t).val.val = t.val := by
      have h := congrArg Subtype.val (e.apply_symm_apply t)
      simpa only [e, pointPolynomialPieceEquiv_val] using h
    have h := LinearMap.congr_fun hs (e.symm t)
    have h' := congrArg (fun z : pointDegreePiece K b (d + 1) => z.val.val) h
    change hyperplaneRestrict K (m + 1) ((s (e.symm t)).val.val) = t.val
    exact h'.trans ht
  · rintro f ⟨t, rfl⟩
    exact ⟨(s (e.symm t)).val, (s (e.symm t)).property, rfl⟩

end IdealGeneration
