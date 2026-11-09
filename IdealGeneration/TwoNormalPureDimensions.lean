module

public import IdealGeneration.TwoNormalDivision
public import IdealGeneration.TwoGroupInterpolation
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Pure subspaces of the residual polynomial pair

Each coordinate projection of (4.8) has kernel of dimension `(m+1) dim G`.
The proof divides point-ideal forms by a nonvanishing normal coordinate and
then uses rank-nullity on the two genuine slice restrictions.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module TwoGroupInterpolation
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m p d : ℕ}

local instance pointGroup (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    AddCommGroup (pointDegreePiece K x d) := Module.addCommMonoidToAddCommGroup K

/-- First-normal multiplication on the actual point ideal. -/
def pointFirstNormalMul (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    pointDegreePiece K x d →ₗ[K] pointDegreePiece K x (d + 1) where
  toFun f := ⟨normalFormMul K (m + 1) d f.val, by
    rw [mem_pointDegreePiece]
    intro i
    change eval (chartPoint K x i) (X 0 * f.val.val) = 0
    rw [map_mul, (mem_pointDegreePiece x f.val).mp f.property i, mul_zero]⟩
  map_add' f g := Subtype.ext ((normalFormMul K (m + 1) d).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((normalFormMul K (m + 1) d).map_smul c f.val)

/-- Restrict point-ideal forms to the second slice `s=0`. -/
def pointRestrictionB (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    pointDegreePiece K x d →ₗ[K] Forms K (m + 1) d :=
  (restrictForm K (m + 1) d).comp (pointDegreePiece K x d).subtype

/-- Restrict point-ideal forms to the first slice `t=0`. -/
def pointRestrictionA (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    pointDegreePiece K x d →ₗ[K] Forms K (m + 1) d :=
  (restrictAForm K m d).comp (pointDegreePiece K x d).subtype

/-- Division by `s` preserves vanishing at points where `s` is nonzero. -/
theorem pointRestrictionB_ker (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0) :
    (pointRestrictionB x (d + 1)).ker = (pointFirstNormalMul x d).range := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (restrictForm_eq_zero_iff K (m + 1) f.val).mp hf
    have hgI : g ∈ pointDegreePiece K x d := by
      rw [mem_pointDegreePiece]
      intro i
      have h := (mem_pointDegreePiece x f.val).mp f.property i
      rw [hg, map_mul, eval_X] at h
      exact (mul_eq_zero.mp h).resolve_left (hs i)
    refine ⟨⟨g, hgI⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hg.symm
  · rintro ⟨g, rfl⟩
    change restrictForm K (m + 1) (d + 1) (normalFormMul K (m + 1) d g.val) = 0
    exact restrictForm_normalFormMul K (m + 1) g.val

/-- The `s`-multiplication map has no nonzero kernel. -/
theorem pointFirstNormalMul_injective (x : PointCoordinates K (m + 1) p) :
    Function.Injective (pointFirstNormalMul x d) := by
  intro f g h
  apply Subtype.ext
  apply normalFormMul_injective K (m + 1) d
  exact congrArg Subtype.val h

/-- The restriction kernel on the second slice is one copy of `G`. -/
theorem finrank_pointRestrictionB_ker (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0) :
    finrank K (pointRestrictionB x (d + 1)).ker = finrank K (pointDegreePiece K x d) := by
  rw [pointRestrictionB_ker x hs]
  exact LinearMap.finrank_range_of_inj (pointFirstNormalMul_injective x)

/-- Second-normal multiplication on the actual point ideal. -/
def pointSecondNormalMul (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    pointDegreePiece K x d →ₗ[K] pointDegreePiece K x (d + 1) where
  toFun f := ⟨⟨X (0 : Fin (m + 1)).succ * f.val.val, by
    change (X (0 : Fin (m + 1)).succ * f.val.val).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using
      (isHomogeneous_X (R := K) (0 : Fin (m + 1)).succ).mul f.val.property⟩, by
    rw [mem_pointDegreePiece]
    intro i
    change eval (chartPoint K x i) (X (0 : Fin (m + 1)).succ * f.val.val) = 0
    rw [map_mul, (mem_pointDegreePiece x f.val).mp f.property i, mul_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    exact Subtype.ext (mul_add _ _ _)
  map_smul' c f := by
    apply Subtype.ext
    exact Subtype.ext (mul_smul_comm _ _ _)

/-- Division by `t` preserves vanishing at points where `t` is nonzero. -/
theorem pointRestrictionA_ker (x : PointCoordinates K (m + 1) p)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0) :
    (pointRestrictionA x (d + 1)).ker = (pointSecondNormalMul x d).range := by
  ext f
  constructor
  · intro hf
    have hfA : restrictA K m f.val.val = 0 := congrArg Subtype.val hf
    obtain ⟨g, hg⟩ := (restrictA_eq_zero_iff K m f.val).mp hfA
    have hgI : g ∈ pointDegreePiece K x d := by
      rw [mem_pointDegreePiece]
      intro i
      have h := (mem_pointDegreePiece x f.val).mp f.property i
      rw [hg, map_mul, eval_X] at h
      exact (mul_eq_zero.mp h).resolve_left (ht i)
    refine ⟨⟨g, hgI⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hg.symm
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    change restrictA K m (X (0 : Fin (m + 1)).succ * g.val.val) = 0
    rw [map_mul, restrictA_t, zero_mul]

/-- The `t`-multiplication map has no nonzero kernel. -/
theorem pointSecondNormalMul_injective (x : PointCoordinates K (m + 1) p) :
    Function.Injective (pointSecondNormalMul x d) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (fun q : pointDegreePiece K x (d + 1) => q.val.val) h
  exact mul_left_cancel₀ (X_ne_zero _) hh

/-- The restriction kernel on the first slice is one copy of `G`. -/
theorem finrank_pointRestrictionA_ker (x : PointCoordinates K (m + 1) p)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0) :
    finrank K (pointRestrictionA x (d + 1)).ker = finrank K (pointDegreePiece K x d) := by
  rw [pointRestrictionA_ker x ht]
  exact LinearMap.finrank_range_of_inj (pointSecondNormalMul_injective x)

/-- Tangential multiplication carries the degree-`d` point ideal into degree `d+1`. -/
def pointTangentialProduct (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    (Fin m → pointDegreePiece K x d) →ₗ[K] pointDegreePiece K x (d + 1) where
  toFun a := ⟨tangentProduct K m d (fun i => (a i).val), by
    rw [mem_pointDegreePiece]
    intro j
    change eval (chartPoint K x j) (∑ i, X i.succ.succ * (a i).val.val) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul, (mem_pointDegreePiece x (a i).val).mp (a i).property j, mul_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    exact (tangentProduct K m d).map_add _ _
  map_smul' c a := by
    apply Subtype.ext
    exact (tangentProduct K m d).map_smul c _

/-- The second coordinate image of (4.8) is exactly ordinary restriction to `s=0`. -/
theorem rightProjection_residualPair_range (x : PointCoordinates K (m + 1) p) :
    (rightProjection (residualPair K m (d := d) x).range).range =
      (pointRestrictionB x (d + 1)).range := by
  ext w
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨z, hz⟩ := u.property
    refine ⟨z.2, ?_⟩
    exact (congrArg Prod.snd hz).trans hu
  · rintro ⟨h, rfl⟩
    exact ⟨⟨residualPair K m x (0, h), ⟨(0, h), rfl⟩⟩, rfl⟩

/-- Adding the tangential product does not change the first coordinate image. -/
theorem leftProjection_residualPair_range (x : PointCoordinates K (m + 1) p) :
    (leftProjection (residualPair K m (d := d) x).range).range =
      (pointRestrictionA x (d + 1)).range := by
  ext w
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨z, hz⟩ := u.property
    refine ⟨z.2 + pointTangentialProduct x d z.1, ?_⟩
    exact (congrArg Prod.fst hz).trans hu
  · rintro ⟨h, rfl⟩
    refine ⟨⟨residualPair K m x (0, h), ⟨(0, h), rfl⟩⟩, ?_⟩
    change restrictAForm K m (d + 1)
      (h.val + tangentProduct K m d (0 : Fin m → Forms K (m + 2) d)) =
      restrictAForm K m (d + 1) h.val
    rw [map_zero, add_zero]

local instance pairImageGroup (x : PointCoordinates K (m + 1) p) (d : ℕ) :
    AddCommGroup (residualPair K m (d := d) x).range := Module.addCommMonoidToAddCommGroup K

/-- The parameter space dimension of the injective residual pair map. -/
theorem finrank_residualPair_range (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    finrank K (residualPair K m (d := d) x).range =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1)) := by
  rw [LinearMap.finrank_range_of_inj (residualPair_injective K m x hs htrace hproduct)]
  simp [Module.finrank_prod, Module.finrank_pi_fintype]

/-- The pure first-coordinate subspace of (4.8) has `(m+1) dim G` dimensions. -/
theorem finrank_rightProjection_residualPair_ker (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    finrank K (rightProjection (residualPair K m (d := d) x).range).ker =
      (m + 1) * finrank K (pointDegreePiece K x d) := by
  have hu := (rightProjection (residualPair K m (d := d) x).range).finrank_range_add_finrank_ker
  have he := (pointRestrictionB x (d + 1)).finrank_range_add_finrank_ker
  rw [rightProjection_residualPair_range, finrank_residualPair_range x hs htrace hproduct] at hu
  rw [finrank_pointRestrictionB_ker x hs] at he
  nlinarith

/-- The pure second-coordinate subspace of (4.8) has `(m+1) dim G` dimensions. -/
theorem finrank_leftProjection_residualPair_ker (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    finrank K (leftProjection (residualPair K m (d := d) x).range).ker =
      (m + 1) * finrank K (pointDegreePiece K x d) := by
  have hu := (leftProjection (residualPair K m (d := d) x).range).finrank_range_add_finrank_ker
  have he := (pointRestrictionA x (d + 1)).finrank_range_add_finrank_ker
  rw [leftProjection_residualPair_range, finrank_residualPair_range x hs htrace hproduct] at hu
  rw [finrank_pointRestrictionA_ker x ht] at he
  nlinarith

end IdealGeneration.TwoNormalTrace
