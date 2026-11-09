module

public import IdealGeneration.FixedPartialTrace
public import IdealGeneration.AffineEulerTransport
public import IdealGeneration.EulerMaximalRank
public import IdealGeneration.PointMonotonicity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Euler evaluation with a prescribed final point

Affine coordinate changes fix the affine chart and transport the actual
polynomial Euler relations. A general configuration can therefore be moved so
that its distinguished final point is any prescribed affine point.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} {n p d : ℕ}

/-- Append one prescribed point to an ordered affine configuration. -/
def snocPoints (a : PointCoordinates K n p) (y : Fin n → K) :
    PointCoordinates K n (p + 1) :=
  fun ij => Fin.snoc (α := fun _ => K) (fun i => a (i, ij.2)) (y ij.2) ij.1

@[simp] theorem snocPoints_castSucc (a : PointCoordinates K n p)
    (y : Fin n → K) (i : Fin p) (j : Fin n) :
    snocPoints a y (i.castSucc, j) = a (i, j) := by simp [snocPoints]

@[simp] theorem snocPoints_last (a : PointCoordinates K n p)
    (y : Fin n → K) (j : Fin n) :
    snocPoints a y (Fin.last p, j) = y j := by simp [snocPoints]

@[simp] theorem restrict_snocPoints_castSucc (a : PointCoordinates K n p) (y : Fin n → K) :
    restrictPoints (snocPoints a y) Fin.castSucc = a := by
  funext ij
  obtain ⟨i, j⟩ := ij
  exact snocPoints_castSucc a y i j

variable [Field K]

local instance eulerRelationsAddCommGroup : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

local instance eulerSubmoduleAddCommGroup (B : Submodule K (EulerRelations K n d)) :
    AddCommGroup B := Module.addCommMonoidToAddCommGroup K

/-- Reduced Euler evaluation and full Euler evaluation have the same kernel. -/
theorem eulerTraceEvaluation_ker_eq (a : PointCoordinates K n p) (d : ℕ) :
    (eulerTraceEvaluation a d).ker = (eulerEvaluation a d).ker := by
  ext f
  simp only [LinearMap.mem_ker]
  constructor
  · intro hf
    have hEuler := eulerEvaluation_range_le a d (show eulerEvaluation a d f ∈
        (eulerEvaluation a d).range from ⟨f, rfl⟩)
    funext j i
    refine Fin.lastCases ?_ (fun k => ?_) j
    · have hi := congrFun hEuler i
      change (∑ j, chartPoint K a i j * eulerEvaluation a d f j i) = 0 at hi
      rw [Fin.sum_univ_castSucc] at hi
      have hfirst (k : Fin n) : eulerEvaluation a d f k.castSucc i = 0 :=
        congrFun (congrFun hf i) k
      simpa only [hfirst, mul_zero, Finset.sum_const_zero, chartPoint_last,
        one_mul, zero_add, Pi.zero_apply] using hi
    · exact congrFun (congrFun hf i) k
  · intro hf
    exact funext (fun i => funext (fun j => congrFun (congrFun hf j.castSucc) i))

/-- The partial trace kernel uses all polynomial component conditions at
its full points and membership in the prescribed fiber subspace at the fixed point. -/
theorem mem_fixedPartialTraceEvaluation_ker_full
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (a : PointCoordinates K n p) (f : EulerRelations K n d) :
    f ∈ (fixedPartialTraceEvaluation y L a d).ker ↔
      eulerEvaluation a d f = 0 ∧ eulerTraceAt y d f ∈ L := by
  have h : eulerTraceEvaluation a d f = 0 ↔ eulerEvaluation a d f = 0 := by
    change f ∈ (eulerTraceEvaluation a d).ker ↔ f ∈ (eulerEvaluation a d).ker
    rw [eulerTraceEvaluation_ker_eq]
  change (eulerTraceEvaluation a d f, L.mkQ (eulerTraceAt y d f)) = 0 ↔ _
  simp only [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, h]

/-- Reduced and full Euler evaluation have kernels of the same dimension. -/
theorem eulerTraceEvaluation_kernel_finrank (a : PointCoordinates K n p) (d : ℕ) :
    finrank K (eulerTraceEvaluation a d).ker = finrank K (eulerEvaluation a d).ker :=
  (LinearEquiv.ofEq _ _ (eulerTraceEvaluation_ker_eq a d)).finrank_eq

/-- Full Euler evaluation vanishes exactly when all polynomial components do. -/
theorem eulerEvaluation_eq_zero_iff (a : PointCoordinates K n p)
    (f : EulerRelations K n d) :
    eulerEvaluation a d f = 0 ↔
      ∀ i j, eval (chartPoint K a i) (f.val j).val = 0 := by
  constructor
  · intro h i j
    exact congrFun (congrFun h j) i
  · intro h
    exact funext (fun j => funext (fun i => h i j))

/-- The polynomial coordinate action transports the vanishing conditions. -/
theorem affineEulerEquiv_evaluation_eq_zero_iff [Infinite K]
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (a : PointCoordinates K n p) (f : EulerRelations K n d) :
    eulerEvaluation a d (affineEulerEquiv source target e d f) = 0 ↔
      eulerEvaluation (affineCoordinates source target e a) d f = 0 := by
  rw [eulerEvaluation_eq_zero_iff, eulerEvaluation_eq_zero_iff]
  constructor
  · intro hf i
    have h := eval_linearCoordinateTupleEquiv
      (affineHomogeneousEquiv source target e) f.val (chartPoint K a i)
    rw [affineHomogeneousEquiv_chartPoint] at h
    have hz : coordinateDualEquiv (affineHomogeneousEquiv source target e)
        (fun j => eval (chartPoint K (affineCoordinates source target e a) i)
          (f.val j).val) = 0 := by
      rw [← h]
      exact funext (hf i)
    have hz' := (coordinateDualEquiv (affineHomogeneousEquiv source target e)).injective
      (hz.trans (map_zero _).symm)
    intro j
    exact congrFun hz' j
  · intro hf i j
    have h := eval_linearCoordinateTupleEquiv
      (affineHomogeneousEquiv source target e) f.val (chartPoint K a i)
    rw [affineHomogeneousEquiv_chartPoint] at h
    have hz : (fun j =>
        eval (chartPoint K (affineCoordinates source target e a) i) (f.val j).val) = 0 :=
      funext (hf i)
    rw [hz, map_zero] at h
    exact congrFun h j

/-- Affine transformations identify the spaces of polynomial Euler relations
vanishing at the corresponding point configurations. -/
def affineEulerKernelEquiv [Infinite K]
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (a : PointCoordinates K n p) (d : ℕ) :
    (eulerEvaluation (affineCoordinates source target e a) d).ker ≃ₗ[K]
      (eulerEvaluation a d).ker where
  toFun f := ⟨affineEulerEquiv source target e d f.val,
    (affineEulerEquiv_evaluation_eq_zero_iff source target e a f.val).mpr f.property⟩
  invFun f := ⟨(affineEulerEquiv source target e d).symm f.val, by
    apply (affineEulerEquiv_evaluation_eq_zero_iff source target e a _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((affineEulerEquiv source target e d).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((affineEulerEquiv source target e d).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((affineEulerEquiv source target e d).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((affineEulerEquiv source target e d).map_smul c f.val)

/-- Lifting a parameter polynomial to a configuration with one extra point. -/
theorem eval_rename_castSucc (D : MvPolynomial (Fin p × Fin n) K)
    (a : PointCoordinates K n (p + 1)) :
    eval a (rename (fun ij => (ij.1.castSucc, ij.2)) D) =
      eval (restrictPoints a Fin.castSucc) D := by
  rw [eval_rename]
  rfl

/-- The independent maximal-rank assertions at adjacent point counts can be
realized by a configuration whose last point has any prescribed position. -/
theorem exists_fixedPoint_euler_kernel_dimensions [CharZero K]
    (y : Fin n → K) (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1)) :
    ∃ a : PointCoordinates K n p,
      finrank K (eulerTraceEvaluation a d).ker =
        finrank K (EulerRelations K n d) - n * p ∧
      finrank K (eulerTraceEvaluation (snocPoints a y) d).ker =
        finrank K (EulerRelations K n d) - n * (p + 1) := by
  obtain ⟨D₀, hD₀, hgood₀⟩ := generic_eulerEvaluation_kernel_finrank (by omega) h₀
  obtain ⟨D₁, hD₁, hgood₁⟩ := generic_eulerEvaluation_kernel_finrank hp h₁
  let D₀' := rename (fun ij : Fin p × Fin n => (ij.1.castSucc, ij.2)) D₀
  have hD₀' : ∃ b : PointCoordinates K n (p + 1), eval b D₀' ≠ 0 := by
    obtain ⟨a, ha⟩ := hD₀
    refine ⟨snocPoints a (fun _ => 0), ?_⟩
    simpa only [D₀', eval_rename_castSucc, restrict_snocPoints_castSucc] using ha
  obtain ⟨b, hb₀, hb₁⟩ := principal_opens_meet D₀' D₁ hD₀' hD₁
  let z : Fin n → K := fun j => b (Fin.last p, j)
  let a := affineCoordinates z y (LinearEquiv.refl K (Fin n → K))
    (restrictPoints b Fin.castSucc)
  have hsnoc : snocPoints a y =
      affineCoordinates z y (LinearEquiv.refl K (Fin n → K)) b := by
    funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [snocPoints, affineCoordinates, z]
    · simp [snocPoints, a, affineCoordinates, restrictPoints]
  refine ⟨a, ?_, ?_⟩
  · exact (eulerTraceEvaluation_kernel_finrank a d).trans
      ((affineEulerKernelEquiv z y (LinearEquiv.refl K _) _ d).finrank_eq.trans
        (hgood₀ _ (by simpa only [D₀', eval_rename_castSucc] using hb₀)))
  · calc
      finrank K (eulerTraceEvaluation (snocPoints a y) d).ker =
          finrank K (eulerTraceEvaluation
            (affineCoordinates z y (LinearEquiv.refl K _) b) d).ker :=
        congrArg (fun c : PointCoordinates K n (p + 1) =>
          finrank K (eulerTraceEvaluation c d).ker) hsnoc
      _ = finrank K (eulerEvaluation
          (affineCoordinates z y (LinearEquiv.refl K _) b) d).ker :=
        eulerTraceEvaluation_kernel_finrank _ d
      _ = finrank K (eulerEvaluation b d).ker :=
        (affineEulerKernelEquiv z y (LinearEquiv.refl K _) b d).finrank_eq
      _ = _ := hgood₁ b hb₁

/-- Appending a point adds its trace evaluation to the joint kernel. -/
theorem eulerTraceEvaluation_snoc_ker (a : PointCoordinates K n p)
    (y : Fin n → K) (d : ℕ) :
    (eulerTraceEvaluation (snocPoints a y) d).ker =
      ((eulerTraceEvaluation a d).prod (eulerTraceAt y d)).ker := by
  ext f
  change eulerTraceEvaluation (snocPoints a y) d f = 0 ↔
    (eulerTraceEvaluation a d f, eulerTraceAt y d f) = 0
  rw [Prod.mk_eq_zero]
  constructor
  · intro h
    constructor
    · funext i j
      simpa [eulerTraceEvaluation, eulerTraceAt, snocPoints] using
        congrFun (congrFun h i.castSucc) j
    · funext j
      simpa [eulerTraceEvaluation, eulerTraceAt, snocPoints] using
        congrFun (congrFun h (Fin.last p)) j
  · rintro ⟨ha, hy⟩
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa [eulerTraceEvaluation, eulerTraceAt, snocPoints] using congrFun hy j
    · simpa [eulerTraceEvaluation, eulerTraceAt, snocPoints] using
        congrFun (congrFun ha k) j

/-- Adjacent ideal-generation assertions make evaluation at a prescribed
point have maximal rank on the relations vanishing at the other points. -/
theorem exists_fixedPoint_euler_restriction_maximalRank [CharZero K]
    (y : Fin n → K) (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1)) :
    ∃ a : PointCoordinates K n p,
      finrank K (eulerTraceEvaluation a d).ker =
        finrank K (EulerRelations K n d) - n * p ∧
      HasMaximalRank ((eulerTraceAt y d).comp (eulerTraceEvaluation a d).ker.subtype) := by
  obtain ⟨a, ha, hay⟩ := exists_fixedPoint_euler_kernel_dimensions y hp h₀ h₁
  refine ⟨a, ha, ?_⟩
  let g := (eulerTraceAt y d).comp (eulerTraceEvaluation a d).ker.subtype
  have hk : finrank K g.ker = finrank K (EulerRelations K n d) - n * (p + 1) := by
    calc
      finrank K g.ker = finrank K
          ((eulerTraceEvaluation a d).prod (eulerTraceAt y d)).ker :=
        (prodKernelEquiv (eulerTraceEvaluation a d) (eulerTraceAt y d)).finrank_eq.symm
      _ = finrank K (eulerTraceEvaluation (snocPoints a y) d).ker :=
        (LinearEquiv.ofEq _ _ (eulerTraceEvaluation_snoc_ker a y d)).finrank_eq.symm
      _ = _ := hay
  apply (maximalRank_iff_rank_eq_min g).mpr
  have hr := g.finrank_range_add_finrank_ker
  rw [ha, hk] at hr
  have hn : finrank K (Fin n → K) = n := by simp
  rw [ha, hn]
  simp only [Nat.mul_add, Nat.mul_one] at hr
  omega

end IdealGeneration
