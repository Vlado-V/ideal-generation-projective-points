module

public import IdealGeneration.Points
public import IdealGeneration.Euler
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Multiplication for actual point ideals

The source is a tuple of degree-`d` equations, one for each coordinate variable.
This is the coordinate presentation of tensoring with the space of linear forms.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] {n p d : ℕ}

/-- Multiplication by all coordinate variables in degree `d`. -/
def formMultiplication (K : Type*) [Field K] (n d : ℕ) :
    (Fin n → Forms K n d) →ₗ[K] Forms K n (d + 1) where
  toFun f := ⟨∑ j, X j * (f j).val, by
    apply IsHomogeneous.sum
    intro j _
    simpa [Nat.add_comm] using (isHomogeneous_X (R := K) j).mul (f j).property⟩
  map_add' f g := by
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    simp [Finset.smul_sum]

@[simp] theorem formMultiplication_val (f : Fin n → Forms K n d) :
    (formMultiplication K n d f).val = ∑ j, X j * (f j).val := rfl

/-- The actual multiplication map from degree-`d` equations to degree `d+1`. -/
def pointMultiplication (a : PointCoordinates K n p) (d : ℕ) :
    (Fin (n + 1) → pointDegreePiece K a d) →ₗ[K] pointDegreePiece K a (d + 1) where
  toFun f := ⟨formMultiplication K (n + 1) d (fun j => (f j).val), by
    apply (mem_pointDegreePiece a _).mpr
    intro i
    simp only [formMultiplication_val, map_sum, map_mul, eval_X]
    apply Finset.sum_eq_zero
    intro j _
    rw [(mem_pointDegreePiece a _).mp (f j).property i, mul_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    exact (formMultiplication K (n + 1) d).map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    exact (formMultiplication K (n + 1) d).map_smul c _

@[simp] theorem pointMultiplication_val (a : PointCoordinates K n p)
    (f : Fin (n + 1) → pointDegreePiece K a d) :
    (pointMultiplication a d f).val.val = ∑ j, X j * (f j).val.val := rfl

/-- Maximal rank for a finite-dimensional map, expressed without rank subtraction. -/
def HasMaximalRank {V W : Type*} [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (f : V →ₗ[K] W) : Prop :=
  Function.Injective f ∨ Function.Surjective f

/-- The Euler map on the fibers at the points. -/
def fiberMultiplication (a : PointCoordinates K n p) :
    (Fin (n + 1) → Fin p → K) →ₗ[K] (Fin p → K) where
  toFun f i := ∑ j, chartPoint K a i j * f j i
  map_add' f g := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    change (∑ j, chartPoint K a i j * (c * f j i)) =
      c * ∑ j, chartPoint K a i j * f j i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Evaluate each component of a tuple of forms. -/
def componentEvaluation (a : PointCoordinates K n p) (d : ℕ) :
    (Fin (n + 1) → Forms K (n + 1) d) →ₗ[K] (Fin (n + 1) → Fin p → K) :=
  LinearMap.pi (fun j => (pointEvaluation K a d).comp (LinearMap.proj j))

/-- The Euler square for actual homogeneous polynomials and point evaluations. -/
def pointEulerSquare (a : PointCoordinates K n p) (d : ℕ) :
    LinearSquare K (Fin (n + 1) → Forms K (n + 1) d)
      (Forms K (n + 1) (d + 1)) (Fin (n + 1) → Fin p → K) (Fin p → K) where
  top := formMultiplication K (n + 1) d
  left := componentEvaluation a d
  right := pointEvaluation K a (d + 1)
  bottom := fiberMultiplication a
  commutes f := by
    ext i
    simp [formMultiplication, componentEvaluation, fiberMultiplication,
      pointEvaluation, evaluationLinear]

/-- The top Euler map is onto in characteristic zero, by Euler's identity. -/
theorem formMultiplication_surjective [CharZero K] (n d : ℕ) :
    Function.Surjective (formMultiplication K n d) := by
  intro f
  let c : K := ((d + 1 : ℕ) : K)⁻¹
  let g : Fin n → Forms K n d := fun j =>
    ⟨c • pderiv j f.val, by
      apply (homogeneousSubmodule (Fin n) K d).smul_mem
      simpa using f.property.pderiv (i := j)⟩
  refine ⟨g, Subtype.ext ?_⟩
  change (∑ j : Fin n, X j * (c • pderiv j f.val)) = f.val
  simp only [mul_smul_comm, ← Finset.smul_sum]
  rw [f.property.sum_X_mul_pderiv]
  have hc : (d : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  simp [c, ← Nat.cast_smul_eq_nsmul K, smul_smul, hc]

/-- Scalar postulation makes componentwise evaluation surjective. -/
theorem componentEvaluation_surjective (a : PointCoordinates K n p)
    (h : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (componentEvaluation a d) := by
  intro y
  choose f hf using fun j => h (y j)
  refine ⟨f, ?_⟩
  funext j
  exact hf j

/-- Componentwise kernels agree with the kernel of componentwise evaluation. -/
def componentKernelEquiv (a : PointCoordinates K n p) (d : ℕ) :
    (Fin (n + 1) → pointDegreePiece K a d) ≃ₗ[K]
      LinearMap.ker (componentEvaluation a d) where
  toFun f := ⟨fun j => (f j).val, by
    ext j i
    exact (mem_pointDegreePiece a _).mp (f j).property i⟩
  invFun f j := ⟨f.val j, by
    apply (mem_pointDegreePiece a _).mpr
    intro i
    exact congrFun (congrFun f.property j) i⟩
  left_inv f := by ext j; rfl
  right_inv f := by rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/-- The top map on vertical kernels is point-ideal multiplication in coordinates. -/
theorem topOnKernel_componentKernelEquiv (a : PointCoordinates K n p) (d : ℕ)
    (f : Fin (n + 1) → pointDegreePiece K a d) :
    (pointEulerSquare a d).topOnKernel (componentKernelEquiv a d f) =
      pointMultiplication a d f := rfl

/-- Coordinate identification preserves injectivity. -/
theorem pointMultiplication_injective_iff (a : PointCoordinates K n p) (d : ℕ) :
    Function.Injective (pointMultiplication a d) ↔
      Function.Injective (pointEulerSquare a d).topOnKernel := by
  let e := componentKernelEquiv a d
  constructor
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact congrArg e (h hxy)
  · intro h x y hxy
    apply e.injective
    apply h
    exact hxy

/-- Coordinate identification preserves surjectivity. -/
theorem pointMultiplication_surjective_iff (a : PointCoordinates K n p) (d : ℕ) :
    Function.Surjective (pointMultiplication a d) ↔
      Function.Surjective (pointEulerSquare a d).topOnKernel := by
  let e := componentKernelEquiv a d
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨e x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    obtain ⟨x, rfl⟩ := e.surjective x
    exact ⟨x, hx⟩

/-- Lemma 2.2 for the actual multiplication and Euler evaluation maps. -/
theorem pointEuler_maximalRank_iff [CharZero K] (a : PointCoordinates K n p)
    (h : Function.Surjective (pointEvaluation K a d)) :
    HasMaximalRank (pointMultiplication a d) ↔
      HasMaximalRank (pointEulerSquare a d).leftOnKernel := by
  change (Function.Injective (pointMultiplication a d) ∨
    Function.Surjective (pointMultiplication a d)) ↔ _
  rw [pointMultiplication_injective_iff, pointMultiplication_surjective_iff]
  exact (pointEulerSquare a d).maximalRank_iff
    (formMultiplication_surjective (n + 1) d) (componentEvaluation_surjective a h)

end IdealGeneration
