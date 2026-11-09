module

public import IdealGeneration.NormalCoefficientRecovery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual normal-linear elimination of the cubic middle map in (B.1) and (B.2). -/

noncomputable section
namespace IdealGeneration.CubicMiddle

open MvPolynomial NormalDegree

variable {K : Type*} [Field K] {m p q : ℕ} (C : ConeConfiguration K 2 m p q)

abbrev ResidualSource := Fin (2 + m) → C.residualPiece 3
abbrev TraceSource := Fin 2 → C.tracePiece 3

/-- The form obtained by multiplying the residual cubics by all coordinates. -/
def residualFormMap : ResidualSource C →ₗ[K] Forms K (2 + m) 4 :=
  (C.residualPiece 4).subtype.comp (C.residualMultiplication 3)

/-- The residual products whose upper normal degrees have canceled. -/
def eliminatedSource : Submodule K (ResidualSource C) :=
  (weightedHomogeneousSubmodule K (normalWeight 2 m) 1).comap
    ((Forms K (2 + m) 4).subtype.comp (residualFormMap C))

theorem mem_eliminatedSource (u : ResidualSource C) :
    u ∈ eliminatedSource C ↔
      (residualFormMap C u).val.IsWeightedHomogeneous (normalWeight 2 m) 1 := Iff.rfl

/-- The two trace-cubic coefficients of the actual residual product. -/
def phi : eliminatedSource C →ₗ[K] (Fin 2 → Forms K m 3) :=
  (linearCoefficientMap K 2 m 3).comp ((residualFormMap C).comp (eliminatedSource C).subtype)

/-- The residual product is reconstructed from its two normal-linear coefficients. -/
theorem phi_reconstruct (u : eliminatedSource C) :
    normalLinearProduct K 2 m 3 (phi C u) = residualFormMap C u.val :=
  normalLinearProduct_coefficient K 2 m (residualFormMap C u.val)
    ((mem_eliminatedSource C u.val).mp u.property)

/-- Evaluate a normal-linear coefficient tuple at the trace points. -/
def traceEvaluation : (Fin 2 → Forms K m 3) →ₗ[K] (Fin q → Fin 2 → K) where
  toFun u i k := eval (C.trace i) (u k).val
  map_add' u v := by ext i k; simp
  map_smul' r u := by ext i k; simp

/-- The actual eliminated evaluation map. -/
def evaluation : eliminatedSource C →ₗ[K] (Fin q → Fin 2 → K) :=
  (traceEvaluation C).comp (phi C)

theorem middle_val (u : ResidualSource C) (v : TraceSource C) :
    (C.middleMultiplication 3 (u, v)).val = residualFormMap C u +
      normalLinearProduct K 2 m 3 (fun k => (v k).val) := rfl

private theorem residualForm_eq_neg (x : (C.middleMultiplication 3).ker) :
    residualFormMap C x.val.1 =
      -normalLinearProduct K 2 m 3 (fun k => (x.val.2 k).val) := by
  have h := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
  change (C.middleMultiplication 3 (x.val.1, x.val.2)).val = 0 at h
  rw [middle_val] at h
  exact eq_neg_of_add_eq_zero_left h

private def eliminatedPart (x : (C.middleMultiplication 3).ker) : eliminatedSource C :=
  ⟨x.val.1, (mem_eliminatedSource C x.val.1).mpr (by
    rw [residualForm_eq_neg C x]
    exact (normalLinearProduct_weighted K 2 m (fun k => (x.val.2 k).val)).neg)⟩

private theorem phi_eliminatedPart (x : (C.middleMultiplication 3).ker) :
    phi C (eliminatedPart C x) = -(fun k => (x.val.2 k).val) := by
  change linearCoefficientMap K 2 m 3 (residualFormMap C x.val.1) = _
  rw [residualForm_eq_neg C x, map_neg, linearCoefficientMap_product]

private theorem evaluation_eliminatedPart_zero (x : (C.middleMultiplication 3).ker) :
    evaluation C (eliminatedPart C x) = 0 := by
  funext i k
  change eval (C.trace i) ((phi C (eliminatedPart C x) k).val) = 0
  rw [phi_eliminatedPart]
  change eval (C.trace i) (-(x.val.2 k).val.val) = 0
  rw [map_neg, (C.mem_tracePiece _).mp (x.val.2 k).property i, neg_zero]

private def traceCorrection (x : (evaluation C).ker) : TraceSource C := fun k =>
  ⟨-(phi C x.val k), (C.mem_tracePiece _).mpr (fun i => by
    have h := congrFun (congrFun (LinearMap.mem_ker.mp x.property) i) k
    change eval (C.trace i) (phi C x.val k).val = 0 at h
    change eval (C.trace i) (-(phi C x.val k).val) = 0
    rw [map_neg, h, neg_zero])⟩

private theorem middle_traceCorrection_zero (x : (evaluation C).ker) :
    C.middleMultiplication 3 (x.val.val, traceCorrection C x) = 0 := by
  apply Subtype.ext
  rw [middle_val]
  change residualFormMap C x.val.val + normalLinearProduct K 2 m 3 (-(phi C x.val)) = 0
  rw [map_neg, phi_reconstruct, add_neg_cancel]

/-- Kernel of the actual middle multiplication is exactly the kernel of its
normal-linear residual evaluation. The trace correction is uniquely recovered. -/
def middleKernelEquiv : (C.middleMultiplication 3).ker ≃ₗ[K] (evaluation C).ker where
  toFun x := ⟨eliminatedPart C x, LinearMap.mem_ker.mpr (evaluation_eliminatedPart_zero C x)⟩
  invFun x := ⟨(x.val.val, traceCorrection C x), LinearMap.mem_ker.mpr (middle_traceCorrection_zero C x)⟩
  left_inv x := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext k
    apply Subtype.ext
    change -(phi C (eliminatedPart C x) k) = (x.val.2 k).val
    rw [phi_eliminatedPart]
    simp
  right_inv x := Subtype.ext (Subtype.ext rfl)
  map_add' x y := Subtype.ext (Subtype.ext rfl)
  map_smul' r x := Subtype.ext (Subtype.ext rfl)

/-- A cone normal imposes a scalar equation on the value at its support. -/
def normalPairing (i : Fin p) : (Fin q → Fin 2 → K) →ₗ[K] K where
  toFun a := ∑ k, C.normal i k * a (C.support i) k
  map_add' a b := by
    simp [Fin.sum_univ_two]
    ring
  map_smul' r a := by
    simp [Fin.sum_univ_two]
    ring

/-- The allowed values at the trace points from (B.2). -/
def allowedValues : Submodule K (Fin q → Fin 2 → K) :=
  ⨅ i, (normalPairing C i).ker

private theorem eval_normalLinearProduct (u : Fin 2 → Forms K m 3) (i : Fin p) :
    eval (C.point i) (normalLinearProduct K 2 m 3 u).val =
      C.height i ^ 3 * ∑ k, C.normal i k * eval (C.trace (C.support i)) (u k).val := by
  rw [normalLinearProduct_val, map_sum]
  simp only [map_mul, eval_X, eval_coneExtend, ConeConfiguration.point,
    Fin.addCases_left, Fin.addCases_right]
  have h (k : Fin 2) : eval (fun j => C.height i * C.trace (C.support i) j) (u k).val =
      C.height i ^ 3 * eval (C.trace (C.support i)) (u k).val :=
    homogeneous_eval_scale (u k).property _ _
  simp_rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The evaluated coefficients satisfy every cone normal equation. -/
theorem evaluation_mem_allowedValues (hheight : ∀ i, C.height i ≠ 0)
    (u : eliminatedSource C) : evaluation C u ∈ allowedValues C := by
  simp only [allowedValues, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i
  have h := (C.mem_conePiece _).mp (C.residualMultiplication 3 u.val).property.1 i
  change eval (C.point i) (residualFormMap C u.val).val = 0 at h
  rw [← phi_reconstruct C u, eval_normalLinearProduct C] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hheight i))

/-- The map `D` with codomain restricted to its allowed values. -/
def allowedEvaluation (hheight : ∀ i, C.height i ≠ 0) : eliminatedSource C →ₗ[K] allowedValues C :=
  (evaluation C).codRestrict (allowedValues C) (evaluation_mem_allowedValues C hheight)

/-- The middle kernel is identified with the kernel of the actual map `D`. -/
def middleKernelAllowedEquiv (hheight : ∀ i, C.height i ≠ 0) :
    (C.middleMultiplication 3).ker ≃ₗ[K] (allowedEvaluation C hheight).ker :=
  (middleKernelEquiv C).trans (LinearEquiv.ofEq _ _ (by
    ext u
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h))

end IdealGeneration.CubicMiddle
