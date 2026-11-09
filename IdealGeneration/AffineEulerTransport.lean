module

public import IdealGeneration.MultiplicationOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Linear coordinate changes on polynomial Euler relations

The coordinate substitutions in this file act on the actual homogeneous
polynomials.  The coefficient tuples transform by the dual linear action.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] [Infinite K] {m n d p : ℕ}

/-- A linear change of homogeneous coordinates, written as polynomial substitution. -/
def linearCoordinateSubstitution (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    Poly K m →ₐ[K] Poly K m :=
  aeval fun i => polynomialOfLinear ((LinearMap.proj i).comp e.toLinearMap)

omit [Infinite K] in
@[simp] theorem eval_linearCoordinateSubstitution
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (z : Fin m → K) (f : Poly K m) :
    eval z (linearCoordinateSubstitution e f) = eval (e z) f := by
  have h : (eval z).comp (linearCoordinateSubstitution e).toRingHom = eval (e z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [linearCoordinateSubstitution]
    · intro i
      simp [linearCoordinateSubstitution, eval_polynomialOfLinear]
  exact congrArg (fun F : Poly K m →+* K => F f) h

omit [Infinite K] in
/-- Linear substitution preserves total homogeneity. -/
theorem linearCoordinateSubstitution_homogeneous
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) {f : Poly K m}
    (hf : f.IsHomogeneous d) : (linearCoordinateSubstitution e f).IsHomogeneous d := by
  have hg : ∀ i : Fin m,
      (polynomialOfLinear ((LinearMap.proj i).comp e.toLinearMap)).IsHomogeneous 1 := by
    intro i
    apply IsHomogeneous.sum
    intro j _
    exact (isHomogeneous_X K j).C_mul _
  simpa only [one_mul, linearCoordinateSubstitution] using hf.aeval _ hg

/-- A coordinate change gives an isomorphism of every homogeneous piece. -/
def linearCoordinateFormsEquiv
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (d : ℕ) :
    Forms K m d ≃ₗ[K] Forms K m d where
  toFun f := ⟨linearCoordinateSubstitution e f.val,
    linearCoordinateSubstitution_homogeneous e f.property⟩
  invFun f := ⟨linearCoordinateSubstitution e.symm f.val,
    linearCoordinateSubstitution_homogeneous e.symm f.property⟩
  left_inv f := by
    apply Subtype.ext
    apply MvPolynomial.funext
    intro z
    simp
  right_inv f := by
    apply Subtype.ext
    apply MvPolynomial.funext
    intro z
    simp
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' c f := Subtype.ext (map_smul _ _ _)

/-- A tuple is the list of values of a linear map on the coordinate basis. -/
def tupleLinearEquiv {V : Type*} [AddCommGroup V] [Module K V] :
    (Fin m → V) ≃ₗ[K] ((Fin m → K) →ₗ[K] V) :=
  (Pi.basisFun K (Fin m)).constr K

omit [Infinite K] in
@[simp] theorem tupleLinearEquiv_apply {V : Type*} [AddCommGroup V] [Module K V]
    (f : Fin m → V) (z : Fin m → K) :
    tupleLinearEquiv f z = ∑ i, z i • f i := by
  simp [tupleLinearEquiv, Basis.constr_apply_fintype]

/-- The transpose action on coordinate-value tuples. -/
def coordinateDualEquiv (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    (Fin m → K) ≃ₗ[K] (Fin m → K) :=
  tupleLinearEquiv.trans ((e.symm.arrowCongr (LinearEquiv.refl K K)).trans
    tupleLinearEquiv.symm)

omit [Infinite K] in
@[simp] theorem coordinateDualEquiv_pairing
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (v z : Fin m → K) :
    tupleLinearEquiv (coordinateDualEquiv e v) z = tupleLinearEquiv v (e z) := by
  simp [coordinateDualEquiv]

omit [Infinite K] in
/-- Coordinates of the dual action are given by the transpose matrix. -/
theorem coordinateDualEquiv_apply
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (v : Fin m → K) (j : Fin m) :
    coordinateDualEquiv e v j = ∑ i, e (Pi.single j 1) i * v i := by
  change tupleLinearEquiv v (e ((Pi.basisFun K (Fin m)) j)) = _
  simp [tupleLinearEquiv_apply, smul_eq_mul]

omit [Infinite K] in
/-- Applying the coordinate dual construction twice recovers the original map. -/
theorem coordinateDualEquiv_involutive
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    coordinateDualEquiv (coordinateDualEquiv e) = e := by
  ext z i
  rw [coordinateDualEquiv_apply]
  simp only [coordinateDualEquiv_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h := congrArg (fun v : Fin m → K => e v i)
    ((Pi.basisFun K (Fin m)).sum_repr z)
  simpa [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- Coordinate substitution together with the corresponding coefficient action. -/
def linearCoordinateTupleEquiv
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (d : ℕ) :
    (Fin m → Forms K m d) ≃ₗ[K] (Fin m → Forms K m d) :=
  tupleLinearEquiv.trans ((e.symm.arrowCongr (linearCoordinateFormsEquiv e d)).trans
    tupleLinearEquiv.symm)

@[simp] theorem linearCoordinateTupleEquiv_pairing
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (f : Fin m → Forms K m d)
    (z : Fin m → K) :
    tupleLinearEquiv (linearCoordinateTupleEquiv e d f) z =
      linearCoordinateFormsEquiv e d (tupleLinearEquiv f (e z)) := by
  simp [linearCoordinateTupleEquiv]

/-- Evaluation of the transformed tuple is the dual change of the evaluated tuple. -/
theorem eval_linearCoordinateTupleEquiv
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (f : Fin m → Forms K m d)
    (z : Fin m → K) :
    (fun j => eval z (linearCoordinateTupleEquiv e d f j).val) =
      coordinateDualEquiv e (fun j => eval (e z) (f j).val) := by
  apply (tupleLinearEquiv (K := K) (m := m) (V := K)).injective
  apply LinearMap.ext
  intro w
  rw [coordinateDualEquiv_pairing]
  have h := congrArg (evaluationLinear K m d z)
    (linearCoordinateTupleEquiv_pairing e f w)
  simpa [tupleLinearEquiv_apply, evaluationLinear, linearCoordinateFormsEquiv, map_sum] using h

/-- Multiplication by the coordinate variables commutes with the tuple change. -/
theorem linearCoordinateTupleEquiv_multiplication
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (f : Fin m → Forms K m d) :
    formMultiplication K m d (linearCoordinateTupleEquiv e d f) =
      linearCoordinateFormsEquiv e (d + 1) (formMultiplication K m d f) := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro z
  have h := congrArg (fun v : Fin m → K => tupleLinearEquiv v z)
    (eval_linearCoordinateTupleEquiv e f z)
  rw [coordinateDualEquiv_pairing] at h
  simpa [formMultiplication_val, map_sum, map_mul, tupleLinearEquiv_apply,
    linearCoordinateFormsEquiv, smul_eq_mul] using h

/-- Euler relations are preserved by every invertible linear coordinate change. -/
def linearCoordinateEulerEquiv
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) (d : ℕ) :
    EulerRelations K n d ≃ₗ[K] EulerRelations K n d where
  toFun f := ⟨linearCoordinateTupleEquiv e d f.val, by
    rw [LinearMap.mem_ker, linearCoordinateTupleEquiv_multiplication, f.property,
      map_zero]⟩
  invFun f := ⟨(linearCoordinateTupleEquiv e d).symm f.val, by
    apply (linearCoordinateFormsEquiv e (d + 1)).injective
    rw [map_zero, ← linearCoordinateTupleEquiv_multiplication,
      LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((linearCoordinateTupleEquiv e d).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((linearCoordinateTupleEquiv e d).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((linearCoordinateTupleEquiv e d).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((linearCoordinateTupleEquiv e d).map_smul c f.val)

/-- The homogeneous linear map extending an affine map between two chosen origins. -/
def affineHomogeneousEquiv (source target : Fin n → K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K) where
  toFun z := Fin.snoc
    (e (fun j => z j.castSucc - z (Fin.last n) * source j) + z (Fin.last n) • target)
    (z (Fin.last n))
  invFun z := Fin.snoc
    (e.symm (fun j => z j.castSucc - z (Fin.last n) * target j) + z (Fin.last n) • source)
    (z (Fin.last n))
  left_inv z := by
    have h : (fun j =>
        (e (fun k => z k.castSucc - z (Fin.last n) * source k) j +
          z (Fin.last n) * target j) - z (Fin.last n) * target j) =
        e (fun k => z k.castSucc - z (Fin.last n) * source k) := by
      funext j
      ring
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, h, LinearEquiv.symm_apply_apply]
      ring
  right_inv z := by
    have h : (fun j =>
        (e.symm (fun k => z k.castSucc - z (Fin.last n) * target k) j +
          z (Fin.last n) * source j) - z (Fin.last n) * source j) =
        e.symm (fun k => z k.castSucc - z (Fin.last n) * target k) := by
      funext j
      ring
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, h, LinearEquiv.apply_symm_apply]
      ring
  map_add' z w := by
    have h : (fun j => (z + w) j.castSucc - (z + w) (Fin.last n) * source j) =
        (fun j => z j.castSucc - z (Fin.last n) * source j) +
        (fun j => w j.castSucc - w (Fin.last n) * source j) := by
      funext j
      simp only [Pi.add_apply]
      ring
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [Pi.add_apply] at h
      simp only [Pi.add_apply, Fin.snoc_castSucc]
      rw [h, map_add]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  map_smul' a z := by
    have h : (fun j => (a • z) j.castSucc - (a • z) (Fin.last n) * source j) =
        a • (fun j => z j.castSucc - z (Fin.last n) * source j) := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp only [Pi.smul_apply, smul_eq_mul] at h
      simp only [Pi.smul_apply, smul_eq_mul, Fin.snoc_castSucc]
      rw [h, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

omit [Infinite K] in
/-- Explicit formula for the homogeneous extension. -/
theorem affineHomogeneousEquiv_apply (source target : Fin n → K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (z : Fin (n + 1) → K) :
    affineHomogeneousEquiv source target e z =
      Fin.snoc (e (fun j => z j.castSucc - z (Fin.last n) * source j) +
        z (Fin.last n) • target) (z (Fin.last n)) := rfl

/-- Affine point coordinates transported by the chosen affine map. -/
def affineCoordinates (source target : Fin n → K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (a : PointCoordinates K n p) :
    PointCoordinates K n p :=
  fun ij => (e (fun j => a (ij.1, j) - source j) + target) ij.2

omit [Infinite K] in
@[simp] theorem affineHomogeneousEquiv_chartPoint
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (a : PointCoordinates K n p) (i : Fin p) :
    affineHomogeneousEquiv source target e (chartPoint K a i) =
      chartPoint K (affineCoordinates source target e a) i := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [affineHomogeneousEquiv, affineCoordinates]

omit [Infinite K] in
@[simp] theorem affineHomogeneousEquiv_origin
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    affineHomogeneousEquiv source target e (Fin.snoc source 1) = Fin.snoc target 1 := by
  have hzero : (fun j : Fin n => source j - source j) = 0 := by
    funext j
    simp
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [affineHomogeneousEquiv]
  · simp only [affineHomogeneousEquiv_apply, Fin.snoc_castSucc,
      Fin.snoc_last, one_mul, one_smul, hzero, map_zero, zero_add]

omit [Infinite K] in
/-- The linear part acts on the first coordinate basis vectors. -/
theorem affineHomogeneousEquiv_single_castSucc
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (j : Fin n) :
    affineHomogeneousEquiv source target e (Pi.single j.castSucc 1) =
      Fin.snoc (e (Pi.single j 1)) 0 := by
  have h : (fun k : Fin n =>
      (Pi.single j.castSucc 1 : Fin (n + 1) → K) k.castSucc -
        (Pi.single j.castSucc 1 : Fin (n + 1) → K) (Fin.last n) * source k) =
      Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, Fin.castSucc_inj]
  have hlast : (Pi.single j.castSucc 1 : Fin (n + 1) → K) (Fin.last n) = 0 := by
    simp
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [affineHomogeneousEquiv_apply, Fin.snoc_last, hlast]
  · simp only [affineHomogeneousEquiv_apply, Fin.snoc_castSucc]
    rw [h, hlast, zero_smul, add_zero]

omit [Infinite K] in
/-- On the first components, the dual homogeneous action is exactly the dual
of the affine linear part. -/
theorem coordinateDualEquiv_affine_castSucc
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (v : Fin (n + 1) → K) (j : Fin n) :
    coordinateDualEquiv (affineHomogeneousEquiv source target e) v j.castSucc =
      coordinateDualEquiv e (fun i => v i.castSucc) j := by
  rw [coordinateDualEquiv_apply, Fin.sum_univ_castSucc,
    affineHomogeneousEquiv_single_castSucc]
  simp [coordinateDualEquiv_apply]

/-- The actual action on homogeneous Euler relations induced by an affine map. -/
abbrev affineEulerEquiv (source target : Fin n → K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (d : ℕ) :=
  linearCoordinateEulerEquiv (affineHomogeneousEquiv source target e) d

/-- Fiber values at the chosen source point are transported by the full dual
linear group on the first components. -/
theorem affineEulerEquiv_evaluation
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (f : EulerRelations K n d) :
    (fun j : Fin n =>
      eval (Fin.snoc source 1) ((affineEulerEquiv source target e d f).val j.castSucc).val) =
      coordinateDualEquiv e
        (fun j : Fin n => eval (Fin.snoc target 1) (f.val j.castSucc).val) := by
  have h := eval_linearCoordinateTupleEquiv
    (affineHomogeneousEquiv source target e) f.val (Fin.snoc source 1)
  rw [affineHomogeneousEquiv_origin] at h
  funext j
  exact (congrFun h j.castSucc).trans
    (coordinateDualEquiv_affine_castSucc source target e _ j)

/-- The same fiber formula holds at every affine point. -/
theorem affineEulerEquiv_evaluation_at
    (source target : Fin n → K) (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (z : Fin n → K) (f : EulerRelations K n d) :
    (fun j : Fin n =>
      eval (Fin.snoc z 1) ((affineEulerEquiv source target e d f).val j.castSucc).val) =
      coordinateDualEquiv e
        (fun j : Fin n => eval (Fin.snoc (e (z - source) + target) 1)
          (f.val j.castSucc).val) := by
  have hz : affineHomogeneousEquiv source target e (Fin.snoc z 1) =
      Fin.snoc (e (z - source) + target) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [affineHomogeneousEquiv_apply, Fin.snoc_last]
    · simp only [affineHomogeneousEquiv_apply, Fin.snoc_castSucc,
        Fin.snoc_last, one_mul, one_smul]
      rfl
  have h := eval_linearCoordinateTupleEquiv
    (affineHomogeneousEquiv source target e) f.val (Fin.snoc z 1)
  rw [hz] at h
  funext j
  exact (congrFun h j.castSucc).trans
    (coordinateDualEquiv_affine_castSucc source target e _ j)

end IdealGeneration
