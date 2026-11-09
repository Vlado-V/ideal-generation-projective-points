module

public import IdealGeneration.ConeRepresentatives
public import IdealGeneration.ShearAvoidance
public import IdealGeneration.RepresentativeNormalization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Moving finite projective configurations into an affine chart

A triangular linear coordinate change preserves homogeneous equations and their
coordinate multiplication maps. Nonzero rescaling then gives normalized chart
representatives.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {n p d : ℕ}

/-- A linear form involving the first coordinates. -/
def shearLinear (v : Fin n → K) : Poly K (n + 1) :=
  ∑ j, C (v j) * X j.castSucc

/-- A triangular change of homogeneous coordinates. -/
def shearChange (v : Fin n → K) : Poly K (n + 1) →ₐ[K] Poly K (n + 1) :=
  aeval (Fin.snoc (fun j => X j.castSucc) (X (Fin.last n) + shearLinear v))

@[simp] theorem shearChange_X_castSucc (v : Fin n → K) (j : Fin n) :
    shearChange v (X j.castSucc) = X j.castSucc := by simp [shearChange]

@[simp] theorem shearChange_X_last (v : Fin n → K) :
    shearChange v (X (Fin.last n)) = X (Fin.last n) + shearLinear v := by
  simp [shearChange]

@[simp] theorem shearChange_C (v : Fin n → K) (a : K) :
    shearChange v (C a) = C a := by simp [shearChange]

@[simp] theorem shearChange_linear (v w : Fin n → K) :
    shearChange v (shearLinear w) = shearLinear w := by simp [shearLinear]

@[simp] theorem shearLinear_neg (v : Fin n → K) : shearLinear (-v) = -shearLinear v := by
  simp [shearLinear, Finset.sum_neg_distrib]

/-- Opposite shears are inverse substitutions. -/
theorem shearChange_comp_neg (v : Fin n → K) :
    (shearChange v).comp (shearChange (-v)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- The shear is an automorphism of the polynomial algebra. -/
def shearEquiv (v : Fin n → K) : Poly K (n + 1) ≃ₐ[K] Poly K (n + 1) :=
  AlgEquiv.ofAlgHom (shearChange v) (shearChange (-v))
    (by simpa using shearChange_comp_neg v)
    (by simpa using shearChange_comp_neg (-v))

theorem shearChange_homogeneous (v : Fin n → K) {f : Poly K (n + 1)}
    (hf : f.IsHomogeneous d) : (shearChange v f).IsHomogeneous d := by
  have hg : ∀ i : Fin (n + 1),
      ((Fin.snoc (fun j : Fin n => (X j.castSucc : Poly K (n + 1)))
        (X (Fin.last n) + shearLinear v) : Fin (n + 1) → Poly K (n + 1)) i).IsHomogeneous 1 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      apply (isHomogeneous_X K _).add
      apply IsHomogeneous.sum
      intro j _
      exact (isHomogeneous_X K _).C_mul _
    · simpa using (isHomogeneous_X K j.castSucc)
  simpa only [one_mul, shearChange] using hf.aeval _ hg

/-- The shear restricts to each homogeneous degree. -/
def shearFormsEquiv (v : Fin n → K) (d : ℕ) :
    Forms K (n + 1) d ≃ₗ[K] Forms K (n + 1) d where
  toFun f := ⟨shearChange v f.val, shearChange_homogeneous v f.property⟩
  invFun f := ⟨shearChange (-v) f.val, shearChange_homogeneous (-v) f.property⟩
  left_inv f := Subtype.ext ((shearEquiv v).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((shearEquiv v).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The corresponding change of point coordinates. -/
def shearPoint (v : Fin n → K) (z : Fin (n + 1) → K) : Fin (n + 1) → K :=
  Fin.snoc (fun j => z j.castSucc) (z (Fin.last n) + ∑ j, v j * z j.castSucc)

@[simp] theorem eval_shearChange (v : Fin n → K) (z : Fin (n + 1) → K)
    (f : Poly K (n + 1)) : eval z (shearChange v f) = eval (shearPoint v z) f := by
  have h : (eval z).comp (shearChange v).toRingHom = eval (shearPoint v z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [shearPoint, shearLinear]
  exact congrArg (fun F : Poly K (n + 1) →+* K => F f) h

/-- Equation spaces move contravariantly with the point representatives. -/
def shearPieceEquiv (v : Fin n → K) (z : Fin p → Fin (n + 1) → K) (d : ℕ) :
    representativePiece K (fun i => shearPoint v (z i)) d ≃ₗ[K]
      representativePiece K z d where
  toFun f := ⟨shearFormsEquiv v d f.val, by
    apply (mem_representativePiece K z _).mpr
    intro i
    exact (eval_shearChange v (z i) f.val.val).trans
      ((mem_representativePiece K _ _).mp f.property i)⟩
  invFun f := ⟨(shearFormsEquiv v d).symm f.val, by
    apply (mem_representativePiece K _ _).mpr
    intro i
    rw [← eval_shearChange v (z i)]
    change eval (z i) ((shearFormsEquiv v d) ((shearFormsEquiv v d).symm f.val)).val = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (mem_representativePiece K z _).mp f.property i⟩
  left_inv f := Subtype.ext ((shearFormsEquiv v d).left_inv f.val)
  right_inv f := Subtype.ext ((shearFormsEquiv v d).right_inv f.val)
  map_add' f g := Subtype.ext ((shearFormsEquiv v d).map_add _ _)
  map_smul' a f := Subtype.ext ((shearFormsEquiv v d).map_smul a _)


/-- The elementary row operation on the tuple presenting multiplication. -/
def shearTupleEquiv {E : Type*} [AddCommGroup E] [Module K E]
    (v : Fin n → K) : (Fin (n + 1) → E) ≃ₗ[K] (Fin (n + 1) → E) where
  toFun f := Fin.snoc (fun j => f j.castSucc + v j • f (Fin.last n)) (f (Fin.last n))
  invFun f := Fin.snoc (fun j => f j.castSucc - v j • f (Fin.last n)) (f (Fin.last n))
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_add' f g := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [smul_add]
    abel
  map_smul' a f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [smul_add, smul_smul, mul_comm]

/-- Source change making the two coordinate multiplication maps commute. -/
def shearSourceEquiv (v : Fin n → K) (z : Fin p → Fin (n + 1) → K) (d : ℕ) :
    (Fin (n + 1) → representativePiece K (fun i => shearPoint v (z i)) d) ≃ₗ[K]
      (Fin (n + 1) → representativePiece K z d) :=
  (LinearEquiv.piCongrRight (fun _ => shearPieceEquiv v z d)).trans (shearTupleEquiv (E := representativePiece K z d) v)

/-- Coordinate substitution is compatible with multiplication of equations. -/
theorem shear_multiplication (v : Fin n → K) (z : Fin p → Fin (n + 1) → K)
    (f : Fin (n + 1) → representativePiece K (fun i => shearPoint v (z i)) d) :
    representativeMultiplication K z d (shearSourceEquiv v z d f) =
      shearPieceEquiv v z (d + 1)
        (representativeMultiplication K (fun i => shearPoint v (z i)) d f) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [representativeMultiplication_val, formMultiplication_val]
  change (∑ j, X j * (shearSourceEquiv v z d f j).val.val) =
    shearChange v (∑ j, X j * (f j).val.val)
  rw [map_sum]
  simp only [map_mul]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shearSourceEquiv, shearTupleEquiv, shearPieceEquiv, shearFormsEquiv,
    shearLinear, mul_add, add_mul, Finset.sum_mul, Finset.sum_add_distrib,
    mul_assoc, add_assoc]
  simp only [smul_eq_C_mul, add_comm]

/-- Conjugate multiplication maps have the same injectivity. -/
theorem shear_multiplication_injective_iff (v : Fin n → K)
    (z : Fin p → Fin (n + 1) → K) :
    Function.Injective (representativeMultiplication K z d) ↔
      Function.Injective (representativeMultiplication K (fun i => shearPoint v (z i)) d) := by
  constructor
  · intro h f g hfg
    apply (shearSourceEquiv v z d).injective
    apply h
    rw [shear_multiplication, shear_multiplication, hfg]
  · intro h f g hfg
    obtain ⟨f, rfl⟩ := (shearSourceEquiv v z d).surjective f
    obtain ⟨g, rfl⟩ := (shearSourceEquiv v z d).surjective g
    apply congrArg (shearSourceEquiv v z d)
    apply h
    apply (shearPieceEquiv v z (d + 1)).injective
    simpa only [← shear_multiplication] using hfg

/-- Conjugate multiplication maps have the same surjectivity. -/
theorem shear_multiplication_surjective_iff (v : Fin n → K)
    (z : Fin p → Fin (n + 1) → K) :
    Function.Surjective (representativeMultiplication K z d) ↔
      Function.Surjective (representativeMultiplication K (fun i => shearPoint v (z i)) d) := by
  constructor
  · intro h f
    obtain ⟨g, hg⟩ := h (shearPieceEquiv v z (d + 1) f)
    obtain ⟨g, rfl⟩ := (shearSourceEquiv v z d).surjective g
    refine ⟨g, (shearPieceEquiv v z (d + 1)).injective ?_⟩
    simpa only [← shear_multiplication] using hg
  · intro h f
    obtain ⟨f, rfl⟩ := (shearPieceEquiv v z (d + 1)).surjective f
    obtain ⟨g, hg⟩ := h f
    exact ⟨shearSourceEquiv v z d g, by rw [shear_multiplication, hg]⟩


/-- Every finite family of nonzero homogeneous representatives can be put in a
single normalized affine chart while preserving every degree of its equations
and both possible maximal-rank properties of multiplication. -/
theorem exists_chart_transport [Infinite K]
    (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0) :
    ∃ a : PointCoordinates K n p,
      (∀ d, Module.finrank K (representativePiece K z d) =
        Module.finrank K (pointDegreePiece K a d)) ∧
      (∀ d, Function.Injective (representativeMultiplication K z d) ↔
        Function.Injective (pointMultiplication a d)) ∧
      (∀ d, Function.Surjective (representativeMultiplication K z d) ↔
        Function.Surjective (pointMultiplication a d)) := by
  obtain ⟨v, hv⟩ := exists_shear_avoiding_representatives z hz
  let w : Fin p → Fin (n + 1) → K := fun i => shearPoint v (z i)
  have hw : ∀ i, w i (Fin.last n) ≠ 0 := by
    intro i
    simpa only [w, shearPoint, Fin.snoc_last] using hv i
  refine ⟨normalizedCoordinates w, ?_, ?_, ?_⟩
  · intro d
    exact (shearPieceEquiv v z d).finrank_eq.symm.trans (normalization_finrank w hw d)
  · intro d
    exact (shear_multiplication_injective_iff v z).trans
      (normalization_multiplication_injective_iff w hw)
  · intro d
    exact (shear_multiplication_surjective_iff v z).trans
      (normalization_multiplication_surjective_iff w hw)

/-- In particular, actual maximal-rank witnesses survive passage to a chart. -/
theorem exists_chart_maximalRank [Infinite K]
    (z : Fin p → Fin (n + 1) → K) (hz : ∀ i, z i ≠ 0)
    (h : HasMaximalRank (representativeMultiplication K z d)) :
    ∃ a : PointCoordinates K n p, HasMaximalRank (pointMultiplication a d) := by
  obtain ⟨a, _, hi, hs⟩ := exists_chart_transport z hz
  exact ⟨a, h.elim (fun h => Or.inl ((hi d).mp h)) (fun h => Or.inr ((hs d).mp h))⟩


/-- The chart transport with an arbitrary positive count of homogeneous variables. -/
theorem exists_chart_transport_of_pos [Infinite K] {N : ℕ}
    (hN : 0 < N) (z : Fin p → Fin N → K) (hz : ∀ i, z i ≠ 0) :
    ∃ a : PointCoordinates K (N - 1) p,
      (∀ d, Module.finrank K (representativePiece K z d) =
        Module.finrank K (pointDegreePiece K a d)) ∧
      (∀ d, Function.Injective (representativeMultiplication K z d) ↔
        Function.Injective (pointMultiplication a d)) ∧
      (∀ d, Function.Surjective (representativeMultiplication K z d) ↔
        Function.Surjective (pointMultiplication a d)) := by
  cases N with
  | zero => omega
  | succ n => simpa only [Nat.add_one_sub_one] using exists_chart_transport z hz

end IdealGeneration
