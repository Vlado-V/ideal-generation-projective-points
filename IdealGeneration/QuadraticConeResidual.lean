module

public import IdealGeneration.QuadraticVariableTransport
public import IdealGeneration.QuadraticConeLinearEvaluation
public import IdealGeneration.QuadraticFlagLiftWitness
public import IdealGeneration.ConeMiddleFamily
public import IdealGeneration.TwoGroupLinearCore
public import IdealGeneration.Numerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The represented quadrics and actual normal-ideal scalar postulation. -/

noncomputable section
namespace IdealGeneration.QuadraticConeResidual
open MvPolynomial Module QuadraticFlag QuadraticElimination QuadraticVariableTransport ConeMiddleFamily

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable {m p q : ℕ} (D : QuadraticLiftParameters K P J)
variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (r : ConeIndex P J ≃ Fin p)
variable (C : ConeConfiguration K 2 m p q)

/-- The ambient cone configuration uses the displayed marked supports and heights. -/
def Compatible : Prop :=
  ∀ z, C.point (r z) = pointOf e (D.coneNormalPoint z) (D.coneTracePoint z)

omit [Fintype P] [Fintype J] in
theorem eval_flatten_at_cone (h : Compatible D e r C) (z : ConeIndex P J)
    (f : MvPolynomial Bool (MvPolynomial ((P × Bool) ⊕ J) K)) :
    eval (C.point (r z)) (flatten e f) = D.conePointEval z f := by
  rw [h z, eval_flatten]; rfl

/-- Scalar evaluation on the actual normal-ideal part of the forms. -/
def normalEval (d : ℕ) : normalForms K 2 m d →ₗ[K] (Fin p → K) :=
  LinearMap.pi (fun i => (evaluationLinear K (2 + m) d (C.point i)).comp
    (normalForms K 2 m d).subtype)

@[simp] theorem normalEval_apply (d : ℕ) (f : normalForms K 2 m d) (i : Fin p) :
    normalEval C d f i = eval (C.point i) f.val.val := rfl

/-- A pair of trace-linear coefficient vectors gives an actual normal quadric. -/
def mixedNormalForm (uv : (((P × Bool) ⊕ J) → K) × (((P × Bool) ⊕ J) → K)) :
    normalForms K 2 m 2 :=
  ⟨⟨flatten e (normalPairMap (linearPolynomial uv.1, linearPolynomial uv.2)),
    flattenedPair_homogeneous e _ (linearPolynomial_isHomogeneous uv.1)
      (linearPolynomial_isHomogeneous uv.2)⟩,
    Subtype.ext (flattenedPair_restrict e _)⟩

/-- The independent base and layer equations give full normal scalar evaluation. -/
theorem normalEval_quadratic_surjective (h : Compatible D e r C) :
    Function.Surjective (normalEval C 2) := by
  intro v
  obtain ⟨uv, huv⟩ := D.mixedConeEvaluation_surjective (fun z => v (r z))
  refine ⟨mixedNormalForm e uv, ?_⟩
  funext i
  obtain ⟨z, rfl⟩ := r.surjective i
  change eval (C.point (r z)) (flatten e (normalPairMap (linearPolynomial uv.1,
    linearPolynomial uv.2))) = v (r z)
  rw [eval_flatten_at_cone D e r C h]
  exact congrFun huv z

/-- Multiplying by a normal coordinate nonzero at every cone point also gives
full cubic evaluation on the normal ideal. -/
theorem normalEval_cubic_surjective
    (h₂ : Function.Surjective (normalEval C 2))
    (hs : ∀ i, C.point i (normalIndex (m := m) false) ≠ 0) :
    Function.Surjective (normalEval C 3) := by
  intro v
  let s := normalIndex (m := m) false
  obtain ⟨F, hF⟩ := h₂ (fun i => v i / C.point i s)
  let G : Forms K (2 + m) 3 :=
    ⟨X s * F.val.val, (isHomogeneous_X K s).mul F.val.property⟩
  have hG : G ∈ normalForms K 2 m 3 := by
    apply Subtype.ext
    change coneRestrict K 2 m (X s * F.val.val) = 0
    rw [map_mul]
    have hz : coneRestrict K 2 m (X s) = 0 := coneRestrict_X_normal K 2 m _
    rw [hz, zero_mul]
  refine ⟨⟨G, hG⟩, ?_⟩
  funext i
  change eval (C.point i) (X s * F.val.val) = v i
  have he : eval (C.point i) F.val.val = v i / C.point i s := congrFun hF i
  rw [map_mul, eval_X, he, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (hs i)

/-- The kernel of normal scalar evaluation is the actual residual ideal piece. -/
def residualKernelEquiv (d : ℕ) : C.residualPiece d ≃ₗ[K] (normalEval C d).ker where
  toFun f := ⟨⟨f.val, f.property.2⟩, by
    funext i
    exact (C.mem_conePiece f.val).mp f.property.1 i⟩
  invFun f := ⟨f.val.val, ⟨(C.mem_conePiece _).mpr (fun i => congrFun f.property i), f.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the trace subtracts the pure-trace monomials. -/
theorem finrank_normalForms (d : ℕ) :
    finrank K (normalForms K 2 m d) = N (2 + m) d - N m d := by
  have ho : Function.Surjective (coneRestrictForm K 2 m d) := fun f =>
    ⟨coneExtendForm K 2 m d f, coneRestrictForm_extendForm K 2 m f⟩
  have h := TwoGroup.rank_nullity_monoid (coneRestrictForm K 2 m d)
  rw [LinearMap.range_eq_top.mpr ho, finrank_top, finrank_forms, finrank_forms] at h
  change N m d + finrank K (normalForms K 2 m d) = N (2 + m) d at h
  omega

/-- Full normal scalar evaluation subtracts the number of marked cone points. -/
theorem finrank_residualPiece_of_surjective (d : ℕ)
    (h : Function.Surjective (normalEval C d)) :
    finrank K (C.residualPiece d) = N (2 + m) d - N m d - p := by
  rw [(residualKernelEquiv C d).finrank_eq]
  have he := TwoGroup.rank_nullity_monoid (normalEval C d)
  rw [LinearMap.range_eq_top.mpr h, finrank_top, Module.finrank_pi,
    Fintype.card_fin, finrank_normalForms] at he
  omega

/-- The lift space has three normal coefficients and one coefficient per base variable. -/
abbrev ResidualCoordinates := LiftSpace (K := K) (H := P × Bool → K)

/-- The explicit polynomial realization of the chosen residual quadrics. -/
def representedQuadric := normalPolynomialMap D.firstLift D.secondLift
  (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)

theorem representedQuadric_eval (x : ResidualCoordinates (K := K) (P := P)) (z : ConeIndex P J) :
    D.conePointEval z (representedQuadric D x) = 0 := by
  have he : D.conePointEval z (representedQuadric D x) =
      liftedQuadratic (aeval (D.coneTracePoint z)) (D.coneNormalPoint z false)
        (D.coneNormalPoint z true) D.firstLift D.secondLift
        (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection) x := by
    simp [representedQuadric, liftedQuadratic, quadraticExpression]
  rw [he]
  rcases z with i | ⟨j,b⟩
  · exact D.actualNormalLiftVanishing.base i x
  · cases b
    · exact D.actualNormalLiftVanishing.layer₀ j x
    · exact D.actualNormalLiftVanishing.layer₁ j x

/-- The represented quadrics lie in the genuine residual ideal of the cones. -/
def representedToResidual (h : Compatible D e r C) :
    ResidualCoordinates (K := K) (P := P) →ₗ[K] C.residualPiece 2 where
  toFun x := ⟨⟨flatten e (representedQuadric D x),
    flattenedQuadric_homogeneous e D.firstLift D.secondLift
      (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
      D.firstLift_homogeneous D.secondLift_homogeneous
      (firstKernelMap_homogeneous _) (secondKernelMap_homogeneous _ _) x⟩,
    ⟨(C.mem_conePiece _).mpr (fun i => by
      obtain ⟨z, rfl⟩ := r.surjective i
      rw [eval_flatten_at_cone D e r C h]
      exact representedQuadric_eval D x z),
      Subtype.ext (flattenedQuadric_restrict e _ _ _ _ x)⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten e).toAlgHom.toLinearMap.comp (representedQuadric D)).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((flatten e).toAlgHom.toLinearMap.comp (representedQuadric D)).map_smul a x

@[simp] theorem representedToResidual_val (h : Compatible D e r C)
    (x : ResidualCoordinates (K := K) (P := P)) :
    (representedToResidual D e r C h x).val.val = flatten e (representedQuadric D x) := rfl

/-- The residual representation is faithful whenever its nested polynomial is. -/
theorem representedToResidual_injective (h : Compatible D e r C)
    (hi : Function.Injective (representedQuadric D)) :
    Function.Injective (representedToResidual D e r C h) := by
  intro x y he
  apply hi
  apply (flatten e).injective
  exact congrArg (fun f => f.val.val) he

/-- The number of normal quadratic monomials is `2m+3`. -/
theorem quadratic_normal_count (m : ℕ) : N (2 + m) 2 - N m 2 = 2 * m + 3 := by
  have h₁ := QuadraticFlag.two_mul_quadratic_count (2 + m)
  have h₂ := QuadraticFlag.two_mul_quadratic_count m
  have he : N (2 + m) 2 = N m 2 + 2 * m + 3 := by nlinarith
  omega

/-- The number of normal cubic monomials is `(m+2)^2`. -/
theorem cubic_normal_count (m : ℕ) : N (2 + m) 3 - N m 3 = (m + 2) ^ 2 := by
  have h₁ : N (2 + m) 3 = (m + 4).choose 3 := by unfold N; congr 1; omega
  have h₂ : N m 3 = (m + 2).choose 3 := by unfold N; congr 1
  have h₃ : (m + 4).choose 3 = (m + 3).choose 2 + (m + 3).choose 3 := by
    exact Nat.choose_succ_succ (m + 3) 2
  have h₄ : (m + 3).choose 3 = (m + 2).choose 2 + (m + 2).choose 3 := by
    exact Nat.choose_succ_succ (m + 2) 2
  have ha : (m + 3).choose 2 = N (m + 2) 2 := by unfold N; congr 1
  have hb : (m + 2).choose 2 = N (m + 1) 2 := by unfold N; congr 1
  rw [h₁, h₂, h₃, h₄, ha, hb]
  have hs := QuadraticFlag.two_mul_quadratic_count (m + 2)
  have ht := QuadraticFlag.two_mul_quadratic_count (m + 1)
  have he : N (m + 2) 2 + N (m + 1) 2 = (m + 2) ^ 2 := by nlinarith
  omega

theorem trace_cardinality (e : ((P × Bool) ⊕ J) ≃ Fin m) : m = Fintype.card (P × Bool) + Fintype.card J := by
  simpa [Fintype.card_sum] using (Fintype.card_congr e).symm

theorem cone_cardinality (r : ConeIndex P J ≃ Fin p) : p = Fintype.card (P × Bool) + 2 * Fintype.card J := by
  simpa [ConeIndex, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm] using
    (Fintype.card_congr r).symm

/-- The actual residual quadrics have dimension `h+3`. -/
theorem finrank_residualQuadrics (h : Compatible D e r C) :
    finrank K (C.residualPiece 2) = Fintype.card (P × Bool) + 3 := by
  rw [finrank_residualPiece_of_surjective C 2 (normalEval_quadratic_surjective D e r C h),
    quadratic_normal_count, trace_cardinality e, cone_cardinality r]
  omega

/-- The actual residual cubic dimension is the normal monomial count minus the cone count. -/
theorem finrank_residualCubics (h : Compatible D e r C)
    (hs : ∀ i, C.point i (normalIndex (m := m) false) ≠ 0) :
    finrank K (C.residualPiece 3) = (m + 2) ^ 2 - p := by
  rw [finrank_residualPiece_of_surjective C 3
    (normalEval_cubic_surjective C (normalEval_quadratic_surjective D e r C h) hs), cubic_normal_count]

/-- Faithfulness and the dimension count identify the full residual quadratic space. -/
theorem representedToResidual_surjective (h : Compatible D e r C)
    (hi : Function.Injective (representedQuadric D)) :
    Function.Surjective (representedToResidual D e r C h) := by
  let : AddCommGroup (C.residualPiece 2) := Module.addCommMonoidToAddCommGroup K
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj (representedToResidual_injective D e r C h hi),
    finrank_residualQuadrics D e r C h]
  simp [ResidualCoordinates, LiftSpace, Module.finrank_prod, Nat.add_comm]

end IdealGeneration.QuadraticConeResidual
