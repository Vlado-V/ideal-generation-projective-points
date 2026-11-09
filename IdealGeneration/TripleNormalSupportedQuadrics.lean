module

public import IdealGeneration.TripleNormalBaseLift
public import IdealGeneration.TripleNormalQuadraticCoordinates
public import IdealGeneration.TripleNormalLayerCompatibility
public import IdealGeneration.TripleNormalElimination

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The residual quadrics of the supported three-normal configuration

The pure-normal quadratic is arbitrary. At each base coordinate the two
cone equations leave one conic direction, and the layer equations determine
the remaining coefficients. The resulting coordinate lift is an isomorphism
onto the actual degree-two normal-ideal equations.
-/

noncomputable section
namespace IdealGeneration.TripleNormal.SupportedQuadrics
open MvPolynomial Matrix NormalDegree
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {h p q : ℕ}

abbrev Coordinates (K : Type*) [Field K] (h : ℕ) := Forms K 3 2 × (Fin h → K)

/-- The actual two normal vectors attached to one base coordinate point. -/
def baseNormal (ω t : K) : Fin 2 → Fin 3 → K :=
  ![thetaPlus ω • sigmaPlus ω t, thetaMinus ω • sigmaMinus ω t]

/-- These are all the cone points, and every prescribed base or layer point
occurs among them. The trace-only points remain arbitrary. -/
structure PointPattern (C : ConeConfiguration K 3 (h + 4) p q)
    (ω : K) (t : Fin h → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
    (x : Layer.Supports K h) : Prop where
  exhaustive : ∀ k, (∃ i μ, C.point k = Layer.point (baseNormal ω (t i) μ) (Pi.single i 1) 0) ∨
    ∃ j ν, C.point k = Layer.point (n j ν) (x j ν) (Pi.single j (ζ j ν))
  base : ∀ i μ, ∃ k, C.point k = Layer.point (baseNormal ω (t i) μ) (Pi.single i 1) 0
  layer : ∀ j ν, ∃ k, C.point k = Layer.point (n j ν) (x j ν) (Pi.single j (ζ j ν))

/-- The base mixed coefficients are the particular lift plus the free
conic direction at each base coordinate. -/
def mixedCoefficients (ω : K) (t : Fin h → K) :
    Coordinates K h →ₗ[K] (Fin h → Fin 3 → K) :=
  (baseLiftCoefficients ω t).comp (LinearMap.fst K _ _) +
    (LinearMap.pi (fun i => (LinearMap.proj i).smulRight (conicVector (t i)))).comp
      (LinearMap.snd K _ _)

@[simp] theorem mixedCoefficients_apply (ω : K) (t : Fin h → K)
    (v : Coordinates K h) (i : Fin h) :
    mixedCoefficients ω t v i = baseLiftCoefficient ω (t i) v.1 + v.2 i • conicVector (t i) := rfl

private theorem baseLift_eval (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (Q : Forms K 3 2) (μ : Fin 2) :
    eval (baseNormal ω t μ) Q.val + baseNormal ω t μ ⬝ᵥ baseLiftCoefficient ω t Q = 0 := by
  fin_cases μ
  · exact baseLiftCoefficient_eval_plus ω t hω ht Q
  · exact baseLiftCoefficient_eval_minus ω t hω ht Q

private theorem baseNormal_annihilates (ω t : K) (hω : IsPrimitiveRoot ω 3) (μ : Fin 2) :
    baseNormal ω t μ ⬝ᵥ conicVector t = 0 := by
  fin_cases μ
  · change (thetaPlus ω • sigmaPlus ω t) ⬝ᵥ conicVector t = 0
    rw [smul_dotProduct, conic_plus_annihilates ω t hω, smul_zero]
  · change (thetaMinus ω • sigmaMinus ω t) ⬝ᵥ conicVector t = 0
    rw [smul_dotProduct, conic_minus_annihilates ω t hω, smul_zero]

theorem mixedCoefficients_base_equation (ω : K) (t : Fin h → K)
    (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, t i ≠ 0) (v : Coordinates K h) (i : Fin h) (μ : Fin 2) :
    eval (baseNormal ω (t i) μ) v.1.val +
      baseNormal ω (t i) μ ⬝ᵥ mixedCoefficients ω t v i = 0 := by
  rw [mixedCoefficients_apply, dotProduct_add, dotProduct_smul,
    baseNormal_annihilates ω (t i) hω μ, smul_zero, add_zero]
  exact baseLift_eval ω (t i) hω (ht i) v.1 μ

/-- The concrete homogeneous lift before imposing the residual subtype. -/
def liftForm (ω : K) (t : Fin h → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
    (x : Layer.Supports K h) : Coordinates K h →ₗ[K] Forms K (3 + (h + 4)) 2 :=
  (Layer.quadratic n ζ x).comp ((LinearMap.fst K _ _).prod (mixedCoefficients ω t))

@[simp] theorem liftForm_apply (ω : K) (t : Fin h → K) (n : Layer.Normals K)
    (ζ : Layer.Heights K) (x : Layer.Supports K h) (v : Coordinates K h) :
    liftForm ω t n ζ x v = Layer.quadratic n ζ x (v.1, mixedCoefficients ω t v) := rfl

@[simp] theorem pureRestrict_liftForm (ω : K) (t : Fin h → K) (n : Layer.Normals K)
    (ζ : Layer.Heights K) (x : Layer.Supports K h) (v : Coordinates K h) :
    pureRestrictForm K 3 (h + 4) 2 (liftForm ω t n ζ x v) = v.1 := by
  rw [liftForm_apply, Layer.pureRestrict_quadratic]

theorem liftForm_injective (ω : K) (t : Fin h → K) (n : Layer.Normals K)
    (ζ : Layer.Heights K) (x : Layer.Supports K h) : Function.Injective (liftForm ω t n ζ x) := by
  intro v w hvw
  have hQ : v.1 = w.1 := by
    simpa only [pureRestrict_liftForm] using congrArg (pureRestrictForm K 3 (h + 4) 2) hvw
  simp only [liftForm_apply, quadratic_eq_coefficientQuadratic, coefficientQuadratic, hQ] at hvw
  have htab := traceLinearProduct_injective K 3 (h + 4) 1 (add_left_cancel hvw)
  have hA : mixedCoefficients ω t v = mixedCoefficients ω t w := by
    funext i
    apply normalForm_injective
    simpa only [Fin.addCases_left] using congrFun htab (i.castAdd 4)
  apply Prod.ext hQ
  funext i
  have hi := congrArg (fun b : Fin 3 → K => b 0) (congrFun hA i)
  simpa [hQ, conicVector] using hi

variable (C : ConeConfiguration K 3 (h + 4) p q)
  (ω : K) (t : Fin h → K) (n : Layer.Normals K) (ζ : Layer.Heights K) (x : Layer.Supports K h)
  (points : PointPattern C ω t n ζ x) (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, t i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)

/-- The lift lands in the actual vanishing equations in the normal ideal. -/
def lift : Coordinates K h →ₗ[K] C.residualPiece 2 :=
  (liftForm ω t n ζ x).codRestrict _ (by
    intro v
    rw [liftForm_apply]
    exact Layer.quadratic_mem_residual C n ζ x (fun i => baseNormal ω (t i)) v.1
      (mixedCoefficients ω t v) points.exhaustive
      (mixedCoefficients_base_equation ω t hω ht v) hdet hζ)

@[simp] theorem lift_val (v : Coordinates K h) :
    (lift C ω t n ζ x points hω ht hdet hζ v).val = liftForm ω t n ζ x v := rfl

@[simp] theorem quadraticRestriction_lift (v : Coordinates K h) :
    quadraticRestriction C (lift C ω t n ζ x points hω ht hdet hζ v) = v.1 :=
  pureRestrict_liftForm ω t n ζ x v

theorem lift_injective : Function.Injective (lift C ω t n ζ x points hω ht hdet hζ) := by
  intro v w hvw
  exact liftForm_injective ω t n ζ x (congrArg Subtype.val hvw)

private theorem base_difference_mem_kernel (ω t : K) (hω : IsPrimitiveRoot ω 3) (ht : t ≠ 0)
    (Q : Forms K 3 2) (A : Fin 3 → K)
    (hbase : ∀ μ, eval (baseNormal ω t μ) Q.val + baseNormal ω t μ ⬝ᵥ A = 0) :
    (baseNormalMatrix ω t).mulVec (A - baseLiftCoefficient ω t Q) = 0 := by
  have he (μ : Fin 2) : baseNormal ω t μ ⬝ᵥ (A - baseLiftCoefficient ω t Q) = 0 := by
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr (add_left_cancel ((hbase μ).trans (baseLift_eval ω t hω ht Q μ).symm))
  have hω₀ : ω ≠ 0 := hω.ne_zero (by decide)
  funext μ
  fin_cases μ
  · change sigmaPlus ω t ⬝ᵥ (A - baseLiftCoefficient ω t Q) = 0
    have hp := he 0
    change (thetaPlus ω • sigmaPlus ω t) ⬝ᵥ (A - baseLiftCoefficient ω t Q) = 0 at hp
    rw [smul_dotProduct, smul_eq_mul] at hp
    exact (mul_eq_zero.mp hp).resolve_left (neg_ne_zero.mpr (pow_ne_zero _ hω₀))
  · change sigmaMinus ω t ⬝ᵥ (A - baseLiftCoefficient ω t Q) = 0
    have hm := he 1
    change (thetaMinus ω • sigmaMinus ω t) ⬝ᵥ (A - baseLiftCoefficient ω t Q) = 0 at hm
    rw [smul_dotProduct, smul_eq_mul] at hm
    exact (mul_eq_zero.mp hm).resolve_left hω₀

private theorem layerCoefficients_eq_correction
    (n : Layer.Normals K) (ζ : Layer.Heights K) (x : Layer.Supports K h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) (Z : Fin 4 → Fin 3 → K)
    (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)
    (he : ∀ j ν, eval (Layer.point (n j ν) (x j ν) (Pi.single j (ζ j ν)))
      (coefficientQuadratic Q A Z).val = 0) :
    Z = Layer.correction n ζ x (Q, A) := by
  funext j
  apply Matrix.mulVec_injective_of_det_ne_zero (hdet j)
  rw [Layer.normalMatrix_correction n ζ x j (hdet j) (Q, A)]
  funext ν
  change n j ν ⬝ᵥ Z j = -(eval (n j ν) Q.val + ∑ i, x j ν i * (n j ν ⬝ᵥ A i)) / ζ j ν
  apply mul_right_cancel₀ (hζ j ν)
  rw [div_mul_cancel₀ _ (hζ j ν)]
  have hv := he j ν
  rw [eval_coefficientQuadratic_layer] at hv
  linear_combination hv

/-- The actual residual equations have precisely the prescribed pure-normal
part, free base coefficients, and uniquely corrected layer coefficients. -/
theorem lift_surjective : Function.Surjective (lift C ω t n ζ x points hω ht hdet hζ) := by
  intro f
  let Q := pureRestrictForm K 3 (h + 4) 2 f.val
  obtain ⟨A, Z, hpoly⟩ := exists_coefficientQuadratic f.val f.property.2
  change coefficientQuadratic Q A Z = f.val at hpoly
  have hb (i : Fin h) (μ : Fin 2) :
      eval (baseNormal ω (t i) μ) Q.val + baseNormal ω (t i) μ ⬝ᵥ A i = 0 := by
    obtain ⟨k, hk⟩ := points.base i μ
    have he := (C.mem_conePiece f.val).mp f.property.1 k
    rw [hk, ← hpoly, eval_coefficientQuadratic_base] at he
    exact he
  have hfree (i : Fin h) : ∃ γ : K,
      A i = baseLiftCoefficient ω (t i) Q + γ • conicVector (t i) := by
    obtain ⟨γ, hg⟩ := (baseNormalMatrix_ker_iff ω (t i) hω (ht i) _).mp
      (base_difference_mem_kernel ω (t i) hω (ht i) Q (A i) (hb i))
    exact ⟨γ, sub_eq_iff_eq_add'.mp hg⟩
  choose γ hγ using hfree
  have hA : mixedCoefficients ω t (Q, γ) = A := by
    funext i
    exact (hγ i).symm
  have hZ : Z = Layer.correction n ζ x (Q, A) := by
    apply layerCoefficients_eq_correction n ζ x Q A Z hdet hζ
    intro j ν
    obtain ⟨k, hk⟩ := points.layer j ν
    rw [hpoly, ← hk]
    exact (C.mem_conePiece f.val).mp f.property.1 k
  refine ⟨(Q, γ), Subtype.ext ?_⟩
  rw [lift_val, liftForm_apply, hA, quadratic_eq_coefficientQuadratic, ← hZ]
  exact hpoly

/-- The exact residual splitting, with its forward map given by the lift. -/
def liftEquiv : Coordinates K h ≃ₗ[K] C.residualPiece 2 :=
  LinearEquiv.ofBijective (lift C ω t n ζ x points hω ht hdet hζ)
    ⟨lift_injective C ω t n ζ x points hω ht hdet hζ,
      lift_surjective C ω t n ζ x points hω ht hdet hζ⟩

abbrev residualEquiv : C.residualPiece 2 ≃ₗ[K] Coordinates K h :=
  (liftEquiv C ω t n ζ x points hω ht hdet hζ).symm

@[simp] theorem liftEquiv_val (v : Coordinates K h) :
    (liftEquiv C ω t n ζ x points hω ht hdet hζ v).val = liftForm ω t n ζ x v := rfl

@[simp] theorem residualEquiv_fst (f : C.residualPiece 2) :
    (residualEquiv C ω t n ζ x points hω ht hdet hζ f).1 = quadraticRestriction C f := by
  have he := congrArg (quadraticRestriction C)
    ((liftEquiv C ω t n ζ x points hω ht hdet hζ).apply_symm_apply f)
  change quadraticRestriction C (lift C ω t n ζ x points hω ht hdet hζ
    ((liftEquiv C ω t n ζ x points hω ht hdet hζ).symm f)) = quadraticRestriction C f at he
  simpa only [quadraticRestriction_lift] using he

/-- A linear section of pure-normal restriction, obtained by taking the
free conic coefficients to be zero. -/
def pureLift : Forms K 3 2 →ₗ[K] C.residualPiece 2 :=
  (lift C ω t n ζ x points hω ht hdet hζ).comp (LinearMap.inl K _ _)

@[simp] theorem pureRestrict_pureLift (Q : Forms K 3 2) :
    pureRestrictForm K 3 (h + 4) 2 (pureLift C ω t n ζ x points hω ht hdet hζ Q).val = Q := by
  change pureRestrictForm K 3 (h + 4) 2 (liftForm ω t n ζ x (Q, 0)) = Q
  exact pureRestrict_liftForm ω t n ζ x (Q, 0)

/-- The free coefficients give exactly the kernel of pure-normal restriction. -/
def mixedLift : (Fin h → K) →ₗ[K] (quadraticRestriction C).ker :=
  ((lift C ω t n ζ x points hω ht hdet hζ).comp (LinearMap.inr K _ _)).codRestrict _ (by
    intro γ
    change quadraticRestriction C (lift C ω t n ζ x points hω ht hdet hζ (0, γ)) = 0
    exact quadraticRestriction_lift C ω t n ζ x points hω ht hdet hζ (0, γ))

def mixedEquiv : (Fin h → K) ≃ₗ[K] (quadraticRestriction C).ker :=
  LinearEquiv.ofBijective (mixedLift C ω t n ζ x points hω ht hdet hζ) (by
    constructor
    · intro γ δ he
      have hv : lift C ω t n ζ x points hω ht hdet hζ (0, γ) =
          lift C ω t n ζ x points hω ht hdet hζ (0, δ) := congrArg Subtype.val he
      exact congrArg Prod.snd (lift_injective C ω t n ζ x points hω ht hdet hζ hv)
    · intro f
      obtain ⟨v, hv⟩ := lift_surjective C ω t n ζ x points hω ht hdet hζ f.val
      have hQ : v.1 = 0 := by
        have he := (congrArg (quadraticRestriction C) hv).trans f.property
        simpa only [quadraticRestriction_lift] using he
      refine ⟨v.2, Subtype.ext ?_⟩
      change lift C ω t n ζ x points hω ht hdet hζ (0, v.2) = f.val
      rw [← hQ]
      exact hv)

@[simp] theorem mixedEquiv_form (γ : Fin h → K) :
    (mixedEquiv C ω t n ζ x points hω ht hdet hζ γ).val.val =
      liftForm ω t n ζ x (0, γ) := rfl

/-- Adding three base coordinates preserves the old part of each lifted
polynomial, for both the pure section and the free mixed directions. -/
theorem restrict_liftForm_append (ω : K) (t : Fin h → K) (u : Fin 3 → K)
    (n : Layer.Normals K) (ζ : Layer.Heights K) (hh : 6 ≤ h) (Q : Forms K 3 2)
    (γ : Fin h → K) (δ : Fin 3 → K) :
    extensionAmbientRestrictionForm h 2
      (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
        (Q, Fin.append γ δ)) =
      liftForm ω t n ζ (Layer.baseSupport K h) (Q, γ) := by
  simp only [liftForm_apply]
  apply Layer.restrict_quadratic n ζ hh
  intro i
  simp only [mixedCoefficients_apply, Fin.append_left]

end IdealGeneration.TripleNormal.SupportedQuadrics
