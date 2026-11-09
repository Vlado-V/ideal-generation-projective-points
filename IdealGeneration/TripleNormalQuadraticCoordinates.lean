module

public import IdealGeneration.TripleNormalLayerLift
public import IdealGeneration.NormalCoefficientRecovery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Pure and mixed coordinates of a quadric in the three-normal ideal. -/

noncomputable section
namespace IdealGeneration.TripleNormal.SupportedQuadrics

open MvPolynomial NormalDegree Matrix
open scoped Matrix

variable {K : Type*} [Field K] {h : ℕ}

/-- Evaluation at the three normal coordinate points recovers the linear coefficients. -/
def normalCoordinates (f : Forms K 3 1) : Fin 3 → K :=
  fun u => eval (Pi.single u 1) f.val

@[simp] theorem normalCoordinates_normalForm (a : Fin 3 → K) :
    normalCoordinates (Layer.normalForm a) = a := by
  funext u
  change eval (Pi.single u 1) (Layer.normalForm a).val = a u
  rw [Layer.eval_normalForm]
  unfold dotProduct
  rw [Finset.sum_eq_single u]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

/-- Every homogeneous normal linear form is reconstructed from these values. -/
@[simp] theorem normalForm_normalCoordinates (f : Forms K 3 1) :
    Layer.normalForm (normalCoordinates f) = f := by
  let F : (Fin 3 → K) →ₗ[K] Poly K 3 :=
    (homogeneousSubmodule (Fin 3) K 1).subtype.comp Layer.normalForm
  have hspan : Submodule.span K (Set.range (X : Fin 3 → Poly K 3)) ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    refine ⟨Pi.single u 1, ?_⟩
    change (∑ i, C ((Pi.single u 1 : Fin 3 → K) i) * X i) = X u
    rw [Finset.sum_eq_single u]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  have hf : f.val ∈ Submodule.span K (Set.range (X : Fin 3 → Poly K 3)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact f.property
  obtain ⟨a, ha⟩ := hspan hf
  have ha' : Layer.normalForm a = f := Subtype.ext ha
  rw [← ha', normalCoordinates_normalForm]

theorem normalForm_injective : Function.Injective (Layer.normalForm (K := K)) := by
  intro a b hab
  simpa only [normalCoordinates_normalForm] using congrArg normalCoordinates hab

/-- Form the quadric with a prescribed pure normal part and mixed coefficients. -/
def coefficientQuadratic (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (Z : Fin 4 → Fin 3 → K) : Forms K (3 + (h + 4)) 2 :=
  pureExtendForm K 3 (h + 4) 2 Q +
    traceLinearProduct K 3 (h + 4) 1
      (fun i : Fin (h + 4) => Layer.normalForm (Fin.addCases A Z i))

theorem quadratic_eq_coefficientQuadratic (n : Layer.Normals K) (ζ : Layer.Heights K)
    (x : Layer.Supports K h) (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) :
    Layer.quadratic n ζ x (Q, A) = coefficientQuadratic Q A (Layer.correction n ζ x (Q, A)) := by
  simp only [Layer.quadratic, coefficientQuadratic, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply]
  apply congrArg (fun f => pureExtendForm K 3 (h + 4) 2 Q + traceLinearProduct K 3 (h + 4) 1 f)
  funext i
  induction i using Fin.addCases <;> simp

/-- The pure term and the two groups of mixed terms evaluate separately. -/
theorem eval_coefficientQuadratic (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (Z : Fin 4 → Fin 3 → K) (a : Fin 3 → K) (y : Fin h → K) (z : Fin 4 → K) :
    eval (Layer.point a y z) (coefficientQuadratic Q A Z).val =
      eval a Q.val + (∑ i, y i * (a ⬝ᵥ A i)) + ∑ j, z j * (a ⬝ᵥ Z j) := by
  simp only [coefficientQuadratic, Submodule.coe_add, map_add, traceLinearProduct_val,
    map_sum, map_mul, eval_X]
  have ha : Layer.point a y z ∘ Fin.castAdd (h + 4) = a := by
    funext i
    simp [Layer.point]
  simp only [pureExtendForm, pureExtend, LinearMap.coe_mk, AddHom.coe_mk, eval_rename,
    Layer.point, Fin.addCases_right]
  rw [ha, Fin.sum_univ_add]
  simp [add_assoc]

theorem eval_coefficientQuadratic_base (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (Z : Fin 4 → Fin 3 → K) (a : Fin 3 → K) (i : Fin h) :
    eval (Layer.point a (Pi.single i 1) 0) (coefficientQuadratic Q A Z).val =
      eval a Q.val + a ⬝ᵥ A i := by
  rw [eval_coefficientQuadratic]
  have hs : ∑ b, (Pi.single i 1 : Fin h → K) b * (a ⬝ᵥ A b) = a ⬝ᵥ A i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  simp [hs]

theorem eval_coefficientQuadratic_layer (Q : Forms K 3 2) (A : Fin h → Fin 3 → K)
    (Z : Fin 4 → Fin 3 → K) (a : Fin 3 → K) (y : Fin h → K) (j : Fin 4) (zeta : K) :
    eval (Layer.point a y (Pi.single j zeta)) (coefficientQuadratic Q A Z).val =
      eval a Q.val + (∑ i, y i * (a ⬝ᵥ A i)) + zeta * (a ⬝ᵥ Z j) := by
  rw [eval_coefficientQuadratic, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

/-- Every normal-ideal quadric has the indicated pure and mixed coordinates. -/
theorem exists_coefficientQuadratic (f : Forms K (3 + (h + 4)) 2)
    (hf : coneRestrictForm K 3 (h + 4) 2 f = 0) :
    ∃ (A : Fin h → Fin 3 → K) (Z : Fin 4 → Fin 3 → K),
      coefficientQuadratic (pureRestrictForm K 3 (h + 4) 2 f) A Z = f := by
  let g := componentForm K 3 (h + 4) 1 f
  let B : Fin (h + 4) → Fin 3 → K :=
    fun i => normalCoordinates (traceCoefficientMap K 3 (h + 4) 1 g i)
  let A : Fin h → Fin 3 → K := fun i => B (i.castAdd 4)
  let Z : Fin 4 → Fin 3 → K := fun j => B (j.natAdd h)
  have hcoeff (i : Fin (h + 4)) :
      Layer.normalForm (Fin.addCases A Z i) = traceCoefficient K 3 (h + 4) 1 g i := by
    rw [show Fin.addCases A Z i = B i from Fin.addCases_castAdd_natAdd B i]
    exact normalForm_normalCoordinates (traceCoefficientMap K 3 (h + 4) 1 g i)
  have hweight : g.val.IsWeightedHomogeneous (traceWeight 3 (h + 4)) 1 :=
    trace_homogeneous K 3 (h + 4) g.property (component_weighted K 3 (h + 4) 1 f.val)
      (by decide : 1 ≤ 2)
  have htrace : traceLinearProduct K 3 (h + 4) 1
      (fun i : Fin (h + 4) => Layer.normalForm (Fin.addCases A Z i)) = g := by
    apply Subtype.ext
    rw [traceLinearProduct_val]
    simp only [hcoeff]
    exact (trace_linear_reconstruct K 3 (h + 4) g hweight).symm
  refine ⟨A, Z, ?_⟩
  rw [coefficientQuadratic, htrace]
  apply Subtype.ext
  change pureExtend K 3 (h + 4) (pureRestrict K 3 (h + 4) f.val) + g.val = f.val
  exact (add_comm _ _).trans (quadratic_split K 3 (h + 4) f hf).symm

end IdealGeneration.TripleNormal.SupportedQuadrics
