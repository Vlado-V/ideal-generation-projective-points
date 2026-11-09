module

public import IdealGeneration.TripleNormalRootMotion
public import IdealGeneration.TripleNormalNewLayerProducts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Base evaluations of the actual new-source columns of the reduced map. -/

noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial Matrix NormalDegree SupportedQuadrics
open scoped Matrix

variable {K : Type*} [Field K] {h p q : ℕ}

private theorem eval_normalLinearProduct_base (F : Fin 3 → Forms K (h + 3 + 4) 2)
    (y : Fin (h + 3) → K) (a : Fin 3) :
    eval (Layer.point (Pi.single a 1) y 0) (normalLinearProduct K 3 (h + 3 + 4) 2 F).val =
      eval (Fin.append y 0) (F a).val := by
  rw [normalLinearProduct_val, map_sum]
  simp only [map_mul, eval_X, eval_coneExtend, Layer.point, Fin.addCases_left, Fin.addCases_right]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_mul]; rfl
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_mul]
  · simp

private theorem eval_traceLinearProduct_base (F : Fin (h + 3 + 4) → Forms K 3 2)
    (y : Fin (h + 3) → K) (a : Fin 3) :
    eval (Layer.point (Pi.single a 1) y 0) (traceLinearProduct K 3 (h + 3 + 4) 2 F).val =
      ∑ i, y i * eval (Pi.single a 1) (F (i.castAdd 4)).val := by
  have ha : Layer.point (Pi.single a (1 : K)) y 0 ∘ Fin.castAdd (h + 3 + 4) = Pi.single a 1 := by
    funext i
    simp [Layer.point]
  have he (Q : Poly K 3) : eval (Layer.point (Pi.single a 1) y 0) (pureExtend K 3 (h + 3 + 4) Q) =
      eval (Pi.single a 1) Q := by rw [pureExtend, eval_rename, ha]
  rw [traceLinearProduct_val, map_sum, Fin.sum_univ_add]
  simp_rw [map_mul, eval_X, he]
  simp only [Layer.point,
    Fin.addCases_right, Fin.addCases_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

variable (C : ConeConfiguration K 3 (h + 3 + 4) p q)
  (ω : K) (t : Fin h → K) (v : Fin 3 → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
  (points : PointPattern C ω (Fin.append t v) n ζ (Layer.baseSupport K (h + 3)))
  (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, Fin.append t v i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)

local notation "T" => (h + 3 + 4)
local notation "x" => Layer.baseSupport K (h + 3)
local notation "τ" => Fin.append t v
local notation "H" => mixedEquiv C ω τ n ζ x points hω ht hdet hζ
local notation "L" => pureLift C ω τ n ζ x points hω ht hdet hζ

/-- The pure quadratic coefficient at each new base direction. -/
def newMotionQuadric (v : Fin 3 → K) (u : Fin 3 → Fin 3 → K) (b : Fin 3) : Forms K 3 2 :=
  motionQuadratic (u b) (conicVector (v b))

/-- The compatible triple whose three rows are the specified new mixed directions. -/
def newMotionOmega (u : Fin 3 → Fin 3 → K) : Omega C :=
  ⟨fun a => (H (Fin.append 0 (fun b => u b a))).val, by
    change formMultiplication K 3 2 (fun a => quadraticRestriction C (H (Fin.append 0 (fun b => u b a))).val) = 0
    have hz (a : Fin 3) : quadraticRestriction C (H (Fin.append 0 (fun b => u b a))).val = 0 :=
      LinearMap.mem_ker.mp (H (Fin.append 0 (fun b => u b a))).property
    rw [show (fun a => quadraticRestriction C (H (Fin.append 0 (fun b => u b a))).val) = 0 from
      funext hz, map_zero]⟩

private theorem newMotionOmega_polynomial (hh : 6 ≤ h) (u : Fin 3 → Fin 3 → K) (a : Fin 3) :
    ((newMotionOmega C ω t v n ζ points hω ht hdet hζ u).val a).val.val =
      ∑ b : Fin 3, MvPolynomial.C (u b a) *
        (X ((NewLayerBlock.newBaseVariable h b).natAdd 3) *
          pureExtend K 3 T (Layer.normalForm (conicVector (v b))).val) := by
  have hs := pi_eq_sum_univ' (Fin.append (0 : Fin h → K) (fun b : Fin 3 => u b a))
  rw [Fin.sum_univ_add] at hs
  simp only [Fin.append_left, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add, Fin.append_right] at hs
  let F : (Fin (h + 3) → K) →ₗ[K] Poly K (3 + T) :=
    (MvPolynomial.homogeneousSubmodule (Fin (3 + T)) K 2).subtype.comp
      ((C.residualPiece 2).subtype.comp ((MixedKernel C).subtype.comp (H).toLinearMap))
  change F (Fin.append 0 (fun b => u b a)) = _
  rw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  change u b a • (H (Pi.single (b.natAdd h) 1)).val.val.val = _
  rw [smul_eq_C_mul, mixedEquiv_form, NewLayerBlock.newMixedForm_polynomial ω t v n ζ hh b]

/-- The normal product has precisely the new trace-coordinate quadrics of a motion. -/
theorem coefficientQuadrics_newMotionOmega (hh : 6 ≤ h) (u : Fin 3 → Fin 3 → K) :
    coefficientQuadrics C (newMotionOmega C ω t v n ζ points hω ht hdet hζ u) =
      Fin.append (Fin.append 0 (newMotionQuadric v u)) 0 := by
  let η := newMotionOmega C ω t v n ζ points hω ht hdet hζ u
  apply traceLinearProduct_injective K 3 T 2
  apply Subtype.ext
  rw [traceLinearProduct_val, ← coefficientQuadrics_reconstruct]
  change (normalProduct C η.val).val.val = _
  rw [normalProduct_val, traceLinearProduct_val]
  have hpoly (a : Fin 3) : (η.val a).val.val =
      ∑ b : Fin 3, MvPolynomial.C (u b a) *
        (X ((NewLayerBlock.newBaseVariable h b).natAdd 3) *
          pureExtend K 3 T (Layer.normalForm (conicVector (v b))).val) :=
    newMotionOmega_polynomial C ω t v n ζ points hω ht hdet hζ hh u a
  simp_rw [hpoly, Finset.mul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, Submodule.coe_zero, map_zero,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro b _
  change _ = X ((NewLayerBlock.newBaseVariable h b).natAdd 3) * (pureExtend K 3 T
    ((Layer.normalForm (u b)).val * (Layer.normalForm (conicVector (v b))).val))
  rw [map_mul]
  change _ = X ((NewLayerBlock.newBaseVariable h b).natAdd 3) *
    (pureExtend K 3 T (∑ a, MvPolynomial.C (u b a) * X a) *
      pureExtend K 3 T (Layer.normalForm (conicVector (v b))).val)
  rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_mul, pureExtend, rename_C, rename_X]
  ring

private theorem eval_liftedQuadric_base (Q : Forms K 3 2) (γ : Fin (h + 3) → K)
    (y : Fin (h + 3) → K) (a : Fin 3) :
    eval (Layer.point (Pi.single a 1) y 0) (liftForm ω τ n ζ x (Q, γ)).val =
      eval (Pi.single a 1) Q.val +
        ∑ i, y i * (baseLiftCoefficient ω (τ i) Q a + γ i * conicVector (τ i) a) := by
  rw [liftForm_apply, Layer.eval_quadratic]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mixedCoefficients_apply,
    single_dotProduct, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem eval_traceProduct_base (F : Fin T → C.residualPiece 2)
    (y : Fin (h + 3) → K) (a : Fin 3) :
    eval (Layer.point (Pi.single a 1) y 0) (traceProduct C F).val.val =
      ∑ i, y i * eval (Layer.point (Pi.single a 1) y 0) (F (i.castAdd 4)).val.val := by
  rw [traceProduct_val, map_sum, Fin.sum_univ_add]
  simp only [map_mul, eval_X, Layer.point, Fin.addCases_right, Fin.addCases_left, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

/-- Evaluation on the base hyperplane gives the motion correction and all mixed products. -/
theorem eval_reducedCoefficient_newMotion_base (hh : 6 ≤ h) (u : Fin 3 → Fin 3 → K)
    (ρ : Fin T → Fin (h + 3) → K) (y : Fin (h + 3) → K) (a : Fin 3) :
    eval (Fin.append y 0)
      ((reducedCoefficient C L (newMotionOmega C ω t v n ζ points hω ht hdet hζ u,
        fun j => H (ρ j))) a).val =
      -(∑ b : Fin 3, y (b.natAdd h) *
        ∑ i, y i * baseLiftCoefficient ω (τ i) (newMotionQuadric v u b) a) +
      ∑ j : Fin (h + 3), y j * ∑ i, y i * (ρ (j.castAdd 4) i * conicVector (τ i) a) := by
  let η := newMotionOmega C ω t v n ζ points hω ht hdet hζ u
  let f : Fin T → MixedKernel C := fun j => H (ρ j)
  let P := Layer.point (Pi.single a (1 : K)) y 0
  have hL (Q : Forms K 3 2) : quadraticRestriction C (L Q) = Q :=
    pureRestrict_pureLift C ω τ n ζ x points hω ht hdet hζ Q
  have hr := congrArg (fun F : Forms K (3 + T) 3 => eval P F.val)
    (reduced_reconstruct C L hL (η, f))
  change eval P (normalLinearProduct K 3 T 2 (reducedCoefficient C L (η, f))).val = _ at hr
  rw [show P = Layer.point (Pi.single a 1) y 0 from rfl, eval_normalLinearProduct_base] at hr
  change eval (Fin.append y 0) ((reducedCoefficient C L (η, f)) a).val = _
  rw [hr]
  have hcoef : coefficientQuadrics C η = Fin.append (Fin.append 0 (newMotionQuadric v u)) 0 :=
    coefficientQuadrics_newMotionOmega C ω t v n ζ points hω ht hdet hζ hh u
  have ho : eval P (omegaProduct C η).val.val =
      ∑ b : Fin 3, y (b.natAdd h) * eval (Pi.single a 1) (newMotionQuadric v u b).val := by
    rw [coefficientQuadrics_reconstruct, ← traceLinearProduct_val, hcoef]
    dsimp only [P]
    rw [eval_traceLinearProduct_base, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, Submodule.coe_zero, map_zero,
      mul_zero, Finset.sum_const_zero, zero_add]
  have hc : eval P (liftedCorrection C L η).val.val =
      ∑ b : Fin 3, y (b.natAdd h) * (eval (Pi.single a 1) (newMotionQuadric v u b).val +
        ∑ i, y i * baseLiftCoefficient ω (τ i) (newMotionQuadric v u b) a) := by
    change eval (Layer.point (Pi.single a 1) y 0)
      (traceProduct C (fun j => L (coefficientQuadrics C η j))).val.val = _
    rw [eval_traceProduct_base, hcoef, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, map_zero, Submodule.coe_zero,
      mul_zero, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro b _
    change y (b.natAdd h) * eval P (liftForm ω τ n ζ x (newMotionQuadric v u b, 0)).val = _
    rw [show P = Layer.point (Pi.single a 1) y 0 from rfl, eval_liftedQuadric_base]
    simp only [Pi.zero_apply, zero_mul, add_zero]
  have hm : eval P (mixedProduct C f).val.val =
      ∑ j : Fin (h + 3), y j * ∑ i, y i * (ρ (j.castAdd 4) i * conicVector (τ i) a) := by
    change eval (Layer.point (Pi.single a 1) y 0) (traceProduct C (fun j => (f j).val)).val.val = _
    rw [eval_traceProduct_base]
    simp only [f, mixedEquiv_form, eval_liftedQuadric_base, Submodule.coe_zero, map_zero,
      zero_add, Pi.zero_apply]
  change eval P ((omegaProduct C η).val.val - (liftedCorrection C L η).val.val +
    (mixedProduct C f).val.val) = _
  rw [map_add, map_sub, ho, hc, hm]
  simp only [mul_add, Finset.sum_add_distrib]
  abel

end IdealGeneration.TripleNormal
