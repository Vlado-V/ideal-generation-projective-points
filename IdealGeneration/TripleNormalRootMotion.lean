module

public import IdealGeneration.TripleNormalBaseLift
public import IdealGeneration.TripleNormalLayerLift

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The root-motion quadrics and their chord projections in the three-normal step. -/

noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K]

/-- The product of the two normal linear forms specified by their coefficients. -/
def motionQuadratic (u v : Fin 3 → K) : Forms K 3 2 :=
  ⟨(Layer.normalForm u).val * (Layer.normalForm v).val,
    (Layer.normalForm u).property.mul (Layer.normalForm v).property⟩

@[simp] theorem eval_motionQuadratic (a u v : Fin 3 → K) :
    eval a (motionQuadratic u v).val = (a ⬝ᵥ u) * (a ⬝ᵥ v) := by
  simp only [motionQuadratic, map_mul, Layer.eval_normalForm]

/-- The projection of the mixed coefficient at root `r` onto the chord from `b` to `r`. -/
def rootMotionProjection (ω b r : K) (u : Fin 3 → K) : K :=
  (conicVector b ⨯₃ conicVector r) ⬝ᵥ baseLiftCoefficient ω r (motionQuadratic u (conicVector b))

/-- Clearing the local cross-product scale gives the root probe of the motion. -/
theorem rootMotionProjection_scaled (ω b r : K) (hω : IsPrimitiveRoot ω 3) (hr : r ≠ 0)
    (u : Fin 3 → K) :
    crossScale ω r * rootMotionProjection ω b r u = -(chordFactor r b) * (rootVector r ⬝ᵥ u) := by
  let Q := motionQuadratic u (conicVector b)
  let A := baseLiftCoefficient ω r Q
  have hp := congrFun (baseLiftCoefficient_solves ω r hω hr Q) 0
  have hm := congrFun (baseLiftCoefficient_solves ω r hω hr Q) 1
  change sigmaPlus ω r ⬝ᵥ A = -thetaPlus ω * eval (sigmaPlus ω r) Q.val at hp
  change sigmaMinus ω r ⬝ᵥ A = -thetaMinus ω * eval (sigmaMinus ω r) Q.val at hm
  dsimp only [Q] at hp hm
  rw [eval_motionQuadratic] at hp hm
  exact conic_edge_lift ω b r hω u A hp hm

/-- At the moving base point both right sides vanish, so the explicit section gives zero. -/
theorem baseLiftCoefficient_motionQuadratic_diagonal (ω b : K) (hω : IsPrimitiveRoot ω 3)
    (u : Fin 3 → K) :
    baseLiftCoefficient ω b (motionQuadratic u (conicVector b)) = 0 := by
  have hrhs : baseLiftRhs ω b (motionQuadratic u (conicVector b)) = 0 := by
    funext i
    fin_cases i
    · change -thetaPlus ω * eval (sigmaPlus ω b) (motionQuadratic u (conicVector b)).val = 0
      rw [eval_motionQuadratic, conic_plus_annihilates ω b hω, mul_zero, mul_zero]
    · change -thetaMinus ω * eval (sigmaMinus ω b) (motionQuadratic u (conicVector b)).val = 0
      rw [eval_motionQuadratic, conic_minus_annihilates ω b hω, mul_zero, mul_zero]
  change (baseLiftMatrix ω b).mulVec (baseLiftRhs ω b (motionQuadratic u (conicVector b))) = 0
  rw [hrhs, Matrix.mulVec_zero]

/-- Three distinct old roots with nonzero chord factors give independent motion coordinates. -/
theorem rootMotionProjection_bijective [CharZero K] (ω b : K) (roots : Fin 3 → K)
    (hω : IsPrimitiveRoot ω 3) (hroots : ∀ i, roots i ≠ 0) (hinj : Function.Injective roots)
    (hq : ∀ i, chordFactor (roots i) b ≠ 0) :
    Function.Bijective (fun u i => rootMotionProjection ω b (roots i) u) := by
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of ![rootVector (roots 0), rootVector (roots 1),
    rootVector (roots 2)]
  have hdet : M.det ≠ 0 := rootProbe_det_ne_zero _ _ _
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  have hM (u : Fin 3 → K) (i : Fin 3) : M.mulVec u i = rootVector (roots i) ⬝ᵥ u := by
    fin_cases i <;> rfl
  have hMinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  have hMsurj : Function.Surjective M.mulVec :=
    LinearMap.surjective_of_injective (f := M.mulVecLin) hMinj
  constructor
  · intro u v he
    apply hMinj
    funext i
    have hi := congrArg (fun x : K => crossScale ω (roots i) * x) (congrFun he i)
    rw [rootMotionProjection_scaled ω b (roots i) hω (hroots i),
      rootMotionProjection_scaled ω b (roots i) hω (hroots i)] at hi
    rw [hM, hM]
    exact mul_left_cancel₀ (neg_ne_zero.mpr (hq i)) hi
  · intro z
    let y (i : Fin 3) := (crossScale ω (roots i) * z i) / (-chordFactor (roots i) b)
    obtain ⟨u, hu⟩ := hMsurj y
    refine ⟨u, funext fun i => ?_⟩
    apply mul_left_cancel₀ (crossScale_ne_zero ω (roots i) hω (hroots i))
    rw [rootMotionProjection_scaled ω b (roots i) hω (hroots i), ← hM, congrFun hu i]
    dsimp only [y]
    field_simp [hq i]

end IdealGeneration.TripleNormal
