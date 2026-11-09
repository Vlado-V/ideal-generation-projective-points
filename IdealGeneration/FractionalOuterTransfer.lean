module

public import IdealGeneration.FractionalOuterResidual
public import IdealGeneration.FractionalResidualOpen
public import IdealGeneration.FractionalTopMove

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The outer fractional transfer

An actual lower joint witness is made compatible with scalar interpolation,
then scalar cancellation and one final transverse movement give ideal generation.
-/

noncomputable section
namespace IdealGeneration.FractionalOuterTransfer
open Module MvPolynomial DifferentialPoint DifferentialFiber FractionalHyperplane
  FractionalCompatibility FractionalOuterCancellation FractionalOuterResidual FractionalTopMove
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]

/-- The fixed partial image supplied by the initial upper-critical trace. -/
abbrev initialImage {n p d : ℕ} (A : PointCoordinates K n p) (y : Fin n → K) :=
  topTraceImage y (TraceKernel A (d + 1))

/-- The injective lower witness gives the corresponding ambient ideal-generation assertion. -/
theorem injective_joint_to_idealGeneration [CharZero K] {n p q z d : ℕ}
    (A : PointCoordinates K n p) (y : Fin n → K)
    (hscalar : Function.Surjective (pointEvaluation K (snocPoints A y) (d + 1)))
    (htrace : Function.Injective ((vectorEvaluation (Fin.snoc y 1)).comp
      (TraceKernel A (d + 1)).subtype))
    (hcount : (p + 1) + q = (n + (d + 1)).choose (d + 1))
    (hz : z + q ≤ N (n + 2) d)
    (a₀ : JointCoordinates (K := K) n q z)
    (hinj : Function.Injective (twoLevelEvaluation y ((initialImage (d := d) A y).map dropLast) a₀ d)) :
    IdealGenerationAt K (n + 1) (d + 1) ((z + q) + (p + 1)) := by
  let B := TraceKernel A (d + 1)
  let L := initialImage (d := d) A y
  have hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0 := topTraceImage_tangent y B
  obtain ⟨a, ha, hcompat, hoff⟩ := compatible_twoLevel_injective
    y (L.map dropLast) (snocPoints A y) hscalar hcount a₀ hinj
  have hspecial : Function.Injective (specializedResidualMap (d := d) A y L a) :=
    specialized_residual_injective A y L a hL hoff hcompat ha
  have hdirect : Function.Injective (directResidualMap (d := d) A y B a) :=
    (specialized_residual_injective_iff_direct A y B a).mp hspecial
  obtain ⟨Z, hZ, _hpost, hres⟩ := FractionalResidualOpen.injective_off_witness
    (fun i => Fin.cons 0 (chartPoint K A i)) B (Fin.cons 0 (Fin.snoc y 1))
    (specializedFullConfiguration a) hdirect hz
  exact idealGenerationAt_of_top_injective Z A y hZ htrace hres

/-- The independent lower witness gives the corresponding ambient ideal-generation assertion. -/
theorem surjective_joint_to_idealGeneration [CharZero K] {n p q z d : ℕ}
    (A : PointCoordinates K n p) (y : Fin n → K)
    (hscalar : Function.Surjective (pointEvaluation K (snocPoints A y) (d + 1)))
    (htrace : Function.Surjective (eulerTraceEvaluation A (d + 1)))
    (hcount : (p + 1) + q = (n + (d + 1)).choose (d + 1))
    (hz : z + q ≤ N (n + 2) d)
    (a₀ : JointCoordinates (K := K) n q z)
    (hsurj : Function.Surjective (twoLevelEvaluation y ((initialImage (d := d) A y).map dropLast) a₀ d)) :
    IdealGenerationAt K (n + 1) (d + 1) ((z + q) + (p + 1)) := by
  let B := TraceKernel A (d + 1)
  let L := initialImage (d := d) A y
  have hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0 := topTraceImage_tangent y B
  obtain ⟨a, ha, hcompat, hoff⟩ := compatible_twoLevel_surjective
    y (L.map dropLast) (snocPoints A y) hscalar hcount a₀ hsurj
  have hspecial : Function.Surjective (specializedResidualMap (d := d) A y L a) :=
    specialized_residual_surjective A y L a hL hoff hcompat ha
  have hdirect : Function.Surjective (directResidualMap (d := d) A y B a) :=
    (specialized_residual_surjective_iff_direct A y B a).mp hspecial
  obtain ⟨Z, hZ, hpost, hres⟩ := FractionalResidualOpen.surjective_off_witness
    (fun i => Fin.cons 0 (chartPoint K A i)) B (Fin.cons 0 (Fin.snoc y 1))
    (specializedFullConfiguration a) hdirect hz
  exact idealGenerationAt_of_top_surjective Z A y hZ htrace hres hpost hscalar

end IdealGeneration.FractionalOuterTransfer
