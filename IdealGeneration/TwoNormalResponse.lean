module

public import IdealGeneration.TwoNormalEuler
public import IdealGeneration.DifferentialLine

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# First response in the two normal directions

For a residual Euler tuple, tangential components vanish to second order.
The two normal first coefficients are the scalar traces of its two residual
normal coefficients.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial TwoNormalTrace DifferentialLine

variable {K : Type*} [Field K] {m d : ℕ}

/-- The point on the common trace with the specified trace coordinates. -/
def commonTracePoint (y : Fin m → K) : Fin (m + 2) → K :=
  Fin.cons 0 (Fin.cons 0 y)

/-- A velocity in the two normal directions. -/
def twoNormalVelocity (u v : K) : Fin (m + 2) → K :=
  Fin.cons u (Fin.cons v (fun _ => 0))

/-- Evaluation after the common-trace restriction is evaluation at `s=t=0`. -/
theorem eval_restrictTrace (y : Fin m → K) (f : Poly K (m + 2)) :
    eval y (restrictTrace K m f) = eval (commonTracePoint y) f := by
  simp [restrictTrace, AlgHom.comp_apply, eval_hyperplaneRestrict, commonTracePoint]

/-- The genuine first coefficient of the moving residual Euler tuple. -/
theorem residualEuler_first_coefficient (y : Fin m → K) (u v : K)
    (z : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :
    (fun j : Fin (m + 2) =>
      (lineSubstitution (commonTracePoint y) (twoNormalVelocity u v)
        ((residualEuler K m d z).val j).val).coeff 1) =
      Fin.cons (v * eval y (restrictTrace K m z.2.val))
        (Fin.cons (u * eval y (restrictTrace K m
          (-z.2 - tangentProduct K m d z.1).val)) (fun _ => 0)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change (lineSubstitution (commonTracePoint y) (twoNormalVelocity u v)
      (X (0 : Fin (m + 1)).succ * z.2.val)).coeff 1 = _
    rw [coeff_one_coordinate_mul _ _ _ _ (by rfl), eval_restrictTrace]
    rfl
  · refine Fin.cases ?_ (fun i => ?_) j
    · change (lineSubstitution (commonTracePoint y) (twoNormalVelocity u v)
        (X (0 : Fin (m + 2)) * (-z.2 - tangentProduct K m d z.1).val)).coeff 1 =
          u * eval y (restrictTrace K m (-z.2 - tangentProduct K m d z.1).val)
      rw [coeff_one_coordinate_mul _ _ _ _ (by rfl), eval_restrictTrace]
      rfl
    · change (lineSubstitution (commonTracePoint y) (twoNormalVelocity u v)
        (X (0 : Fin (m + 2)) *
          (X (0 : Fin (m + 1)).succ * (z.1 i).val))).coeff 1 = 0
      rw [coeff_one_coordinate_mul _ _ _ _ (by rfl), map_mul, eval_X]
      simp [commonTracePoint]

end IdealGeneration.TwoNormalIntegral
