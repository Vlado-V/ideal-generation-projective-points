module

public import IdealGeneration.CubicB11Actual

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Scalar entry formulas for B.11, with sums only over the old trace coordinates. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open MvPolynomial Parameters CubicNormalExpansion

variable {K : Type*} [Field K] {m : ℕ}

/-- The old-space value of the linear correction to a mixed lift. -/
def oldLinearValue (Q : Parameters K (m + 2)) (c : Fin (m + 2)) (a : Fin 3 → K)
    (y : Fin m → K) (r : Fin 2) : K :=
  ∑ i, Q.mixedLinear c a (Fin.castAdd 2 i) r * y i

/-- The old-space value of the normal-linear part of a pure lift. -/
def oldPureValue (Q : Parameters K (m + 2)) (a : Fin 4 → K)
    (y : Fin m → K) (r : Fin 2) : K :=
  let V := (Q.pureCubic a).val
  ∑ i : Fin m, ∑ j : Fin m,
    upperCoefficient V.2.2.1 V.2.2.2 (Fin.castAdd 2 i) (Fin.castAdd 2 j) r * y i * y j

/-- The remaining column uses one pure and two successive mixed solves. -/
def oldRemainingValue (Q : Parameters K (m + 2)) (c : Fin (m + 2))
    (u : Fin 2) (a : Fin 3 → K) (y : Fin m → K) (r : Fin 2) : K :=
  oldPureValue Q (shiftQuadratic u a) y r +
    ∑ i : Fin m, y i * oldLinearValue Q c (shiftLinear u (Q.mixedLinear c a (Fin.castAdd 2 i))) y r

/-- The five scalar entry formulas to be expressed in primitive coordinates. -/
def b7OldValue (Q : Parameters K (m + 2)) (y : Fin m → K) (w : Fin 2 → K) (r : Fin 2) :
    B7Column m → K
  | .localColumn _ c => localValue Q c y w r
  | .motion b i q => w b * y i *
      (oldLinearValue Q (Fin.natAdd m b) (normalBasis q) y r -
        oldLinearValue Q (Fin.castAdd 2 i) (normalBasis q) y r)
  | .extra b i u => w b * y i.val *
      oldLinearValue Q (Fin.natAdd m b) (shiftLinear u (crossNormal Q b i.val)) y r
  | .remaining b u q => w b * oldRemainingValue Q (Fin.natAdd m b) u (normalBasis q) y r

private theorem eval_linearRemainder_old (Q : Parameters K (m + 2))
    (c : Fin (m + 2)) (a : Fin 3 → K) (y : Fin m → K) (r : Fin 2) :
    eval (extendTrace y) (linearRemainder Q c a r) = oldLinearValue Q c a y r := by
  simp [linearRemainder, oldLinearValue, map_sum, Fin.sum_univ_add]

private theorem eval_traceA_old (V : Coefficients K (m + 2)) (r : Fin 2) (y : Fin m → K) :
    eval (extendTrace y) (traceA V r) = ∑ i : Fin m, ∑ j : Fin m,
      upperCoefficient V.2.2.1 V.2.2.2 (Fin.castAdd 2 i) (Fin.castAdd 2 j) r * y i * y j := by
  have h : eval (extendTrace y) (traceA V r) =
      traceQuadratic (fun i j => upperCoefficient V.2.2.1 V.2.2.2 i j r) (extendTrace y) := by
    simp [traceA, traceQuadratic, map_sum]
  rw [h]
  simp [traceQuadratic, Fin.sum_univ_add]

private theorem eval_mixedStarRemainder_old (Q : Parameters K (m + 2))
    (c : Fin (m + 2)) (u : Fin 2) (a : Fin 3 → K) (y : Fin m → K) (r : Fin 2) :
    eval (extendTrace y) (Q.mixedStarRemainder u c a r) = oldRemainingValue Q c u a y r := by
  simp [mixedStarRemainder, oldRemainingValue, oldPureValue, oldLinearValue,
    eval_traceA_old, map_sum, Fin.sum_univ_add]

/-- The scalar entry formulas evaluate the literal lower-order cubic columns. -/
theorem b7Value_actual_eq_oldValue (Q : Parameters K (m + 2))
    (y : Fin m → K) (w : Fin 2 → K) (r : Fin 2) (c : B7Column m) :
    b7Value (actualB7Data Q) y w r c = b7OldValue Q y w r c := by
  cases c with
  | localColumn _ _ => rfl
  | motion _ _ _ => simp [b7Value, actualB7Data, motionRemainder, b7OldValue, eval_linearRemainder_old]
  | extra _ _ _ => simp [b7Value, actualB7Data, extraRemainder, b7OldValue, eval_linearRemainder_old]
  | remaining _ _ _ => simp [b7Value, actualB7Data, b7OldValue, eval_mixedStarRemainder_old]

end IdealGeneration.CubicSupported.B5
