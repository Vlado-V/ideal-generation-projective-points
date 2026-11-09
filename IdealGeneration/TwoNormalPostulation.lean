module

public import IdealGeneration.TwoNormalEuler
public import IdealGeneration.RepresentativeGeneric

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar interpolation on the marked two-normal configuration

A trace interpolant is corrected successively by an `s` multiple, a `t`
multiple, and an `st` multiple. Each correction vanishes on all previously
settled groups.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial TwoNormalTrace

variable {K : Type*} [Field K] {m a b q p d : ℕ}

/-- A coordinate nonzero at all representatives propagates scalar
surjectivity to the next degree. -/
theorem representativeEvaluation_surjective_succ_of_coordinate
    {n r e : ℕ} (z : Fin r → Fin n → K) (j : Fin n)
    (hj : ∀ i, z i j ≠ 0)
    (h : Function.Surjective (representativeEvaluation K z e)) :
    Function.Surjective (representativeEvaluation K z (e + 1)) := by
  intro v
  obtain ⟨f, hf⟩ := h (fun i => v i / z i j)
  let g : Forms K n (e + 1) := ⟨MvPolynomial.X j * f.val, by
    change (MvPolynomial.X j * f.val).IsHomogeneous (e + 1)
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) j).mul f.property⟩
  refine ⟨g, ?_⟩
  funext i
  change eval (z i) (MvPolynomial.X j * f.val) = v i
  rw [map_mul, eval_X]
  have hi := congrFun hf i
  change eval (z i) f.val = v i / z i j at hi
  rw [hi]
  rw [mul_comm (z i j), div_mul_cancel₀ _ (hj i)]

/-- Scalar evaluation on the four marked groups in degree `d+2`. -/
def markedScalarEvaluation
    (A : Fin a → Fin (m + 2) → K) (B : Fin b → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) (Z : Fin p → Fin (m + 2) → K) :
    Forms K (m + 2) (d + 1 + 1) →ₗ[K]
      ((Fin a → K) × (Fin b → K) × (Fin q → K) × (Fin p → K)) :=
  (representativeEvaluation K A (d + 1 + 1)).prod
    ((representativeEvaluation K B (d + 1 + 1)).prod
      ((representativeEvaluation K Xpts (d + 1 + 1)).prod
        (representativeEvaluation K Z (d + 1 + 1))))

/-- The marked configuration has onto scalar evaluation from the four lower
scalar interpolation statements used in Proposition 4.5. -/
theorem markedScalarEvaluation_surjective
    (A : Fin a → Fin (m + 2) → K) (B : Fin b → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) (Z : Fin p → Fin (m + 2) → K)
    (hAs : ∀ i, A i (0 : Fin (m + 2)) ≠ 0)
    (hAt : ∀ i, A i (0 : Fin (m + 1)).succ = 0)
    (hBs : ∀ i, B i (0 : Fin (m + 2)) = 0)
    (hBt : ∀ i, B i (0 : Fin (m + 1)).succ ≠ 0)
    (hXs : ∀ i, Xpts i (0 : Fin (m + 2)) ≠ 0)
    (hXt : ∀ i, Xpts i (0 : Fin (m + 1)).succ ≠ 0)
    (hZs : ∀ i, Z i (0 : Fin (m + 2)) = 0)
    (hZt : ∀ i, Z i (0 : Fin (m + 1)).succ = 0)
    (hA : Function.Surjective (representativeEvaluation K A (d + 1)))
    (hB : Function.Surjective (representativeEvaluation K B (d + 1)))
    (hX : Function.Surjective (representativeEvaluation K Xpts d))
    (hZ : Function.Surjective (representativeEvaluation K Z (d + 1 + 1))) :
    Function.Surjective (markedScalarEvaluation (d := d) A B Xpts Z) := by
  rintro ⟨vA, vB, vX, vZ⟩
  obtain ⟨f₀, hf₀⟩ := hZ vZ
  obtain ⟨fA, hfA⟩ := hA (fun i =>
    (vA i - eval (A i) f₀.val) / A i 0)
  let cA := normalFormMul K (m + 1) (d + 1) fA
  obtain ⟨fB, hfB⟩ := hB (fun i =>
    (vB i - eval (B i) (f₀ + cA).val) / B i (0 : Fin (m + 1)).succ)
  let cB := secondNormalMul K m (d + 1) fB
  obtain ⟨fX, hfX⟩ := hX (fun i =>
    (vX i - eval (Xpts i) (f₀ + cA + cB).val) /
      (Xpts i 0 * Xpts i (0 : Fin (m + 1)).succ))
  let cX := normalFormMul K (m + 1) (d + 1) (secondNormalMul K m d fX)
  refine ⟨f₀ + cA + cB + cX, ?_⟩
  apply Prod.ext
  · funext i
    change eval (A i) (f₀.val + MvPolynomial.X 0 * fA.val +
      MvPolynomial.X (0 : Fin (m + 1)).succ * fB.val +
        MvPolynomial.X 0 * (MvPolynomial.X (0 : Fin (m + 1)).succ * fX.val)) = vA i
    simp only [map_add, map_mul, eval_X, hAt, zero_mul, mul_zero, add_zero]
    have hi := congrFun hfA i
    change eval (A i) fA.val = (vA i - eval (A i) f₀.val) / A i 0 at hi
    rw [hi]
    rw [mul_comm (A i 0), div_mul_cancel₀ _ (hAs i)]
    ring
  · apply Prod.ext
    · funext i
      change eval (B i) (f₀.val + MvPolynomial.X 0 * fA.val +
        MvPolynomial.X (0 : Fin (m + 1)).succ * fB.val +
          MvPolynomial.X 0 * (MvPolynomial.X (0 : Fin (m + 1)).succ * fX.val)) = vB i
      simp only [map_add, map_mul, eval_X, hBs, zero_mul, add_zero]
      have hi := congrFun hfB i
      change eval (B i) fB.val =
        (vB i - eval (B i) (f₀.val + MvPolynomial.X 0 * fA.val)) / B i (0 : Fin (m + 1)).succ at hi
      simp only [map_add, map_mul, eval_X, hBs, zero_mul, add_zero] at hi
      rw [hi]
      rw [mul_comm (B i (0 : Fin (m + 1)).succ), div_mul_cancel₀ _ (hBt i)]
      ring
    · apply Prod.ext
      · funext i
        change eval (Xpts i) (f₀.val + MvPolynomial.X 0 * fA.val +
          MvPolynomial.X (0 : Fin (m + 1)).succ * fB.val +
            MvPolynomial.X 0 * (MvPolynomial.X (0 : Fin (m + 1)).succ * fX.val)) = vX i
        simp only [map_add, map_mul, eval_X]
        have hi := congrFun hfX i
        change eval (Xpts i) fX.val =
          (vX i - eval (Xpts i) (f₀.val + MvPolynomial.X 0 * fA.val +
            MvPolynomial.X (0 : Fin (m + 1)).succ * fB.val)) /
              (Xpts i 0 * Xpts i (0 : Fin (m + 1)).succ) at hi
        simp only [map_add, map_mul, eval_X] at hi
        rw [hi]
        rw [← mul_assoc (Xpts i 0) (Xpts i (0 : Fin (m + 1)).succ),
          mul_comm (Xpts i 0 * Xpts i (0 : Fin (m + 1)).succ),
          div_mul_cancel₀ _ (mul_ne_zero (hXs i) (hXt i))]
        ring
      · funext i
        change eval (Z i) (f₀.val + MvPolynomial.X 0 * fA.val +
          MvPolynomial.X (0 : Fin (m + 1)).succ * fB.val +
            MvPolynomial.X 0 * (MvPolynomial.X (0 : Fin (m + 1)).succ * fX.val)) = vZ i
        simp only [map_add, map_mul, eval_X, hZs, hZt, zero_mul, mul_zero, add_zero]
        exact congrFun hf₀ i

end IdealGeneration.TwoNormalIntegral
