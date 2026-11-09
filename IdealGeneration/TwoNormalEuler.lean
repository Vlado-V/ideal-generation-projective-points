module

public import IdealGeneration.TwoNormalTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Euler relations with two normal factors

The residual Euler tuples are `(t h, s(-h-Σyᵢaᵢ), (st aᵢ)ᵢ)`.
This is formula (4.7), in the coordinate order `s,t,y₁,…,yₘ`.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- Multiplication by the second normal coordinate. -/
def secondNormalMul (d : ℕ) : Forms K (m + 2) d →ₗ[K] Forms K (m + 2) (d + 1) where
  toFun f := ⟨X (0 : Fin (m + 1)).succ * f.val, by
    change (X (0 : Fin (m + 1)).succ * f.val).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using
      (isHomogeneous_X (R := K) (0 : Fin (m + 1)).succ).mul f.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

@[simp] theorem secondNormalMul_val {d : ℕ} (f : Forms K (m + 2) d) :
    (secondNormalMul K m d f).val = X (0 : Fin (m + 1)).succ * f.val := rfl

/-- Construct the residual two-normal Euler tuple. -/
def residualEulerTuple (d : ℕ) :
    ((Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) →ₗ[K]
      (Fin (m + 2) → Forms K (m + 2) (d + 1 + 1)) where
  toFun z := Fin.cons (secondNormalMul K m (d + 1) z.2)
    (Fin.cons (normalFormMul K (m + 1) (d + 1) (-z.2 - tangentProduct K m d z.1))
      (fun i => normalFormMul K (m + 1) (d + 1) (secondNormalMul K m d (z.1 i))))
  map_add' z w := by
    funext i
    apply Subtype.ext
    refine Fin.cases ?_ (fun i => ?_) i
    · change X (0 : Fin (m + 1)).succ * (z.2.val + w.2.val) = _
      exact mul_add _ _ _
    · refine Fin.cases ?_ (fun i => ?_) i
      · have h := congrArg Subtype.val ((tangentProduct K m d).map_add z.1 w.1)
        change (tangentProduct K m d (z.1 + w.1)).val =
          (tangentProduct K m d z.1).val + (tangentProduct K m d w.1).val at h
        change X 0 * (-(z.2.val + w.2.val) - (tangentProduct K m d (z.1 + w.1)).val) =
          X 0 * (-z.2.val - (tangentProduct K m d z.1).val) +
            X 0 * (-w.2.val - (tangentProduct K m d w.1).val)
        rw [h]
        ring
      · change X 0 * (X (0 : Fin (m + 1)).succ * ((z.1 i).val + (w.1 i).val)) =
          X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val) +
            X 0 * (X (0 : Fin (m + 1)).succ * (w.1 i).val)
        ring
  map_smul' c z := by
    funext i
    apply Subtype.ext
    refine Fin.cases ?_ (fun i => ?_) i
    · change X (0 : Fin (m + 1)).succ * (c • z.2.val) = _
      exact mul_smul_comm _ _ _
    · refine Fin.cases ?_ (fun i => ?_) i
      · have h := congrArg Subtype.val ((tangentProduct K m d).map_smul c z.1)
        change (tangentProduct K m d (c • z.1)).val =
          c • (tangentProduct K m d z.1).val at h
        change X 0 * (-(c • z.2.val) - (tangentProduct K m d (c • z.1)).val) =
          c • (X 0 * (-z.2.val - (tangentProduct K m d z.1).val))
        rw [h]
        simp only [Algebra.smul_def]
        ring
      · change X 0 * (X (0 : Fin (m + 1)).succ * (c • (z.1 i).val)) =
          c • (X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val))
        simp only [Algebra.smul_def]
        ring

/-- The tuple satisfies the Euler equation as a polynomial identity. -/
theorem residualEulerTuple_relation (d : ℕ)
    (z : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :
    formMultiplication K (m + 2) (d + 1 + 1) (residualEulerTuple K m d z) = 0 := by
  apply Subtype.ext
  change (∑ i, X i * (residualEulerTuple K m d z i).val) = 0
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  change X 0 * (X (0 : Fin (m + 1)).succ * z.2.val) +
    (X (0 : Fin (m + 1)).succ *
      (X 0 * (-z.2.val - ∑ i, X i.succ.succ * (z.1 i).val)) +
      ∑ i, X i.succ.succ * (X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val))) = 0
  have hsum : (∑ i, X i.succ.succ * (X 0 *
      (X (0 : Fin (m + 1)).succ * (z.1 i).val))) =
      X 0 * X (0 : Fin (m + 1)).succ * (∑ i, X i.succ.succ * (z.1 i).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- Formula (4.7) regarded as a map into the genuine Euler relation space. -/
def residualEuler (d : ℕ) :
    ((Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) →ₗ[K]
      (formMultiplication K (m + 2) (d + 1 + 1)).ker :=
  (residualEulerTuple K m d).codRestrict _ (residualEulerTuple_relation K m d)

/-- The residual coefficients are uniquely determined by their Euler tuple. -/
theorem residualEuler_injective (d : ℕ) : Function.Injective (residualEuler K m d) := by
  intro z w hzw
  have heq : residualEulerTuple K m d z = residualEulerTuple K m d w :=
    congrArg Subtype.val hzw
  apply Prod.ext
  · funext i
    apply Subtype.ext
    have h := congrArg (fun f : Fin (m + 2) → Forms K (m + 2) (d + 1 + 1) =>
      (f i.succ.succ).val) heq
    change X 0 * (X (0 : Fin (m + 1)).succ * (z.1 i).val) =
      X 0 * (X (0 : Fin (m + 1)).succ * (w.1 i).val) at h
    exact mul_left_cancel₀ (X_ne_zero _) (mul_left_cancel₀ (X_ne_zero _) h)
  · apply Subtype.ext
    have h := congrArg (fun f : Fin (m + 2) → Forms K (m + 2) (d + 1 + 1) =>
      (f 0).val) heq
    exact mul_left_cancel₀ (X_ne_zero _) h

/-- The image of the residual pair map has the asserted parameter-space dimension. -/
theorem residualPair_range_finrank {p d : ℕ} (x : PointCoordinates K (m + 1) p)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (htrace : Function.Injective ((restrictTraceForm K m d).comp
      (pointDegreePiece K x d).subtype))
    (hproduct : Function.Injective (traceProduct K m d (pointDegreePiece K x d))) :
    finrank K (residualPair K m (d := d) x).range =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1)) := by
  rw [LinearMap.finrank_range_of_inj (residualPair_injective K m x hs htrace hproduct)]
  let : AddCommGroup (pointDegreePiece K x d) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (pointDegreePiece K x (d + 1)) := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K (pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  let : Module.Free K (pointDegreePiece K x (d + 1)) := Module.Free.of_divisionRing K _
  let : Module.Free K (Fin m → pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp

end IdealGeneration.TwoNormalTrace
