module

public import IdealGeneration.TwoNormalAmbientKernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The raw two-slice polynomial pair

Before imposing the off-slice ideal conditions, all pairs of slice forms can
be realized by the coefficients of a residual Euler tuple.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial TwoNormalTrace

set_option maxHeartbeats 800000

variable (K : Type*) [Field K] (m : ℕ)

/-- The free coefficients of the residual Euler tuple. -/
abbrev RawResidualParameters (d : ℕ) :=
  (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)

/-- The two slice forms that specify vanishing of a raw residual tuple. -/
def rawSlicePair (d : ℕ) :
    RawResidualParameters K m d →ₗ[K]
      (Forms K (m + 1) (d + 1) × Forms K (m + 1) (d + 1)) :=
  let h := LinearMap.snd K (Fin m → Forms K (m + 2) d) (Forms K (m + 2) (d + 1))
  let a := LinearMap.fst K (Fin m → Forms K (m + 2) d) (Forms K (m + 2) (d + 1))
  ((restrictAForm K m (d + 1)).comp (h + (tangentProduct K m d).comp a)).prod
    ((restrictForm K (m + 1) (d + 1)).comp h)

@[simp] theorem rawSlicePair_fst {d : ℕ} (w : RawResidualParameters K m d) :
    (rawSlicePair K m d w).1 = restrictAForm K m (d + 1)
      (w.2 + tangentProduct K m d w.1) := rfl

@[simp] theorem rawSlicePair_snd {d : ℕ} (w : RawResidualParameters K m d) :
    (rawSlicePair K m d w).2 = restrictForm K (m + 1) (d + 1) w.2 := rfl

/-- The slice conditions evaluated at the two actual point groups. -/
def rawSlicePairEvaluation {p r : ℕ} (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (d : ℕ) :
    RawResidualParameters K m d →ₗ[K] ((Fin p → K) × (Fin r → K)) :=
  ((pointEvaluation K a (d + 1)).prodMap (pointEvaluation K b (d + 1))).comp
    (rawSlicePair K m d)

/-- On coefficients in the off-slice ideal, this is the existing residual pair evaluation. -/
theorem rawSlicePairEvaluation_parameterLift {p r q : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (d : ℕ) (w : ResidualParameters K m x d) :
    rawSlicePairEvaluation K m a b d (parameterLift K m x d w) =
      pairEvaluation K m a b x d w := rfl

private theorem restrictA_swap_extend {d : ℕ} (g : Forms K (m + 1) d) :
    restrictA K m (swapForm K m d (extendForm K (m + 1) d g)).val = g.val := by
  change hyperplaneRestrict K (m + 1) (swapNormals K m
    (swapNormals K m (hyperplaneExtend K (m + 1) g.val))) = g.val
  simp

/-- The complete two-slice polynomial pair is surjective, as in (5.7). -/
theorem rawSlicePair_surjective [CharZero K] (d : ℕ) :
    Function.Surjective (rawSlicePair K m d) := by
  rintro ⟨fA, fB⟩
  let hB := extendForm K (m + 1) (d + 1) fB
  obtain ⟨v, hv⟩ := formMultiplication_surjective (K := K) (m + 1) d
    (fA - restrictAForm K m (d + 1) hB)
  let liftA (f : Forms K (m + 1) d) := swapForm K m d (extendForm K (m + 1) d f)
  let h := hB + normalFormMul K (m + 1) d (liftA (v 0))
  let a : Fin m → Forms K (m + 2) d := fun i => liftA (v i.succ)
  have hLift (f : Forms K (m + 1) d) : restrictA K m (liftA f).val = f.val :=
    restrictA_swap_extend K m f
  refine ⟨(a, h), Prod.ext ?_ ?_⟩
  · rw [rawSlicePair_fst]
    apply Subtype.ext
    change restrictA K m (h.val + ∑ i, X i.succ.succ * (a i).val) = fA.val
    have hh : restrictA K m h.val = restrictA K m hB.val + X 0 * (v 0).val := by
      change restrictA K m (hB.val + X 0 * (liftA (v 0)).val) = _
      rw [map_add, map_mul, restrictA_s, hLift]
    rw [map_add, hh, map_sum]
    simp only [map_mul, restrictA_y, a, hLift]
    have hpol : (∑ j, X j * (v j).val) = fA.val - restrictA K m hB.val :=
      congrArg Subtype.val hv
    rw [Fin.sum_univ_succ] at hpol
    rw [add_assoc, hpol]
    abel
  · rw [rawSlicePair_snd]
    apply Subtype.ext
    change hyperplaneRestrict K (m + 1)
      (hyperplaneExtend K (m + 1) fB.val + X 0 * (liftA (v 0)).val) = fB.val
    simp only [map_add, hyperplaneRestrict_extend, map_mul, hyperplaneRestrict_X_zero,
      zero_mul, add_zero]

/-- With scalar postulation at each slice, the raw two-slice conditions are independent. -/
theorem rawSlicePairEvaluation_surjective [CharZero K] {p r : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r) (d : ℕ)
    (hA : Function.Surjective (pointEvaluation K a (d + 1)))
    (hB : Function.Surjective (pointEvaluation K b (d + 1))) :
    Function.Surjective (rawSlicePairEvaluation K m a b d) := by
  rintro ⟨u, v⟩
  obtain ⟨fA, hfA⟩ := hA u
  obtain ⟨fB, hfB⟩ := hB v
  obtain ⟨w, hw⟩ := rawSlicePair_surjective K m d (fA, fB)
  refine ⟨w, ?_⟩
  change (pointEvaluation K a (d + 1) (rawSlicePair K m d w).1,
    pointEvaluation K b (d + 1) (rawSlicePair K m d w).2) = (u, v)
  rw [hw]
  exact Prod.ext hfA hfB

end IdealGeneration.TwoNormalFractional
