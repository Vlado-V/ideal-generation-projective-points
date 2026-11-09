module

public import IdealGeneration.TwoNormalRawPair
public import IdealGeneration.TwoNormalSliceCokernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Surjectivity of the normal part at the off-slice points

Scalar interpolation prescribes the tangential and first normal components.
The Euler equation then determines the second normal component. A correction
with coefficients in the off-slice point ideal solves the two slice groups
without changing the prescribed off-slice values.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ)

/-- Evaluate an unconstrained residual tuple in the actual off-slice fibers. -/
def rawNormalFiberEvaluation {q : ℕ} (x : PointCoordinates K (m + 1) q) (d : ℕ) :
    RawResidualParameters K m d →ₗ[K] TraceFibers (fun i => chartPoint K x i) :=
  (traceFiberEvaluation (fun i => chartPoint K x i) (d + 1 + 1)).comp (residualEuler K m d)

/-- The normal part satisfying both slice point conditions, evaluated off the slices. -/
def normalFiberEvaluation {p r q : ℕ} (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (x : PointCoordinates K (m + 1) q) (d : ℕ) :
    (rawSlicePairEvaluation K m a b d).ker →ₗ[K] TraceFibers (fun i => chartPoint K x i) :=
  (rawNormalFiberEvaluation K m x d).comp (rawSlicePairEvaluation K m a b d).ker.subtype

/-- Off-slice scalar interpolation realizes every raw normal fiber value. -/
theorem rawNormalFiberEvaluation_surjective {q : ℕ} (x : PointCoordinates K (m + 1) q)
    (d : ℕ) (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hG : Function.Surjective (pointEvaluation K x d))
    (hH : Function.Surjective (pointEvaluation K x (d + 1))) :
    Function.Surjective (rawNormalFiberEvaluation K m x d) := by
  intro u
  let t : Fin (m + 2) := (0 : Fin (m + 1)).succ
  choose g hg using fun j : Fin m => hG (fun i =>
    u.val i j.succ.succ / (chartPoint K x i 0 * chartPoint K x i t))
  obtain ⟨h, hh⟩ := hH (fun i => u.val i 0 / chartPoint K x i t)
  let w : RawResidualParameters K m d := (g, h)
  let v := rawNormalFiberEvaluation K m x d w
  have h₀ (i : Fin q) : v.val i 0 = u.val i 0 := by
    change eval (chartPoint K x i) (X t * h.val) = _
    have hi := congrFun hh i
    change eval (chartPoint K x i) h.val = u.val i 0 / chartPoint K x i t at hi
    rw [map_mul, eval_X, hi]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (ht i)
  have hy (i : Fin q) (j : Fin m) : v.val i j.succ.succ = u.val i j.succ.succ := by
    change eval (chartPoint K x i) (X 0 * (X t * (g j).val)) = _
    have hi := congrFun (hg j) i
    change eval (chartPoint K x i) (g j).val =
      u.val i j.succ.succ / (chartPoint K x i 0 * chartPoint K x i t) at hi
    rw [map_mul, map_mul, eval_X, eval_X, hi]
    rw [← mul_assoc, ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (mul_ne_zero (hs i) (ht i))
  have h₁ (i : Fin q) : v.val i t = u.val i t := by
    have hvdot : (∑ j, chartPoint K x i j * v.val i j) = 0 := congrFun v.property i
    have hudot : (∑ j, chartPoint K x i j * u.val i j) = 0 := congrFun u.property i
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hvdot hudot
    simp only [h₀ i, hy i] at hvdot
    have hz : chartPoint K x i t * (v.val i t - u.val i t) = 0 := by
      linear_combination hvdot - hudot
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ht i))
  refine ⟨w, Subtype.ext ?_⟩
  funext i j
  refine Fin.cases (h₀ i) (fun j => ?_) j
  exact Fin.cases (h₁ i) (hy i) j

/-- A correction in the off-slice ideal has zero off-slice fiber values. -/
theorem rawNormalFiberEvaluation_parameterLift_zero {q : ℕ}
    (x : PointCoordinates K (m + 1) q) (d : ℕ) (w : ResidualParameters K m x d) :
    rawNormalFiberEvaluation K m x d (parameterLift K m x d w) = 0 := by
  apply Subtype.ext
  funext i j
  exact (parameterEuler_off_trace_vanishing K m x (Fin.elim0 : Fin 0 → Fin m → K) w).1 i j

/-- An independent residual pair evaluation corrects the slice conditions of
any raw off-slice interpolation. -/
theorem normalFiberEvaluation_surjective_of_pair_surjective {p r q : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (d : ℕ)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hG : Function.Surjective (pointEvaluation K x d))
    (hH : Function.Surjective (pointEvaluation K x (d + 1)))
    (hpair : Function.Surjective (pairEvaluation K m a b x d)) :
    Function.Surjective (normalFiberEvaluation K m a b x d) := by
  intro u
  obtain ⟨w, hw⟩ := rawNormalFiberEvaluation_surjective K m x d hs ht hG hH u
  obtain ⟨c, hc⟩ := hpair (rawSlicePairEvaluation K m a b d w)
  let w' := w - parameterLift K m x d c
  have hker : w' ∈ (rawSlicePairEvaluation K m a b d).ker := by
    change rawSlicePairEvaluation K m a b d (w - parameterLift K m x d c) = 0
    rw [map_sub, rawSlicePairEvaluation_parameterLift, hc, sub_self]
  refine ⟨⟨w', hker⟩, ?_⟩
  change rawNormalFiberEvaluation K m x d (w - parameterLift K m x d c) = u
  rw [map_sub, rawNormalFiberEvaluation_parameterLift_zero, sub_zero, hw]

/-- The residual pair kernel dimension determines surjectivity of the residual
pair evaluation, since the coefficients are the actual two ideal pieces. -/
theorem pairEvaluation_surjective_of_kernel_finrank {p r q : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (d : ℕ)
    (hker : finrank K (pairEvaluation K m a b x d).ker + (p + r) =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1))) :
    Function.Surjective (pairEvaluation K m a b x d) := by
  let : AddCommGroup (pointDegreePiece K x d) := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup (pointDegreePiece K x (d + 1)) := Module.addCommMonoidToAddCommGroup K
  let : Module.Free K (pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  let : Module.Free K (pointDegreePiece K x (d + 1)) := Module.Free.of_divisionRing K _
  let : Module.Free K (Fin m → pointDegreePiece K x d) := Module.Free.of_divisionRing K _
  have hsrc : finrank K (ResidualParameters K m x d) =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1)) := by
    unfold ResidualParameters
    rw [Module.finrank_prod, Module.finrank_pi_fintype]
    simp
  have hdim := (pairEvaluation K m a b x d).ker.finrank_quotient_add_finrank
  rw [(pairEvaluation K m a b x d).quotKerEquivRange.finrank_eq, hsrc] at hdim
  have hrange : finrank K (pairEvaluation K m a b x d).range = p + r := by omega
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [hrange, Module.finrank_prod]
  simp

/-- The normal-part surjectivity in Proposition 5.1 follows from the computed
residual pair kernel dimension and scalar interpolation at the off-slice points. -/
theorem normalFiberEvaluation_surjective_of_kernel_finrank {p r q : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (d : ℕ)
    (hs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (ht : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hG : Function.Surjective (pointEvaluation K x d))
    (hH : Function.Surjective (pointEvaluation K x (d + 1)))
    (hker : finrank K (pairEvaluation K m a b x d).ker + (p + r) =
      m * finrank K (pointDegreePiece K x d) + finrank K (pointDegreePiece K x (d + 1))) :
    Function.Surjective (normalFiberEvaluation K m a b x d) :=
  normalFiberEvaluation_surjective_of_pair_surjective K m a b x d hs ht hG hH
    (pairEvaluation_surjective_of_kernel_finrank K m a b x d hker)

/-- The raw pair conditions force vanishing on both slice point groups. -/
theorem residualEuler_slice_vanishing {p r : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r) (d : ℕ)
    (w : RawResidualParameters K m d)
    (hw : rawSlicePairEvaluation K m a b d w = 0) :
    (∀ i j, eval (sliceARepresentative K m (chartPoint K a i))
        ((residualEuler K m d w).val j).val = 0) ∧
    (∀ i j, eval (Fin.cons 0 (chartPoint K b i))
        ((residualEuler K m d w).val j).val = 0) := by
  let T := tangentProduct K m d w.1
  have hA (i : Fin p) : eval (sliceARepresentative K m (chartPoint K a i))
      (w.2.val + T.val) = 0 := by
    rw [← eval_restrictA K m (chartPoint K a i)]
    exact congrFun (congrArg Prod.fst hw) i
  have hB (i : Fin r) : eval (Fin.cons 0 (chartPoint K b i)) w.2.val = 0 := by
    rw [← eval_hyperplaneRestrict K (m + 1) w.2.val (chartPoint K b i)]
    exact congrFun (congrArg Prod.snd hw) i
  constructor
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · change eval (sliceARepresentative K m (chartPoint K a i))
        (X (0 : Fin (m + 1)).succ * w.2.val) = 0
      simp [sliceARepresentative]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change eval (sliceARepresentative K m (chartPoint K a i))
          (X 0 * (-w.2.val - T.val)) = 0
        rw [show -w.2.val - T.val = -(w.2.val + T.val) by ring, map_mul, map_neg,
          hA, neg_zero, mul_zero]
      · change eval (sliceARepresentative K m (chartPoint K a i))
          (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val)) = 0
        simp [sliceARepresentative]
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · change eval (Fin.cons 0 (chartPoint K b i))
        (X (0 : Fin (m + 1)).succ * w.2.val) = 0
      rw [map_mul, hB, mul_zero]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change eval (Fin.cons 0 (chartPoint K b i)) (X 0 * (-w.2.val - T.val)) = 0
        simp
      · change eval (Fin.cons 0 (chartPoint K b i))
          (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val)) = 0
        simp

/-- Every residual tuple vanishes at all points of the common trace. -/
theorem residualEuler_trace_vanishing {q : ℕ} (z : Fin q → Fin m → K) (d : ℕ)
    (w : RawResidualParameters K m d) :
    ∀ i j, eval (Fin.cons 0 (Fin.cons 0 (z i))) ((residualEuler K m d w).val j).val = 0 := by
  intro i j
  refine Fin.cases ?_ (fun j => ?_) j
  · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
      (X (0 : Fin (m + 1)).succ * w.2.val) = 0
    simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
        (X 0 * (-w.2.val - (tangentProduct K m d w.1).val)) = 0
      simp
    · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
        (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val)) = 0
      simp

end IdealGeneration.TwoNormalFractional
