module

public import IdealGeneration.TwoNormalIntegralAssembly
public import IdealGeneration.TwoNormalPostulation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# From the marked motion to an ordinary point-ideal witness

The four groups are concatenated into one affine configuration. Euler fiber
transport preserves the rank of the actual evaluation, and scalar
postulation persists on a principal open of the motion parameter.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial Module TwoNormalSlice TwoNormalTrace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p q b k d : ℕ}

/-- Restrict the fiber values of concatenated representatives to the two groups. -/
private def appendFiberEquiv (A : Fin p → Fin (n + 1) → K)
    (B : Fin q → Fin (n + 1) → K) :
    TraceFibers (Fin.append A B) ≃ₗ[K] (TraceFibers A × TraceFibers B) where
  toFun F := (⟨fun i => F.val (i.castAdd q), by
    funext i
    have h := congrFun (LinearMap.mem_ker.mp F.property) (i.castAdd q)
    change (∑ j, Fin.append A B (i.castAdd q) j * F.val (i.castAdd q) j) = 0 at h
    change (∑ j, A i j * F.val (i.castAdd q) j) = 0
    simpa only [Fin.append_left] using h⟩,
    ⟨fun i => F.val (i.natAdd p), by
      funext i
      have h := congrFun (LinearMap.mem_ker.mp F.property) (i.natAdd p)
      change (∑ j, Fin.append A B (i.natAdd p) j * F.val (i.natAdd p) j) = 0 at h
      change (∑ j, B i j * F.val (i.natAdd p) j) = 0
      simpa only [Fin.append_right] using h⟩)
  invFun F := ⟨Fin.append F.1.val F.2.val, by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (∑ l, Fin.append A B (j.castAdd q) l *
        Fin.append F.1.val F.2.val (j.castAdd q) l) = 0
      simp only [Fin.append_left]
      exact congrFun (LinearMap.mem_ker.mp F.1.property) j
    · change (∑ l, Fin.append A B (j.natAdd p) l *
        Fin.append F.1.val F.2.val (j.natAdd p) l) = 0
      simp only [Fin.append_right]
      exact congrFun (LinearMap.mem_ker.mp F.2.property) j⟩
  left_inv F := by
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j
  right_inv F := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i
    · exact Fin.append_left _ _ i
    · exact Fin.append_right _ _ i
  map_add' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_smul' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

private theorem appendFiberEquiv_evaluation
    (A : Fin p → Fin (n + 1) → K) (B : Fin q → Fin (n + 1) → K) (D : ℕ) :
    (appendFiberEquiv A B).toLinearMap.comp (traceFiberEvaluation (Fin.append A B) D) =
      (traceFiberEvaluation A D).prod (traceFiberEvaluation B D) := by
  apply LinearMap.ext
  intro F
  apply Prod.ext <;> apply Subtype.ext <;> funext i j
  · change eval (Fin.append A B (i.castAdd q)) (F.val j).val = eval (A i) (F.val j).val
    rw [Fin.append_left]
  · change eval (Fin.append A B (i.natAdd p)) (F.val j).val = eval (B i) (F.val j).val
    rw [Fin.append_right]

/-- Translate the point-first fiber tuples to the component-first Euler square. -/
private def chartFiberEquiv (c : PointCoordinates K n p) :
    TraceFibers (chartPoint K c) ≃ₗ[K] (fiberMultiplication c).ker where
  toFun v := ⟨fun j i => v.val i j, v.property⟩
  invFun v := ⟨fun i j => v.val j i, v.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem hasMaximalRank_of_equiv_comp {V W U : Type*}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    [AddCommMonoid U] [Module K U] (e : W ≃ₗ[K] U) (F : V →ₗ[K] W) :
    HasMaximalRank (e.toLinearMap.comp F) ↔ HasMaximalRank F := by
  constructor
  · rintro (hi | hs)
    · exact Or.inl fun _ _ h => hi (congrArg e h)
    · exact Or.inr fun y => by
        obtain ⟨x, hx⟩ := hs (e y)
        exact ⟨x, e.injective hx⟩
  · rintro (hi | hs)
    · exact Or.inl (e.injective.comp hi)
    · exact Or.inr (e.surjective.comp hs)

/-- The actual moving trace representatives, still in the same affine chart. -/
def markedMovingTrace (z : Fin k → Fin n → K) (v u : Fin k → K) (t : Fin 1 → K) :
    Fin k → Fin (n + 2) → K :=
  fun i j => commonTracePoint (z i) j + t 0 * twoNormalVelocity (m := n) (u i) (v i) j

private theorem twoNormalVelocity_last {m : ℕ} (hm : 0 < m) (u v : K) :
    twoNormalVelocity (m := m) u v (Fin.last (m + 1)) = 0 := by
  cases m with
  | zero => omega
  | succ m =>
      change twoNormalVelocity (m := m + 1) u v (Fin.last m).succ.succ = 0
      simp only [twoNormalVelocity, Fin.cons_succ]

private theorem markedMovingTrace_last {m : ℕ} (hm : 0 < m)
    (z : Fin k → Fin m → K)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (v u : Fin k → K) (t : Fin 1 → K) (i : Fin k) :
    markedMovingTrace z v u t i (Fin.last (m + 1)) = 1 := by
  simp only [markedMovingTrace, hz, twoNormalVelocity_last hm, mul_zero, add_zero]

private theorem markedScalarEvaluation_polynomial {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Xpts : Fin q → Fin (m + 2) → K)
    (z : Fin k → Fin m → K) (v u : Fin k → K) (d : ℕ) :
    IsPolynomialFamily (fun t => markedScalarEvaluation (d := d) A B Xpts
      (markedMovingTrace z v u t)) := by
  apply isPolynomialFamily_linearMap
  intro f
  have hZ : IsPolynomialFamily (fun t => representativeEvaluation K
      (markedMovingTrace z v u t) (d + 1 + 1) f) := by
    apply DeformationMatrix.isPolynomialFamily_pi
    intro i
    change IsPolynomialFamily (fun t : Fin 1 → K => eval (markedMovingTrace z v u t i) f.val)
    let y := commonTracePoint (z i)
    let speed := twoNormalVelocity (m := m) (u i) (v i)
    let P := DifferentialLine.lineSubstitution y speed f.val
    have h : (fun t : Fin 1 → K => eval (markedMovingTrace z v u t i) f.val) =
        (fun t : Fin 1 → K => P.eval (t 0)) := by
      funext t
      change eval (fun j => y j + t 0 * speed j) f.val = P.eval (t 0)
      exact (DifferentialLine.eval_lineSubstitution y speed f.val (t 0)).symm
    rw [h]
    exact DeformationMatrix.polynomial_eval_isPolynomialFamily P
  exact (isPolynomialFamily_const _).prod_mk
    ((isPolynomialFamily_const _).prod_mk ((isPolynomialFamily_const _).prod_mk hZ))

/-- The chart representatives of the single concatenated configuration. -/
def markedRepresentatives {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Z : Fin k → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) : Fin (b + (b + (k + q))) → Fin (m + 2) → K :=
  Fin.append A (Fin.append B (Fin.append Z Xpts))

private theorem representativeEvaluation_marked_surjective {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Z : Fin k → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) (d : ℕ)
    (h : Function.Surjective (markedScalarEvaluation (d := d) A B Xpts Z)) :
    Function.Surjective (representativeEvaluation K (markedRepresentatives A B Z Xpts)
      (d + 1 + 1)) := by
  intro v
  let vA : Fin b → K := fun i => v (i.castAdd (b + (k + q)))
  let vB : Fin b → K := fun i => v ((i.castAdd (k + q)).natAdd b)
  let vZ : Fin k → K := fun i => v (((i.castAdd q).natAdd b).natAdd b)
  let vX : Fin q → K := fun i => v (((i.natAdd k).natAdd b).natAdd b)
  obtain ⟨f, hf⟩ := h (vA, vB, vX, vZ)
  refine ⟨f, ?_⟩
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have hi : eval (A i) f.val = vA i := congrFun (congrArg Prod.fst hf) i
    change eval (markedRepresentatives A B Z Xpts (i.castAdd (b + (k + q)))) f.val = vA i
    simpa only [markedRepresentatives, Fin.append_left] using hi
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hi : eval (B i) f.val = vB i := congrFun (congrArg (fun w => w.2.1) hf) i
      change eval (markedRepresentatives A B Z Xpts ((i.castAdd (k + q)).natAdd b)) f.val = vB i
      simpa only [markedRepresentatives, Fin.append_right, Fin.append_left] using hi
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have hi : eval (Z i) f.val = vZ i := congrFun (congrArg (fun w => w.2.2.2) hf) i
        change eval (markedRepresentatives A B Z Xpts (((i.castAdd q).natAdd b).natAdd b))
          f.val = vZ i
        simpa only [markedRepresentatives, Fin.append_right, Fin.append_left] using hi
      · have hi : eval (Xpts i) f.val = vX i := congrFun (congrArg (fun w => w.2.2.1) hf) i
        change eval (markedRepresentatives A B Z Xpts (((i.natAdd k).natAdd b).natAdd b))
          f.val = vX i
        simpa only [markedRepresentatives, Fin.append_right] using hi

private def markedFiberEquiv {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Z : Fin k → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) :
    TraceFibers (markedRepresentatives A B Z Xpts) ≃ₗ[K]
      (TraceFibers A × (TraceFibers B × (TraceFibers Z × TraceFibers Xpts))) :=
  (appendFiberEquiv A (Fin.append B (Fin.append Z Xpts))).trans
    ((LinearEquiv.refl K (TraceFibers A)).prodCongr
      ((appendFiberEquiv B (Fin.append Z Xpts)).trans
        ((LinearEquiv.refl K (TraceFibers B)).prodCongr (appendFiberEquiv Z Xpts))))

private theorem markedFiberEquiv_evaluation {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Z : Fin k → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K) (D : ℕ) :
    (markedFiberEquiv A B Z Xpts).toLinearMap.comp
      (traceFiberEvaluation (markedRepresentatives A B Z Xpts) D) =
        (traceFiberEvaluation A D).prod ((traceFiberEvaluation B D).prod
          ((traceFiberEvaluation Z D).prod (traceFiberEvaluation Xpts D))) := by
  apply LinearMap.ext
  intro F
  have hA := LinearMap.congr_fun
    (appendFiberEquiv_evaluation A (Fin.append B (Fin.append Z Xpts)) D) F
  have hB := LinearMap.congr_fun
    (appendFiberEquiv_evaluation B (Fin.append Z Xpts) D) F
  have hZ := LinearMap.congr_fun (appendFiberEquiv_evaluation Z Xpts D) F
  change (markedFiberEquiv A B Z Xpts)
    (traceFiberEvaluation (markedRepresentatives A B Z Xpts) D F) = _
  simp only [markedFiberEquiv, markedRepresentatives, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [show appendFiberEquiv A (Fin.append B (Fin.append Z Xpts))
      (traceFiberEvaluation (Fin.append A (Fin.append B (Fin.append Z Xpts))) D F) =
    (traceFiberEvaluation A D F,
      traceFiberEvaluation (Fin.append B (Fin.append Z Xpts)) D F) from hA]
  rw [show appendFiberEquiv B (Fin.append Z Xpts)
      (traceFiberEvaluation (Fin.append B (Fin.append Z Xpts)) D F) =
    (traceFiberEvaluation B D F, traceFiberEvaluation (Fin.append Z Xpts) D F) from hB]
  rw [show appendFiberEquiv Z Xpts
      (traceFiberEvaluation (Fin.append Z Xpts) D F) =
    (traceFiberEvaluation Z D F, traceFiberEvaluation Xpts D F) from hZ]
  rfl

private theorem markedMovingEvaluation_maximalRank_ambient {m : ℕ} (hm : 0 < m)
    (a b' : PointCoordinates K m b) (z : Fin k → Fin m → K)
    (x : PointCoordinates K (m + 1) q)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (v u : Fin k → K) (t : Fin 1 → K)
    (h : HasMaximalRank
      (markedMovingEvaluation
        (ambientFixedEvaluation a b' z (chartPoint K x) (d + 1 + 1)) z
        (ambientTraceInclusion a b' z (chartPoint K x)) hz v u t)) :
    HasMaximalRank (traceFiberEvaluation
      (markedRepresentatives (ambientPointA a) (ambientPointB b')
        (markedMovingTrace z v u t) (chartPoint K x)) (d + 1 + 1)) := by
  let Z := markedMovingTrace z v u t
  let E := (LinearEquiv.refl K (TraceFibers (ambientPointA a))).prodCongr
    ((LinearEquiv.refl K (TraceFibers (ambientPointB b'))).prodCongr
      ((fiberTransport (fun i => commonTracePoint (z i)) Z hz
        (markedMovingTrace_last hm z hz v u t)).prodCongr
        (LinearEquiv.refl K (TraceFibers (chartPoint K x)))))
  let F := (traceFiberEvaluation (ambientPointA a) (d + 1 + 1)).prod
    ((traceFiberEvaluation (ambientPointB b') (d + 1 + 1)).prod
      ((traceFiberEvaluation Z (d + 1 + 1)).prod
        (traceFiberEvaluation (chartPoint K x) (d + 1 + 1))))
  have hspeed (i : Fin k) :
      twoNormalVelocity (m := m) (u i) (v i) (Fin.last (m + 1)) = 0 :=
    twoNormalVelocity_last hm (u i) (v i)
  have hline := lineFiberEvaluation_eq_transport (fun i => commonTracePoint (z i))
    (fun i => twoNormalVelocity (m := m) (u i) (v i)) hz hspeed (d + 1 + 1) t
  have hEF : E.toLinearMap.comp F = markedMovingEvaluation
      (ambientFixedEvaluation a b' z (chartPoint K x) (d + 1 + 1)) z
      (ambientTraceInclusion a b' z (chartPoint K x)) hz v u t := by
    unfold markedMovingEvaluation
    rw [hline]
    apply LinearMap.ext
    intro f
    change (traceFiberEvaluation (ambientPointA a) (d + 1 + 1) f,
      traceFiberEvaluation (ambientPointB b') (d + 1 + 1) f,
      fiberTransport (fun i => commonTracePoint (z i)) Z hz
        (markedMovingTrace_last hm z hz v u t) (traceFiberEvaluation Z (d + 1 + 1) f),
      traceFiberEvaluation (chartPoint K x) (d + 1 + 1) f) =
        (traceFiberEvaluation (ambientPointA a) (d + 1 + 1) f,
          traceFiberEvaluation (ambientPointB b') (d + 1 + 1) f, 0,
          traceFiberEvaluation (chartPoint K x) (d + 1 + 1) f) +
        (0, 0, fiberTransport (fun i => commonTracePoint (z i)) Z hz
          (markedMovingTrace_last hm z hz v u t) (traceFiberEvaluation Z (d + 1 + 1) f), 0)
    simp
  have hF : HasMaximalRank F := by
    apply (hasMaximalRank_of_equiv_comp E F).mp
    rw [hEF]
    exact h
  apply (hasMaximalRank_of_equiv_comp (markedFiberEquiv (ambientPointA a) (ambientPointB b')
    Z (chartPoint K x)) _).mp
  rw [markedFiberEquiv_evaluation]
  exact hF

private theorem ambientPointA_last {m : ℕ} (hm : 0 < m)
    (a : PointCoordinates K m b) (i : Fin b) :
    ambientPointA a i (Fin.last (m + 1)) = 1 := by
  cases m with
  | zero => omega
  | succ m =>
      change ambientPointA a i (Fin.last m).succ.succ = 1
      simp only [ambientPointA, Fin.cons_succ]
      exact chartPoint_last a i

private theorem ambientPointB_last {m : ℕ} (hm : 0 < m)
    (a : PointCoordinates K m b) (i : Fin b) :
    ambientPointB a i (Fin.last (m + 1)) = 1 := by
  cases m with
  | zero => omega
  | succ m =>
      change ambientPointB a i (Fin.last m).succ.succ = 1
      simp only [ambientPointB, Fin.cons_succ]
      exact chartPoint_last a i

private theorem idealGenerationAt_of_marked_representatives [CharZero K] {m : ℕ}
    (A B : Fin b → Fin (m + 2) → K) (Z : Fin k → Fin (m + 2) → K)
    (Xpts : Fin q → Fin (m + 2) → K)
    (hA : ∀ i, A i (Fin.last (m + 1)) = 1)
    (hB : ∀ i, B i (Fin.last (m + 1)) = 1)
    (hZ : ∀ i, Z i (Fin.last (m + 1)) = 1)
    (hX : ∀ i, Xpts i (Fin.last (m + 1)) = 1)
    (hscalar : Function.Surjective (markedScalarEvaluation (d := d) A B Xpts Z))
    (hEuler : HasMaximalRank (traceFiberEvaluation (markedRepresentatives A B Z Xpts)
      (d + 1 + 1))) :
    IdealGenerationAt K (m + 1) (d + 1 + 1) (b + (b + (k + q))) := by
  let R := markedRepresentatives A B Z Xpts
  have hRlast (i : Fin (b + (b + (k + q)))) : R i (Fin.last (m + 1)) = 1 := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [R, markedRepresentatives, Fin.append_left] using hA i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [R, markedRepresentatives, Fin.append_right, Fin.append_left] using hB i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa only [R, markedRepresentatives, Fin.append_right, Fin.append_left] using hZ i
        · simpa only [R, markedRepresentatives, Fin.append_right] using hX i
  let c := normalizedCoordinates R
  have hc : chartPoint K c = R := by
    funext i
    simpa only [c, hRlast i, one_mul] using
      normalizedCoordinates_scale R (fun i => by rw [hRlast]; exact one_ne_zero) i
  have hscalarC : Function.Surjective (pointEvaluation K c (d + 1 + 1)) := by
    change Function.Surjective (representativeEvaluation K (chartPoint K c) (d + 1 + 1))
    rw [hc]
    exact representativeEvaluation_marked_surjective A B Z Xpts d hscalar
  have hEulerC : HasMaximalRank (traceFiberEvaluation (chartPoint K c) (d + 1 + 1)) := by
    rw [hc]
    exact hEuler
  apply idealGenerationAt_of_witness (by omega) c hscalarC
  apply (pointEuler_maximalRank_iff c hscalarC).mpr
  exact (hasMaximalRank_of_equiv_comp (chartFiberEquiv c) _).mpr hEulerC

/-- Scalar postulation of the four ambient groups follows from interpolation
in their intrinsic charts and the nonzero normal heights. -/
theorem markedScalarEvaluation_surjective_of_groups {m : ℕ}
    (a b' : PointCoordinates K m b) (z : Fin k → Fin m → K)
    (x : PointCoordinates K (m + 1) q)
    (hAs : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hBt : ∀ i, chartPoint K b' i (0 : Fin (m + 1)) ≠ 0)
    (hXs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hXt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Surjective (pointEvaluation K a (d + 1)))
    (hB : Function.Surjective (pointEvaluation K b' (d + 1)))
    (hX : Function.Surjective (pointEvaluation K x d))
    (hZ : Function.Surjective (scalarEvaluation z (d + 1 + 1))) :
    Function.Surjective (markedScalarEvaluation (d := d)
      (ambientPointA a) (ambientPointB b') (chartPoint K x) (ambientTracePoint z)) := by
  apply markedScalarEvaluation_surjective
    (ambientPointA a) (ambientPointB b') (chartPoint K x) (ambientTracePoint z)
    hAs (fun _ => rfl) (fun _ => rfl) hBt hXs hXt (fun _ => rfl) (fun _ => rfl)
  · intro v
    obtain ⟨f, hf⟩ := hA v
    let F := swapForm K m (d + 1) (extendForm K (m + 1) (d + 1) f)
    have hF : restrictA K m F.val = f.val := by
      change hyperplaneRestrict K (m + 1) (swapNormals K m
        (swapNormals K m (hyperplaneExtend K (m + 1) f.val))) = f.val
      simp
    refine ⟨F, ?_⟩
    funext i
    change eval (sliceARepresentative K m (chartPoint K a i)) F.val = v i
    rw [← eval_restrictA K m (chartPoint K a i), hF]
    exact congrFun hf i
  · intro v
    obtain ⟨f, hf⟩ := hB v
    refine ⟨extendForm K (m + 1) (d + 1) f, ?_⟩
    funext i
    change eval (ambientPointB b' i) (hyperplaneExtend K (m + 1) f.val) = v i
    rw [ambientPointB_eq, ← eval_hyperplaneRestrict, hyperplaneRestrict_extend]
    exact congrFun hf i
  · exact hX
  · intro v
    obtain ⟨f, hf⟩ := hZ v
    let F := extendTraceForm K m (d + 1 + 1) f
    refine ⟨F, ?_⟩
    funext i
    change eval (commonTracePoint (z i)) F.val = v i
    rw [← eval_restrictTrace]
    have hF : restrictTrace K m F.val = f.val :=
      congrArg Subtype.val (restrict_extendTraceForm K m f)
    rw [hF]
    exact congrFun hf i

/-- Maximal Euler rank already present at the marked configuration gives the
general-points assertion at its total count. -/
theorem idealGenerationAt_of_marked_ambient_evaluation [CharZero K] {m : ℕ}
    (hm : 0 < m) (a b' : PointCoordinates K m b) (z : Fin k → Fin m → K)
    (x : PointCoordinates K (m + 1) q)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (hscalar : Function.Surjective (markedScalarEvaluation (d := d)
      (ambientPointA a) (ambientPointB b') (chartPoint K x) (ambientTracePoint z)))
    (hEuler : HasMaximalRank
      (ambientFiberEvaluation a b' z (chartPoint K x) (d + 1 + 1))) :
    IdealGenerationAt K (m + 1) (d + 1 + 1) (b + (b + (k + q))) := by
  apply idealGenerationAt_of_marked_representatives (ambientPointA a) (ambientPointB b')
    (ambientTracePoint z) (chartPoint K x) (ambientPointA_last hm a) (ambientPointB_last hm b')
    hz (chartPoint_last x) hscalar
  apply (hasMaximalRank_of_equiv_comp (markedFiberEquiv (ambientPointA a) (ambientPointB b')
    (ambientTracePoint z) (chartPoint K x)) _).mp
  rw [markedFiberEquiv_evaluation]
  exact hEuler

/-- A scalar-postulated marked motion with maximal Euler rank gives the
ordinary general-points ideal-generation theorem at its total count. -/
theorem idealGenerationAt_of_marked_moving_evaluation [CharZero K] {m : ℕ}
    (hm : 0 < m) (a b' : PointCoordinates K m b) (z : Fin k → Fin m → K)
    (x : PointCoordinates K (m + 1) q)
    (hz : ∀ i, commonTracePoint (z i) (Fin.last (m + 1)) = 1)
    (hscalar : Function.Surjective (markedScalarEvaluation (d := d)
      (ambientPointA a) (ambientPointB b') (chartPoint K x) (ambientTracePoint z)))
    (v u : Fin k → K) (P : MvPolynomial (Fin 1) K) (hP : eval 0 P ≠ 0)
    (hmotion : ∀ t : Fin 1 → K, t 0 ≠ 0 → eval t P ≠ 0 → HasMaximalRank
      (markedMovingEvaluation
        (ambientFixedEvaluation a b' z (chartPoint K x) (d + 1 + 1)) z
        (ambientTraceInclusion a b' z (chartPoint K x)) hz v u t)) :
    IdealGenerationAt K (m + 1) (d + 1 + 1) (b + (b + (k + q))) := by
  let A := ambientPointA a
  let B := ambientPointB b'
  let Xpts := chartPoint K x
  let F := fun t => markedScalarEvaluation (d := d) A B Xpts (markedMovingTrace z v u t)
  have hzero : markedMovingTrace z v u 0 = ambientTracePoint z := by
    funext i j
    change commonTracePoint (z i) j + 0 * twoNormalVelocity (u i) (v i) j =
      ambientTracePoint z i j
    rw [zero_mul, add_zero]
    rfl
  have hF₀ : Function.Surjective (F 0) := by
    change Function.Surjective (markedScalarEvaluation (d := d) A B Xpts (markedMovingTrace z v u 0))
    rw [hzero]
    exact hscalar
  obtain ⟨Q, hQ, hQr⟩ := rank_polynomial_principal_open F
    (markedScalarEvaluation_polynomial A B Xpts z v u d) 0
  have hPQ : P * Q * (X 0 : MvPolynomial (Fin 1) K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by intro h; simp [h] at hP) (by intro h; simp [h] at hQ)) (X_ne_zero 0)
  obtain ⟨t, ht⟩ : ∃ t : Fin 1 → K, eval t (P * Q * X 0) ≠ 0 := by
    by_contra! h
    exact hPQ (MvPolynomial.funext h)
  have ht' : (eval t P ≠ 0 ∧ eval t Q ≠ 0) ∧ t 0 ≠ 0 := by
    simpa only [map_mul, eval_X, mul_ne_zero_iff] using ht
  have hFt : Function.Surjective (F t) := by
    have hdim := hQr t ht'.1.2
    rw [LinearMap.range_eq_top.mpr hF₀, finrank_top] at hdim
    exact LinearMap.range_eq_top.mp
      (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hdim))
  exact idealGenerationAt_of_marked_representatives A B (markedMovingTrace z v u t) Xpts
    (ambientPointA_last hm a) (ambientPointB_last hm b')
    (markedMovingTrace_last hm z hz v u t) (chartPoint_last x) hFt
    (markedMovingEvaluation_maximalRank_ambient hm a b' z x hz v u t
      (hmotion t ht'.2 ht'.1.1))

end IdealGeneration.TwoNormalIntegral
