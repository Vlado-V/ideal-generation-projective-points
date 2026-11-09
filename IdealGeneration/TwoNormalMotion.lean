module

public import IdealGeneration.TwoNormalResponse
public import IdealGeneration.TwoNormalSliceCokernel
public import IdealGeneration.DifferentialPoint

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# A fixed Euler-fiber target for moving trace points

Subtracting the Euler contraction in the last coordinate identifies the
moving fibers with the special fibers. The two normal coordinates of the
first response are unchanged by this identification.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open MvPolynomial Module TwoNormalSlice
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p d : ℕ}

/-- Insert values into the last coordinate and put zero in every other coordinate. -/
def insertLastComponent (n : ℕ) :
    (Fin p → K) →ₗ[K] (Fin p → Fin (n + 1) → K) where
  toFun v i := Fin.snoc (fun _ => 0) (v i)
  map_add' v w := by
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
  map_smul' c v := by
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp

/-- On normalized representatives, last-coordinate insertion splits contraction. -/
theorem traceFiberDot_insertLast (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (v : Fin p → K) :
    traceFiberDot z (insertLastComponent n v) = v := by
  funext i
  change (∑ j, z i j * Fin.snoc (α := fun _ => K) (fun _ => 0) (v i) j) = v i
  rw [Fin.sum_univ_castSucc]
  simp [hz]

/-- Project full component values to the fixed Euler fibers by changing only
last-coordinate values. -/
def fiberRetraction (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) :
    (Fin p → Fin (n + 1) → K) →ₗ[K] TraceFibers z :=
  (LinearMap.id - (insertLastComponent n).comp (traceFiberDot z)).codRestrict _ (by
    intro v
    change traceFiberDot z (v - insertLastComponent n (traceFiberDot z v)) = 0
    rw [map_sub, traceFiberDot_insertLast z hz, sub_self])

@[simp] theorem fiberRetraction_val (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (v : Fin p → Fin (n + 1) → K) :
    (fiberRetraction z hz v).val = v - insertLastComponent n (traceFiberDot z v) := rfl

/-- The retraction fixes values that already satisfy their Euler equations. -/
theorem fiberRetraction_self (z : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (v : TraceFibers z) :
    fiberRetraction z hz v.val = v := by
  apply Subtype.ext
  rw [fiberRetraction_val, show traceFiberDot z v.val = 0 from v.property, map_zero, sub_zero]

/-- Retraction to a second normalized fiber depends only on the first
coordinates, so any prior retraction can be removed. -/
theorem fiberRetraction_retraction (z w : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (hw : ∀ i, w i (Fin.last n) = 1)
    (v : Fin p → Fin (n + 1) → K) :
    fiberRetraction z hz (fiberRetraction w hw v).val = fiberRetraction z hz v := by
  apply Subtype.ext
  simp only [fiberRetraction_val]
  rw [map_sub, traceFiberDot_insertLast z hz, map_sub]
  abel

/-- Two normalized point configurations have canonically identified Euler
fibers by keeping the first coordinates fixed. -/
def fiberTransport (z w : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (hw : ∀ i, w i (Fin.last n) = 1) :
    TraceFibers w ≃ₗ[K] TraceFibers z where
  toFun v := fiberRetraction z hz v.val
  invFun v := fiberRetraction w hw v.val
  left_inv v := (fiberRetraction_retraction w z hw hz v.val).trans (fiberRetraction_self w hw v)
  right_inv v := (fiberRetraction_retraction z w hz hw v.val).trans (fiberRetraction_self z hz v)
  map_add' v w := (fiberRetraction z hz).map_add v.val w.val
  map_smul' c v := (fiberRetraction z hz).map_smul c v.val

local instance relationMotionGroup : AddCommGroup (HyperplaneEuler.Relations K (n + 1) d) :=
  Module.addCommMonoidToAddCommGroup K

/-- The full component values along the chosen lines. -/
def lineValues (z v : Fin p → Fin (n + 1) → K) (d : ℕ) (a : Fin 1 → K) :
    HyperplaneEuler.Relations K (n + 1) d →ₗ[K] (Fin p → Fin (n + 1) → K) :=
  LinearMap.pi fun i => DifferentialPoint.lineEvaluation (z i) (v i) (a 0)

/-- The exact first-order remainder of the full component values. -/
def lineValueRemainder (z v : Fin p → Fin (n + 1) → K) (d : ℕ) (a : Fin 1 → K) :
    HyperplaneEuler.Relations K (n + 1) d →ₗ[K] (Fin p → Fin (n + 1) → K) :=
  LinearMap.pi fun i => DifferentialPoint.lineQuotient (z i) (v i) (a 0)

/-- Evaluation along the lines, with a fixed target equal to the special Euler fibers. -/
def lineFiberEvaluation (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) (a : Fin 1 → K) :
    HyperplaneEuler.Relations K (n + 1) d →ₗ[K] TraceFibers z :=
  (fiberRetraction z hz).comp (lineValues z v d a)

/-- The first-order remainder with the same fixed fiber target. -/
def lineFiberRemainder (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) (a : Fin 1 → K) :
    HyperplaneEuler.Relations K (n + 1) d →ₗ[K] TraceFibers z :=
  (fiberRetraction z hz).comp (lineValueRemainder z v d a)

@[simp] theorem lineFiberEvaluation_zero (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) :
    lineFiberEvaluation z v hz d 0 = traceFiberEvaluation z d := by
  have h : lineValues z v d 0 = relationEvaluation z d := by
    ext F i j
    simp [lineValues, relationEvaluation]
  unfold lineFiberEvaluation
  rw [h]
  apply LinearMap.ext
  intro F
  exact fiberRetraction_self z hz (traceFiberEvaluation z d F)

/-- The fixed-target motion has the exact first-order expansion required by
the rank deformation theorem. -/
theorem lineFiberEvaluation_expansion (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) (a : Fin 1 → K) :
    lineFiberEvaluation z v hz d a = traceFiberEvaluation z d + a 0 • lineFiberRemainder z v hz d a := by
  have h : lineValues z v d a = lineValues z v d 0 + a 0 • lineValueRemainder z v d a := by
    ext F i j
    exact congrFun (LinearMap.congr_fun
      (DifferentialPoint.lineEvaluation_expansion (d := d) (z i) (v i) (a 0)) F) j
  rw [← lineFiberEvaluation_zero z v hz d]
  apply LinearMap.ext
  intro F
  change fiberRetraction z hz (lineValues z v d a F) =
    fiberRetraction z hz (lineValues z v d 0 F) +
      a 0 • fiberRetraction z hz (lineValueRemainder z v d a F)
  rw [h, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]

/-- Coordinatewise polynomial dependence for a double tuple of field values. -/
private theorem nestedPi_polynomial {σ I J : Type*} [Fintype I] [Fintype J]
    (F : (σ → K) → I → J → K)
    (hF : ∀ i j, IsPolynomialFamily (fun a => F a i j)) : IsPolynomialFamily F := by
  let G : (σ → K) → (I × J) → K := fun a ij => F a ij.1 ij.2
  have hG : IsPolynomialFamily G := DeformationMatrix.isPolynomialFamily_pi G
    (fun ij => hF ij.1 ij.2)
  let L : ((I × J) → K) →ₗ[K] (I → J → K) :=
    LinearMap.pi fun i : I => LinearMap.pi fun j : J => LinearMap.proj (i, j)
  exact hG.linear_comp L

/-- The fixed-target evaluation varies polynomially. -/
theorem lineFiberEvaluation_polynomial (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) :
    IsPolynomialFamily (lineFiberEvaluation z v hz d) := by
  apply isPolynomialFamily_linearMap
  intro F
  have h : IsPolynomialFamily (fun a => lineValues z v d a F) := by
    apply nestedPi_polynomial
    intro i j
    exact DeformationMatrix.polynomial_eval_isPolynomialFamily
      (DifferentialLine.lineSubstitution (z i) (v i) (F.val j).val)
  exact h.linear_comp (fiberRetraction z hz)

/-- The fixed-target remainder varies polynomially. -/
theorem lineFiberRemainder_polynomial (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (d : ℕ) :
    IsPolynomialFamily (lineFiberRemainder z v hz d) := by
  apply isPolynomialFamily_linearMap
  intro F
  have h : IsPolynomialFamily (fun a => lineValueRemainder z v d a F) := by
    apply nestedPi_polynomial
    intro i j
    exact DeformationMatrix.polynomial_eval_isPolynomialFamily
      (DifferentialLine.lineSubstitution (z i) (v i) (F.val j).val).divX
  exact h.linear_comp (fiberRetraction z hz)

/-- If the last coordinate stays fixed, the fixed-target motion is the actual
Euler evaluation transported by a linear equivalence of fibers. -/
theorem lineFiberEvaluation_eq_transport (z v : Fin p → Fin (n + 1) → K)
    (hz : ∀ i, z i (Fin.last n) = 1) (hv : ∀ i, v i (Fin.last n) = 0)
    (d : ℕ) (a : Fin 1 → K) :
    let w : Fin p → Fin (n + 1) → K := fun i j => z i j + a 0 * v i j
    let hw : ∀ i, w i (Fin.last n) = 1 := fun i => by simp [w, hz i, hv i]
    lineFiberEvaluation z v hz d a =
      (fiberTransport z w hz hw).toLinearMap.comp (traceFiberEvaluation w d) := by
  dsimp only
  apply LinearMap.ext
  intro F
  apply congrArg (fiberRetraction z hz)
  funext i j
  exact DifferentialPoint.lineEvaluation_apply (z i) (v i) (a 0) F j

/-- Pure normal component values lie in the special fibers on the common trace. -/
def normalTraceFiberValues {m : ℕ} (y : Fin p → Fin m → K) :
    ((Fin p → K) × (Fin p → K)) →ₗ[K] TraceFibers (fun i => commonTracePoint (y i)) where
  toFun v := ⟨fun i => Fin.cons (v.1 i) (Fin.cons (v.2 i) (fun _ => 0)), by
    funext i
    change (∑ j, commonTracePoint (y i) j *
      (Fin.cons (α := fun _ => K) (v.1 i)
        (Fin.cons (α := fun _ => K) (v.2 i) (fun _ => 0))) j) = 0
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [commonTracePoint]⟩
  map_add' v w := by
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> simp
  map_smul' c v := by
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> simp

/-- The special fiber remainder on a residual Euler relation has exactly the
two normal responses. Retraction leaves these first coefficients fixed. -/
theorem lineFiberRemainder_residualEuler {m : ℕ}
    (y : Fin p → Fin m → K) (u v : Fin p → K)
    (hz : ∀ i, commonTracePoint (y i) (Fin.last (m + 1)) = 1)
    (w : (Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :
    lineFiberRemainder (fun i => commonTracePoint (y i))
        (fun i => twoNormalVelocity (m := m) (u i) (v i)) hz (d + 1 + 1) 0
        (TwoNormalTrace.residualEuler K m d w) =
      normalTraceFiberValues y
        (fun i => v i * eval (y i) (TwoNormalTrace.restrictTrace K m w.2.val),
          fun i => u i * eval (y i) (TwoNormalTrace.restrictTrace K m
            (-w.2 - TwoNormalTrace.tangentProduct K m d w.1).val)) := by
  let z := fun i => commonTracePoint (y i)
  let speed := fun i => twoNormalVelocity (m := m) (u i) (v i)
  let N := normalTraceFiberValues y
    (fun i => v i * eval (y i) (TwoNormalTrace.restrictTrace K m w.2.val),
      fun i => u i * eval (y i) (TwoNormalTrace.restrictTrace K m
        (-w.2 - TwoNormalTrace.tangentProduct K m d w.1).val))
  have he : lineValueRemainder z speed (d + 1 + 1) 0
      (TwoNormalTrace.residualEuler K m d w) = N.val := by
    funext i j
    change DifferentialLine.quotientLine (z i) (speed i) 0
      ((TwoNormalTrace.residualEuler K m d w).val j).val = N.val i j
    rw [DifferentialLine.quotientLine_zero]
    exact congrFun (residualEuler_first_coefficient (y i) (u i) (v i) w) j
  change fiberRetraction z hz (lineValueRemainder z speed (d + 1 + 1) 0
    (TwoNormalTrace.residualEuler K m d w)) = N
  rw [he]
  exact fiberRetraction_self z hz N

/-- The two normal response vectors are sums of their separate point coordinates. -/
theorem normalTraceFiberValues_eq_sum {m : ℕ}
    (y : Fin p → Fin m → K) (s t : Fin p → K) :
    normalTraceFiberValues y (s, t) =
      (∑ i, s i • normalTraceFiberValues y (Pi.single i 1, 0)) +
      (∑ i, t i • normalTraceFiberValues y (0, Pi.single i 1)) := by
  classical
  have hs : (∑ i, s i • ((Pi.single i 1 : Fin p → K), (0 : Fin p → K))) = (s, 0) := by
    apply Prod.ext
    · funext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have ht : (∑ i, t i • ((0 : Fin p → K), (Pi.single i 1 : Fin p → K))) = (0, t) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · funext j
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [show (s, t) = (s, 0) + (0, t) by simp, map_add]
  rw [← hs, ← ht, map_sum, map_sum]
  simp only [map_smul]

end IdealGeneration.TwoNormalIntegral
