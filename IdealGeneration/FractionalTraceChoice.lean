module

public import IdealGeneration.PointMonotonicity
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Choosing a trace configuration and one further point

Principal-open conditions on the whole configuration, on its prefix, and on
its final point have a simultaneous solution.
-/

noncomputable section
namespace IdealGeneration.FractionalTraceChoice
open MvPolynomial

variable {K : Type*}

/-- Append a single affine point to an ordered configuration. -/
def adjoinPoint {n p : ℕ} (P : PointCoordinates K n p) (y : Fin n → K) :
    PointCoordinates K n (p + 1) :=
  fun ij => (Fin.snoc (fun i : Fin p => P (i, ij.2)) (y ij.2) : Fin (p + 1) → K) ij.1

/-- The final affine point of an ordered configuration. -/
def lastPoint {n p : ℕ} (Q : PointCoordinates K n (p + 1)) : Fin n → K :=
  fun j => Q (Fin.last p, j)

@[simp] theorem adjoinPoint_castSucc {n p : ℕ}
    (P : PointCoordinates K n p) (y : Fin n → K) (i : Fin p) (j : Fin n) :
    adjoinPoint P y (i.castSucc, j) = P (i, j) := by simp [adjoinPoint]

@[simp] theorem adjoinPoint_last {n p : ℕ}
    (P : PointCoordinates K n p) (y : Fin n → K) (j : Fin n) :
    adjoinPoint P y (Fin.last p, j) = y j := by simp [adjoinPoint]

@[simp] theorem restrict_adjoinPoint {n p : ℕ}
    (P : PointCoordinates K n p) (y : Fin n → K) :
    restrictPoints (adjoinPoint P y) Fin.castSucc = P := by
  funext ij
  simp [restrictPoints]

@[simp] theorem lastPoint_adjoinPoint {n p : ℕ}
    (P : PointCoordinates K n p) (y : Fin n → K) : lastPoint (adjoinPoint P y) = y := by
  funext j
  simp [lastPoint]

/-- Splitting and rejoining an ordered configuration changes none of its coordinates. -/
theorem adjoinPoint_restrict_lastPoint {n p : ℕ} (Q : PointCoordinates K n (p + 1)) :
    adjoinPoint (restrictPoints Q Fin.castSucc) (lastPoint Q) = Q := by
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [restrictPoints, lastPoint]

variable [Field K]

/-- Lift a condition on the first `p` points to the whole configuration. -/
def liftPrefix {n p : ℕ} (E : MvPolynomial (Fin p × Fin n) K) :
    MvPolynomial (Fin (p + 1) × Fin n) K :=
  rename (fun ij => (ij.1.castSucc, ij.2)) E

/-- Lift a condition on the final point to the whole configuration. -/
def liftLast {n p : ℕ} (F : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (p + 1) × Fin n) K :=
  rename (fun j => (Fin.last p, j)) F

@[simp] theorem eval_liftPrefix {n p : ℕ}
    (Q : PointCoordinates K n (p + 1)) (E : MvPolynomial (Fin p × Fin n) K) :
    eval Q (liftPrefix E) = eval (restrictPoints Q Fin.castSucc) E := by
  rw [liftPrefix, eval_rename]
  rfl

@[simp] theorem eval_liftLast {n p : ℕ}
    (Q : PointCoordinates K n (p + 1)) (F : MvPolynomial (Fin n) K) :
    eval Q (liftLast F) = eval (lastPoint Q) F := by
  rw [liftLast, eval_rename]
  rfl

/-- Three independently witnessed open conditions on these three parameter spaces meet. -/
theorem exists_joint_trace_choice [Infinite K] {n p : ℕ}
    (D : MvPolynomial (Fin (p + 1) × Fin n) K)
    (E : MvPolynomial (Fin p × Fin n) K) (F : MvPolynomial (Fin n) K)
    (hD : ∃ Q : PointCoordinates K n (p + 1), eval Q D ≠ 0)
    (hE : ∃ P : PointCoordinates K n p, eval P E ≠ 0)
    (hF : ∃ y : Fin n → K, eval y F ≠ 0) :
    ∃ Q : PointCoordinates K n (p + 1), eval Q D ≠ 0 ∧
      eval (restrictPoints Q Fin.castSucc) E ≠ 0 ∧ eval (lastPoint Q) F ≠ 0 := by
  obtain ⟨P, hP⟩ := hE
  obtain ⟨y, hy⟩ := hF
  have hEF : ∃ Q : PointCoordinates K n (p + 1),
      eval Q (liftPrefix E * liftLast F) ≠ 0 := by
    refine ⟨adjoinPoint P y, ?_⟩
    simpa only [map_mul, eval_liftPrefix, eval_liftLast, restrict_adjoinPoint,
      lastPoint_adjoinPoint] using mul_ne_zero hP hy
  obtain ⟨Q, hQD, hQEF⟩ := principal_opens_meet D (liftPrefix E * liftLast F) hD hEF
  refine ⟨Q, hQD, ?_⟩
  simpa only [map_mul, eval_liftPrefix, eval_liftLast, mul_ne_zero_iff] using hQEF

/-- A nonzero last-point polynomial suffices over an infinite field. -/
theorem exists_joint_trace_choice_of_ne_zero [Infinite K] {n p : ℕ}
    (D : MvPolynomial (Fin (p + 1) × Fin n) K)
    (E : MvPolynomial (Fin p × Fin n) K) (F : MvPolynomial (Fin n) K)
    (hD : ∃ Q : PointCoordinates K n (p + 1), eval Q D ≠ 0)
    (hE : ∃ P : PointCoordinates K n p, eval P E ≠ 0) (hF : F ≠ 0) :
    ∃ Q : PointCoordinates K n (p + 1), eval Q D ≠ 0 ∧
      eval (restrictPoints Q Fin.castSucc) E ≠ 0 ∧ eval (lastPoint Q) F ≠ 0 := by
  apply exists_joint_trace_choice D E F hD hE
  by_contra! h
  exact hF (MvPolynomial.funext h)

/-- The same choice expressed as a prefix configuration and its final point. -/
theorem exists_prefix_and_point [Infinite K] {n p : ℕ}
    (D : MvPolynomial (Fin (p + 1) × Fin n) K)
    (E : MvPolynomial (Fin p × Fin n) K) (F : MvPolynomial (Fin n) K)
    (hD : ∃ Q : PointCoordinates K n (p + 1), eval Q D ≠ 0)
    (hE : ∃ P : PointCoordinates K n p, eval P E ≠ 0) (hF : F ≠ 0) :
    ∃ (P : PointCoordinates K n p) (y : Fin n → K),
      eval (adjoinPoint P y) D ≠ 0 ∧ eval P E ≠ 0 ∧ eval y F ≠ 0 := by
  obtain ⟨Q, hQD, hQE, hQF⟩ := exists_joint_trace_choice_of_ne_zero D E F hD hE hF
  exact ⟨restrictPoints Q Fin.castSucc, lastPoint Q,
    by rwa [adjoinPoint_restrict_lastPoint], hQE, hQF⟩

end IdealGeneration.FractionalTraceChoice
