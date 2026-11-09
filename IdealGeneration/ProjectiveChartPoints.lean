module

public import IdealGeneration.Points
public import Mathlib.LinearAlgebra.Projectivization.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The standard affine chart in Mathlib's projective space. -/

namespace IdealGeneration

open MvPolynomial

variable {K : Type*} [Field K] {n p d : ℕ}

private theorem snoc_one_ne_zero (u : Fin n → K) : (Fin.snoc u 1 : Fin (n + 1) → K) ≠ 0 := by
  intro h
  have he := congrFun h (Fin.last n)
  simp at he

/-- The projective point represented by a chart coordinate with final coordinate one. -/
def projectiveChartPoint (u : Fin n → K) : Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Fin.snoc u 1) (snoc_one_ne_zero u)

/-- Normalization at the final coordinate makes the affine chart injective. -/
theorem projectiveChartPoint_injective : Function.Injective (projectiveChartPoint (K := K) (n := n)) := by
  intro u v h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hc₁ : c = 1 := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc (Fin.last n)
  rw [hc₁, one_smul] at hc
  funext i
  simpa using congrFun hc.symm i.castSucc

/-- The chart consists of the projective points with a nonzero final coordinate. -/
theorem mem_range_projectiveChartPoint_iff (q : Projectivization K (Fin (n + 1) → K)) :
    q ∈ Set.range projectiveChartPoint ↔ q.rep (Fin.last n) ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    let x := projectiveChartPoint u
    have h : Projectivization.mk K x.rep x.rep_nonzero =
        Projectivization.mk K (Fin.snoc u 1) (snoc_one_ne_zero u) := x.mk_rep
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
    have hn : c ≠ 0 := by
      intro hz
      apply x.rep_nonzero
      simpa [hz] using hc.symm
    have hlast : c = x.rep (Fin.last n) := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc (Fin.last n)
    exact hlast ▸ hn
  · intro h
    let u : Fin n → K := fun i => q.rep i.castSucc / q.rep (Fin.last n)
    refine ⟨u, ?_⟩
    calc
      projectiveChartPoint u = Projectivization.mk K q.rep q.rep_nonzero := by
        symm
        apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
        refine ⟨q.rep (Fin.last n), ?_⟩
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Pi.smul_apply, smul_eq_mul]
        · simp [Pi.smul_apply, smul_eq_mul, u, mul_div_cancel₀ _ h]
      _ = q := q.mk_rep

/-- The actual projective point family of a chart configuration. -/
def projectivePointFamily (a : PointCoordinates K n p) (i : Fin p) :
    Projectivization K (Fin (n + 1) → K) :=
  projectiveChartPoint (fun j => a (i, j))

/-- Distinctness in the chart is exactly injectivity of the projective point family. -/
theorem distinctPoints_iff_projectivePointFamily_injective (a : PointCoordinates K n p) :
    DistinctPoints K a ↔ Function.Injective (projectivePointFamily a) := by
  constructor
  · intro h i j hij
    exact h (projectiveChartPoint_injective hij)
  · intro h i j hij
    exact h (congrArg projectiveChartPoint hij)

/-- Homogeneous vanishing descends from nonzero vectors to their projective classes. -/
def projectiveVanishes (f : Forms K (n + 1) d) :
    Projectivization K (Fin (n + 1) → K) → Prop :=
  Projectivization.lift (fun v => eval v.val f.val = 0) (by
    intro v w c he
    have hc : c ≠ 0 := by
      intro hz
      apply v.property
      simpa [hz] using he
    apply propext
    rw [he]
    exact homogeneous_eval_scale_eq_zero_iff f.property w.val hc)

@[simp] theorem projectiveVanishes_mk (f : Forms K (n + 1) d) (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    projectiveVanishes f (Projectivization.mk K v hv) ↔ eval v f.val = 0 := Iff.rfl

@[simp] theorem projectiveVanishes_projectivePointFamily (a : PointCoordinates K n p)
    (f : Forms K (n + 1) d) (i : Fin p) :
    projectiveVanishes f (projectivePointFamily a i) ↔ eval (chartPoint K a i) f.val = 0 := Iff.rfl

/-- A homogeneous equation belongs to the point ideal exactly when it vanishes on the
actual projective family. -/
theorem homogeneous_mem_pointIdeal_iff_projectiveVanishes (a : PointCoordinates K n p)
    (f : Forms K (n + 1) d) :
    f.val ∈ pointIdeal K a ↔ ∀ i, projectiveVanishes f (projectivePointFamily a i) := by
  simp only [homogeneous_mem_pointIdeal_iff, mem_pointDegreePiece, projectiveVanishes_projectivePointFamily]

end IdealGeneration
