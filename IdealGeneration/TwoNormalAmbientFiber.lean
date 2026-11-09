module

public import IdealGeneration.TwoNormalCokernelCompatibility

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Lifting compatible slice values to ambient Euler fibers

The two normal coordinates come first. Slice A lies in `t = 0`, slice B
lies in `s = 0`, and their trace lies in `s = t = 0`.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial

set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p r q l : ℕ}

/-- The first slice has a free first normal coordinate and zero second normal coordinate. -/
def ambientPointA (a : PointCoordinates K m p) (i : Fin p) : Fin (m + 2) → K :=
  Fin.cons (chartPoint K a i 0) (Fin.cons 0 (fun j : Fin m => chartPoint K a i j.succ))

/-- The second slice has zero first normal coordinate and a free second normal coordinate. -/
def ambientPointB (b : PointCoordinates K m r) (i : Fin r) : Fin (m + 2) → K :=
  Fin.cons 0 (Fin.cons (chartPoint K b i 0) (fun j : Fin m => chartPoint K b i j.succ))

/-- The common trace is embedded by prepending two zero normal coordinates. -/
def ambientTracePoint (z : Fin q → Fin m → K) (i : Fin q) : Fin (m + 2) → K :=
  Fin.cons 0 (Fin.cons 0 (z i))

/-- All ambient Euler fiber values in the two slices, the trace, and the residual group. -/
abbrev AmbientFiberValues (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) :=
  TraceFibers (ambientPointA a) × (TraceFibers (ambientPointB b) ×
    (TraceFibers (ambientTracePoint z) × TraceFibers x))

/-- The ambient fiber on the common trace projects to its tangential Euler fiber. -/
def ambientTraceTangent (z : Fin q → Fin m → K) :
    TraceFibers (ambientTracePoint z) →ₗ[K] TraceFibers z where
  toFun u := ⟨fun i j => u.val i j.succ.succ, by
    funext i
    have hi := congrFun (LinearMap.mem_ker.mp u.property) i
    change (∑ j, ambientTracePoint z i j * u.val i j) = 0 at hi
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hi
    change (∑ j, z i j * u.val i j.succ.succ) = 0
    simpa only [ambientTracePoint, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
      using hi⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Retain the slice tangent values, the common tangential trace, and both
normal values on the trace. The extra residual group contributes no slice values. -/
def ambientFiberProjection (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (z : Fin q → Fin m → K) (x : Fin l → Fin (m + 2) → K) :
    AmbientFiberValues a b z x →ₗ[K] CompatibleSliceValues z p r where
  toFun u := (ambientTraceTangent z u.2.2.1,
    (((fun i j => u.1.val i j.succ.succ), fun i => u.2.2.1.val i 0),
      ((fun i j => u.2.1.val i j.succ.succ),
        fun i => u.2.2.1.val i (0 : Fin (m + 1)).succ)))
  map_add' _ _ := Prod.ext ((ambientTraceTangent z).map_add _ _) rfl
  map_smul' c _ := Prod.ext ((ambientTraceTangent z).map_smul c _) rfl

/-- Every compatible pair of slice values lifts to actual ambient Euler
fiber values. The nonzero slice heights solve the omitted normal components. -/
theorem ambientFiberProjection_surjective (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0) :
    Function.Surjective (ambientFiberProjection a b z x) := by
  intro c
  let uA : TraceFibers (ambientPointA a) :=
    ⟨fun i => Fin.cons
      (-(∑ j, chartPoint K a i j.succ * c.2.1.1 i j) / chartPoint K a i 0)
      (Fin.cons 0 (c.2.1.1 i)), by
      funext i
      change (∑ j, ambientPointA a i j * (Fin.cons (α := fun _ : Fin (m + 2) => K)
        (-(∑ k, chartPoint K a i k.succ * c.2.1.1 i k) / chartPoint K a i 0)
        (Fin.cons (α := fun _ : Fin (m + 1) => K) 0 (c.2.1.1 i))) j) = 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [ambientPointA, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
      field_simp [hA i]
      ring⟩
  let uB : TraceFibers (ambientPointB b) :=
    ⟨fun i => Fin.cons 0 (Fin.cons
      (-(∑ j, chartPoint K b i j.succ * c.2.2.1 i j) / chartPoint K b i 0)
      (c.2.2.1 i)), by
      funext i
      change (∑ j, ambientPointB b i j * (Fin.cons (α := fun _ : Fin (m + 2) => K) 0
        (Fin.cons (α := fun _ : Fin (m + 1) => K)
        (-(∑ k, chartPoint K b i k.succ * c.2.2.1 i k) / chartPoint K b i 0)
        (c.2.2.1 i))) j) = 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [ambientPointB, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
      field_simp [hB i]
      ring⟩
  let uZ : TraceFibers (ambientTracePoint z) :=
    ⟨fun i => Fin.cons (c.2.1.2 i) (Fin.cons (c.2.2.2 i) (c.1.val i)), by
      funext i
      change (∑ j, ambientTracePoint z i j *
        (Fin.cons (α := fun _ : Fin (m + 2) => K) (c.2.1.2 i)
          (Fin.cons (α := fun _ : Fin (m + 1) => K) (c.2.2.2 i) (c.1.val i))) j) = 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [ambientTracePoint, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
      exact congrFun (LinearMap.mem_ker.mp c.1.property) i⟩
  refine ⟨(uA, uB, uZ, 0), ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext i j
    simp [ambientFiberProjection, ambientTraceTangent, uZ]
  · apply Prod.ext
    · apply Prod.ext
      · funext i j
        simp [ambientFiberProjection, uA]
      · funext i
        simp [ambientFiberProjection, uZ]
    · apply Prod.ext
      · funext i j
        simp [ambientFiberProjection, uB]
      · funext i
        simp [ambientFiberProjection, uZ]

/-- The ambient fiber target maps to the two actual slice cokernels. -/
def ambientFiberCokernelClasses (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ) :=
  (compatibleCokernelClasses a b z d).comp (ambientFiberProjection a b z x)

/-- Both slice cokernel classes can be realized by ambient Euler fiber values. -/
theorem ambientFiberCokernelClasses_surjective (a : PointCoordinates K m p)
    (b : PointCoordinates K m r) (z : Fin q → Fin m → K)
    (x : Fin l → Fin (m + 2) → K) (d : ℕ)
    (hA : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hB : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Surjective (traceFiberEvaluation z d)) :
    Function.Surjective (ambientFiberCokernelClasses a b z x d) :=
  (compatibleCokernelClasses_surjective a b z d htrace).comp
    (ambientFiberProjection_surjective a b z x hA hB)

end IdealGeneration.TwoNormalSlice
