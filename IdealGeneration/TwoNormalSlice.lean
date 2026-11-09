module

public import IdealGeneration.HyperplaneEuler
public import IdealGeneration.ScalarProductTrace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Euler interpolation on one slice of a two-normal configuration

The slice has normal coordinate `s = x₀`. Its residual points have nonzero
`s`, and its trace points are embedded by prepending a zero coordinate.
The scalar quotient in the normal trace is the actual tangential product
space of the residual point ideal.
-/

noncomputable section
namespace IdealGeneration.TwoNormalSlice
open MvPolynomial Module

set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {m p q : ℕ}

/-- Evaluate homogeneous forms at chosen homogeneous representatives. -/
def scalarEvaluation {n r : ℕ} (z : Fin r → Fin n → K) (d : ℕ) :
    Forms K n d →ₗ[K] (Fin r → K) :=
  LinearMap.pi fun i => evaluationLinear K n d (z i)

@[simp] theorem scalarEvaluation_apply {n r d : ℕ}
    (z : Fin r → Fin n → K) (f : Forms K n d) (i : Fin r) :
    scalarEvaluation z d f i = eval (z i) f.val := rfl

/-- Evaluate every polynomial component of an Euler relation. -/
def relationEvaluation {n r : ℕ} (z : Fin r → Fin n → K) (d : ℕ) :
    HyperplaneEuler.Relations K n d →ₗ[K] (Fin r → Fin n → K) where
  toFun f i j := eval (z i) (f.val j).val
  map_add' f g := by ext i j; simp
  map_smul' c f := by ext i j; simp

@[simp] theorem relationEvaluation_apply {n r d : ℕ}
    (z : Fin r → Fin n → K) (f : HyperplaneEuler.Relations K n d)
    (i : Fin r) (j : Fin n) :
    relationEvaluation z d f i j = eval (z i) (f.val j).val := rfl

/-- Evaluation on the residual and trace groups in the slice. -/
def sliceEvaluation (a : PointCoordinates K m p) (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 1) d →ₗ[K]
      ((Fin p → Fin (m + 1) → K) × (Fin q → Fin (m + 1) → K)) :=
  (relationEvaluation (fun i => chartPoint K a i) d).prod
    (relationEvaluation (fun i => Fin.cons 0 (z i)) d)

/-- A slice-kernel section vanishes if the Euler trace is injective, the
scalar product code separates its image, and residual multiplication is
injective. This is the slice injection used in Proposition 4.5. -/
theorem eq_zero_of_sliceEvaluation_eq_zero (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Injective (relationEvaluation z (d + 1)))
    (hmul : Function.Injective (pointMultiplication a d))
    (hscalar : Function.Injective ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype))
    (F : HyperplaneEuler.Relations K (m + 1) (d + 1))
    (hF : sliceEvaluation a z (d + 1) F = 0) : F = 0 := by
  have hA : relationEvaluation (fun i => chartPoint K a i) (d + 1) F = 0 :=
    congrArg Prod.fst hF
  have hZ : relationEvaluation (fun i => Fin.cons 0 (z i)) (d + 1) F = 0 :=
    congrArg Prod.snd hF
  have hTraceEval : relationEvaluation z (d + 1)
      (HyperplaneEuler.trace K m (d + 1) F) = 0 := by
    funext i j
    have hj := congrFun (congrFun hZ i) j.succ
    change eval (z i) (hyperplaneRestrict K m (F.val j.succ).val) = 0
    rw [eval_hyperplaneRestrict]
    exact hj
  have hTrace : HyperplaneEuler.trace K m (d + 1) F = 0 :=
    htrace (by simpa using hTraceEval)
  obtain ⟨g, hg⟩ := HyperplaneEuler.exists_normal_of_trace_eq_zero K m d F hTrace
  rw [← hg] at hA hZ
  have hgi (j : Fin m) : g j ∈ pointDegreePiece K a d := by
    rw [mem_pointDegreePiece]
    intro i
    have hj := congrFun (congrFun hA i) j.succ
    change eval (chartPoint K a i) (X 0 * (g j).val) = 0 at hj
    rw [map_mul, eval_X] at hj
    exact (mul_eq_zero.mp hj).resolve_left (hnormal i)
  let w : Fin m → pointPolynomialPiece a d :=
    fun j => pointPolynomialPieceEquiv a d ⟨g j, hgi j⟩
  let u : (tangentPointProductForm a d).range :=
    ⟨tangentPointProductForm a d w, ⟨w, rfl⟩⟩
  have huEval : ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype) u = 0 := by
    funext i
    have hi := congrFun (congrFun hZ i) 0
    change eval (Fin.cons 0 (z i))
      (-(HyperplaneEuler.tangentProduct K m d g).val) = 0 at hi
    rw [map_neg, neg_eq_zero] at hi
    change eval (z i) (tangentPointProduct a d w) = 0
    have heq : eval (z i) (tangentPointProduct a d w) =
        eval (Fin.cons 0 (z i)) (HyperplaneEuler.tangentProduct K m d g).val := by
      simp [tangentPointProduct, HyperplaneEuler.tangentProduct,
        eval_hyperplaneRestrict, w]
    exact heq.trans hi
  have hu : u = 0 := hscalar (by simpa using huEval)
  have huw : tangentPointProductForm a d w = 0 :=
    congrArg Subtype.val hu
  have hw : w = 0 := tangentPointProductForm_injective a hnormal hmul
    (by simpa using huw)
  have hgzero : g = 0 := by
    funext j
    apply Subtype.ext
    have hj := congrArg (fun v : Fin m → pointPolynomialPiece a d => (v j).val) hw
    simpa [w] using hj
  rw [← hg, hgzero, map_zero]

/-- The actual evaluation map on the union of residual and trace points in
one slice is injective under the three interpolation hypotheses. -/
theorem sliceEvaluation_injective (a : PointCoordinates K m p)
    (z : Fin q → Fin m → K) (d : ℕ)
    (hnormal : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (htrace : Function.Injective (relationEvaluation z (d + 1)))
    (hmul : Function.Injective (pointMultiplication a d))
    (hscalar : Function.Injective ((scalarEvaluation z (d + 1)).comp
      (tangentPointProductForm a d).range.subtype)) :
    Function.Injective (sliceEvaluation a z (d + 1)) := by
  intro F G hFG
  apply sub_eq_zero.mp
  apply eq_zero_of_sliceEvaluation_eq_zero a z d hnormal htrace hmul hscalar
  calc
    sliceEvaluation a z (d + 1) (F - G) =
        sliceEvaluation a z (d + 1) F - sliceEvaluation a z (d + 1) G :=
      map_sub (sliceEvaluation a z (d + 1)) F G
    _ = 0 := sub_eq_zero.mpr hFG

end IdealGeneration.TwoNormalSlice
