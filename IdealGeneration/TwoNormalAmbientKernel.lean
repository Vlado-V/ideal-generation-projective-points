module

public import IdealGeneration.TwoNormalKernel
public import IdealGeneration.TwoNormalSlice

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The ambient Euler kernel and the residual pair kernel

The four groups are the points on each slice, the off-slice points, and the
common trace. The evaluation maps use their actual homogeneous representatives.
-/

noncomputable section
namespace IdealGeneration.TwoNormalTrace
open MvPolynomial Module
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] (m : ℕ)

abbrev ResidualParameters {s : ℕ} (x : PointCoordinates K (m + 1) s) (d : ℕ) :=
  (Fin m → pointDegreePiece K x d) × pointDegreePiece K x (d + 1)

/-- Forget ideal membership in the residual coefficient parameters. -/
def parameterLift {s : ℕ} (x : PointCoordinates K (m + 1) s) (d : ℕ) :
    ResidualParameters K m x d →ₗ[K]
      ((Fin m → Forms K (m + 2) d) × Forms K (m + 2) (d + 1)) :=
  (LinearMap.pi (fun i => (pointDegreePiece K x d).subtype.comp (LinearMap.proj i))).prodMap
    (pointDegreePiece K x (d + 1)).subtype

/-- The residual Euler relation with its coefficients in the off-slice ideal. -/
def parameterEuler {s : ℕ} (x : PointCoordinates K (m + 1) s) (d : ℕ) :
    ResidualParameters K m x d →ₗ[K] HyperplaneEuler.Relations K (m + 2) (d + 1 + 1) :=
  (residualEuler K m d).comp (parameterLift K m x d)

/-- Impose the two residual groups on the scalar pair (4.8). -/
def pairEvaluation {p r s : ℕ} (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (d : ℕ) :
    ResidualParameters K m x d →ₗ[K] ((Fin p → K) × (Fin r → K)) :=
  ((pointEvaluation K a (d + 1)).prodMap (pointEvaluation K b (d + 1))).comp
    (residualPair K m x)

/-- Actual Euler component evaluation on the four marked point groups. -/
def ambientEvaluation {p r s q : ℕ} (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K) (d : ℕ) :
    HyperplaneEuler.Relations K (m + 2) d →ₗ[K]
      (((Fin p → Fin (m + 2) → K) × (Fin r → Fin (m + 2) → K)) ×
        ((Fin s → Fin (m + 2) → K) × (Fin q → Fin (m + 2) → K))) :=
  ((TwoNormalSlice.relationEvaluation
      (fun i => sliceARepresentative K m (chartPoint K a i)) d).prod
    (TwoNormalSlice.relationEvaluation (fun i => Fin.cons 0 (chartPoint K b i)) d)).prod
      ((TwoNormalSlice.relationEvaluation (fun i => chartPoint K x i) d).prod
        (TwoNormalSlice.relationEvaluation (fun i => Fin.cons 0 (Fin.cons 0 (z i))) d))

/-- Residual Euler parameters vanish at every off-slice and trace point. -/
theorem parameterEuler_off_trace_vanishing {s q d : ℕ}
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (w : ResidualParameters K m x d) :
    (∀ i j, eval (chartPoint K x i) ((parameterEuler K m x d w).val j).val = 0) ∧
      (∀ i j, eval (Fin.cons 0 (Fin.cons 0 (z i))) ((parameterEuler K m x d w).val j).val = 0) := by
  constructor
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · change eval (chartPoint K x i) (X (0 : Fin (m + 1)).succ * w.2.val.val) = 0
      rw [map_mul, (mem_pointDegreePiece x w.2.val).mp w.2.property i, mul_zero]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change eval (chartPoint K x i)
          (X 0 * (-w.2.val.val - ∑ k, X k.succ.succ * (w.1 k).val.val)) = 0
        simp only [map_mul, map_sub, map_neg, map_sum, eval_X]
        rw [(mem_pointDegreePiece x w.2.val).mp w.2.property i]
        have hcoeff (k : Fin m) : eval (chartPoint K x i) (w.1 k).val.val = 0 :=
          (mem_pointDegreePiece x (w.1 k).val).mp (w.1 k).property i
        simp [hcoeff]
      · change eval (chartPoint K x i)
          (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val.val)) = 0
        rw [map_mul, map_mul, (mem_pointDegreePiece x (w.1 j).val).mp (w.1 j).property i,
          mul_zero, mul_zero]
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
        (X (0 : Fin (m + 1)).succ * w.2.val.val) = 0
      simp only [map_mul, eval_X, Fin.cons_succ, Fin.cons_zero, zero_mul]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
          (X 0 * (-w.2.val.val - ∑ k, X k.succ.succ * (w.1 k).val.val)) = 0
        simp
      · change eval (Fin.cons 0 (Fin.cons 0 (z i)))
          (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val.val)) = 0
        simp

/-- On the two slices, the free normal component is precisely the scalar pair. -/
theorem parameterEuler_slice_vanishing_iff {p r s d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (w : ResidualParameters K m x d) :
    ((∀ i j, eval (sliceARepresentative K m (chartPoint K a i))
        ((parameterEuler K m x d w).val j).val = 0) ∧
      (∀ i j, eval (Fin.cons 0 (chartPoint K b i))
        ((parameterEuler K m x d w).val j).val = 0)) ↔
      pairEvaluation K m a b x d w = 0 := by
  let h := w.2.val
  let T := tangentProduct K m d (fun k => (w.1 k).val)
  have hA (i : Fin p) :
      (pairEvaluation K m a b x d w).1 i =
        eval (sliceARepresentative K m (chartPoint K a i)) (h.val + T.val) :=
    eval_restrictA K m (chartPoint K a i) (h.val + T.val)
  have hB (i : Fin r) :
      (pairEvaluation K m a b x d w).2 i =
        eval (Fin.cons 0 (chartPoint K b i)) h.val :=
    eval_hyperplaneRestrict K (m + 1) h.val (chartPoint K b i)
  constructor
  · rintro ⟨hva, hvb⟩
    apply Prod.ext
    · funext i
      rw [hA]
      change eval (sliceARepresentative K m (chartPoint K a i)) (h.val + T.val) = (0 : K)
      have hi := hva i (0 : Fin (m + 1)).succ
      change eval (sliceARepresentative K m (chartPoint K a i))
        (X 0 * (-h.val - T.val)) = 0 at hi
      rw [map_mul, eval_X] at hi
      have hneg := (mul_eq_zero.mp hi).resolve_left (ha i)
      rw [map_sub, map_neg] at hneg
      rw [map_add]
      linear_combination -hneg
    · funext i
      rw [hB]
      have hi := hvb i 0
      change eval (Fin.cons 0 (chartPoint K b i))
        (X (0 : Fin (m + 1)).succ * h.val) = 0 at hi
      rw [map_mul, eval_X] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hb i)
  · intro hw
    have hwa (i : Fin p) :
        eval (sliceARepresentative K m (chartPoint K a i)) (h.val + T.val) = 0 := by
      rw [← hA]
      exact congrFun (congrArg Prod.fst hw) i
    have hwb (i : Fin r) : eval (Fin.cons 0 (chartPoint K b i)) h.val = 0 := by
      rw [← hB]
      exact congrFun (congrArg Prod.snd hw) i
    constructor
    · intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · change eval (sliceARepresentative K m (chartPoint K a i))
          (X (0 : Fin (m + 1)).succ * h.val) = 0
        simp only [map_mul, eval_X, sliceARepresentative, Fin.cons_succ, Fin.cons_zero, zero_mul]
      · refine Fin.cases ?_ (fun j => ?_) j
        · change eval (sliceARepresentative K m (chartPoint K a i))
            (X 0 * (-h.val - T.val)) = 0
          rw [map_mul, map_sub, map_neg]
          have hi := hwa i
          rw [map_add] at hi
          have hneg : -eval (sliceARepresentative K m (chartPoint K a i)) h.val -
              eval (sliceARepresentative K m (chartPoint K a i)) T.val = 0 := by
            linear_combination -hi
          rw [hneg, mul_zero]
        · change eval (sliceARepresentative K m (chartPoint K a i))
            (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val.val)) = 0
          simp only [map_mul, eval_X, sliceARepresentative, Fin.cons_succ, Fin.cons_zero,
            zero_mul, mul_zero]
    · intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · change eval (Fin.cons 0 (chartPoint K b i))
          (X (0 : Fin (m + 1)).succ * h.val) = 0
        rw [map_mul, hwb, mul_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · change eval (Fin.cons 0 (chartPoint K b i)) (X 0 * (-h.val - T.val)) = 0
          simp
        · change eval (Fin.cons 0 (chartPoint K b i))
            (X 0 * (X (0 : Fin (m + 1)).succ * (w.1 j).val.val)) = 0
          simp

/-- The four-group vanishing conditions on residual Euler parameters are
exactly the two scalar groups on the residual pair. -/
theorem parameterEuler_ambient_eq_zero_iff {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (w : ResidualParameters K m x d) :
    ambientEvaluation K m a b x z (d + 1 + 1) (parameterEuler K m x d w) = 0 ↔
      pairEvaluation K m a b x d w = 0 := by
  have hoff := parameterEuler_off_trace_vanishing K m (d := d) x z w
  have hslice := parameterEuler_slice_vanishing_iff K m (d := d) a b x ha hb w
  constructor
  · intro h
    apply hslice.mp
    exact ⟨fun i j => congrFun (congrFun (congrArg (fun v => v.1.1) h) i) j,
      fun i j => congrFun (congrFun (congrArg (fun v => v.1.2) h) i) j⟩
  · intro h
    obtain ⟨hA, hB⟩ := hslice.mpr h
    apply Prod.ext
    · apply Prod.ext <;> funext i j
      · exact hA i j
      · exact hB i j
    · apply Prod.ext <;> funext i j
      · exact hoff.1 i j
      · exact hoff.2 i j

/-- Slice injection turns ambient pointwise vanishing into polynomially zero
Euler restrictions on each complete slice. -/
theorem slice_relations_zero_of_ambient_eq_zero {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (hA : Function.Injective (TwoNormalSlice.sliceEvaluation a z d))
    (hB : Function.Injective (TwoNormalSlice.sliceEvaluation b z d))
    (f : HyperplaneEuler.Relations K (m + 2) d)
    (hf : ambientEvaluation K m a b x z d f = 0) :
    sliceARelation K m d f = 0 ∧ sliceBRelation K m d f = 0 := by
  have hAeval (i : Fin p) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.1.1) hf) i) j
  have hBeval (i : Fin r) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.1.2) hf) i) j
  have hZeval (i : Fin q) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun v => v.2.2) hf) i) j
  constructor
  · apply hA
    rw [map_zero]
    apply Prod.ext
    · funext i j
      change eval (chartPoint K a i) ((sliceARelation K m d f).val j).val = 0
      rw [eval_sliceARelation]
      exact hAeval i _
    · funext i j
      change eval (Fin.cons 0 (z i)) ((sliceARelation K m d f).val j).val = 0
      rw [eval_sliceARelation]
      exact hZeval i _
  · apply hB
    rw [map_zero]
    apply Prod.ext
    · funext i j
      change eval (chartPoint K b i) ((sliceBRelation K m d f).val j).val = 0
      rw [eval_sliceBRelation]
      exact hBeval i _
    · funext i j
      change eval (Fin.cons 0 (z i)) ((sliceBRelation K m d f).val j).val = 0
      rw [eval_sliceBRelation]
      exact hZeval i _

/-- Every ambient kernel section comes from residual ideal coefficients
satisfying the two scalar evaluation groups. -/
theorem exists_parameters_of_ambient_eq_zero {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (TwoNormalSlice.sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (TwoNormalSlice.sliceEvaluation b z (d + 1 + 1)))
    (f : HyperplaneEuler.Relations K (m + 2) (d + 1 + 1))
    (hf : ambientEvaluation K m a b x z (d + 1 + 1) f = 0) :
    ∃ w : ResidualParameters K m x d,
      parameterEuler K m x d w = f ∧ pairEvaluation K m a b x d w = 0 := by
  obtain ⟨hfA, hfB⟩ := slice_relations_zero_of_ambient_eq_zero K m a b x z hA hB f hf
  obtain ⟨v, hv⟩ := exists_residualEuler_of_slice_relations_zero K m d f hfA hfB
  have hx (i : Fin s) (j : Fin (m + 2)) :=
    congrFun (congrFun (congrArg (fun w => w.2.1) hf) i) j
  have hcoeff (i : Fin s) :=
    (residualEuler_vanishing_iff K m d v (chartPoint K x i) (hxs i) (hxt i)).mp
      (by
        intro j
        rw [hv]
        have hij := hx i j
        change eval (chartPoint K x i) (f.val j).val = (0 : K) at hij
        exact hij)
  have hmemA (j : Fin m) : v.1 j ∈ pointDegreePiece K x d := by
    rw [mem_pointDegreePiece]
    exact fun i => (hcoeff i).1 j
  have hmemH : v.2 ∈ pointDegreePiece K x (d + 1) := by
    rw [mem_pointDegreePiece]
    exact fun i => (hcoeff i).2
  let w : ResidualParameters K m x d := (fun j => ⟨v.1 j, hmemA j⟩, ⟨v.2, hmemH⟩)
  have hw : parameterEuler K m x d w = f := hv
  refine ⟨w, hw, ?_⟩
  apply (parameterEuler_ambient_eq_zero_iff K m (d := d) a b x z ha hb w).mp
  rw [hw]
  exact hf

/-- Residual ideal parameters retain their uniqueness as Euler relations. -/
theorem parameterEuler_injective {s d : ℕ} (x : PointCoordinates K (m + 1) s) :
    Function.Injective (parameterEuler K m x d) := by
  intro v w hvw
  have h := residualEuler_injective K m d hvw
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrFun (congrArg Prod.fst h) i
  · apply Subtype.ext
    exact congrArg Prod.snd h

/-- The residual pair kernel maps into the actual four-group Euler kernel. -/
def pairKernelToAmbientKernel {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0) :
    (pairEvaluation K m a b x d).ker →ₗ[K]
      (ambientEvaluation K m a b x z (d + 1 + 1)).ker :=
  ((parameterEuler K m x d).comp (pairEvaluation K m a b x d).ker.subtype).codRestrict _
    (fun w => (parameterEuler_ambient_eq_zero_iff K m (d := d) a b x z ha hb w.val).mpr w.property)

/-- The normal form identifies the actual ambient evaluation kernel with
the two-group scalar kernel used in Proposition 4.5. -/
def pairAmbientKernelEquiv {p r s q d : ℕ}
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) s) (z : Fin q → Fin m → K)
    (ha : ∀ i, chartPoint K a i (0 : Fin (m + 1)) ≠ 0)
    (hb : ∀ i, chartPoint K b i (0 : Fin (m + 1)) ≠ 0)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hA : Function.Injective (TwoNormalSlice.sliceEvaluation a z (d + 1 + 1)))
    (hB : Function.Injective (TwoNormalSlice.sliceEvaluation b z (d + 1 + 1))) :
    (pairEvaluation K m a b x d).ker ≃ₗ[K]
      (ambientEvaluation K m a b x z (d + 1 + 1)).ker :=
  LinearEquiv.ofBijective (pairKernelToAmbientKernel K m (d := d) a b x z ha hb) (by
    constructor
    · intro v w hvw
      apply Subtype.ext
      exact parameterEuler_injective K m x (congrArg Subtype.val hvw)
    · intro f
      obtain ⟨w, hw, hp⟩ := exists_parameters_of_ambient_eq_zero K m a b x z
        ha hb hxs hxt hA hB f.val f.property
      exact ⟨⟨w, hp⟩, Subtype.ext hw⟩)

end IdealGeneration.TwoNormalTrace
