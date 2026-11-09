module

public import IdealGeneration.TwoNormalFractionalKernel
public import IdealGeneration.TwoNormalFractionalSurjection
public import IdealGeneration.TwoNormalAmbientComparison
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimension of the fractional ambient Euler kernel

Restriction to the common trace is a surjection on the ambient kernel, since
the normal part can compensate all values off the slices. Its kernel is the
actual residual pair kernel, giving the sum of the two dimensions.
-/

noncomputable section
namespace IdealGeneration.TwoNormalFractional
open MvPolynomial Module TwoNormalTrace TwoNormalSlice
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m d p r q k : ℕ}

/-- Restrict the ambient kernel to the trace kernel. -/
def ambientKernelToTraceKernel
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K) (D : ℕ) :
    (ambientEvaluation K m a b x z D).ker →ₗ[K] (traceFiberEvaluation z D).ker :=
  ((ambientTraceRelation K m D).comp (ambientEvaluation K m a b x z D).ker.subtype)
    |>.codRestrict _ (fun f => by
      apply Subtype.ext
      exact trace_vanishing_of_slice_vanishing b z (sliceBRelation K m D f.val)
        (slice_evaluations_zero_of_ambient_eq_zero a b x z f.val f.property).2)

/-- The zero-trace part of the fractional ambient kernel is the residual pair kernel. -/
def residualPairToZeroTraceKernelEquiv
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0) :
    (pairEvaluation K m a b x d).ker ≃ₗ[K]
      (ambientKernelToTraceKernel a b x z (d + 1 + 1)).ker := by
  let D := d + 1 + 1
  let G := ambientKernelToTraceKernel a b x z D
  let E := pairKernelToAmbientKernel K m (d := d) a b x z hc.normalA hc.normalB
  have hGE (w : (pairEvaluation K m a b x d).ker) : G (E w) = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change restrictTrace K m
      (X 0 * (X (0 : Fin (m + 1)).succ * ((w.val.1 j).val).val)) = 0
    simp
  let L : (pairEvaluation K m a b x d).ker →ₗ[K] G.ker := E.codRestrict _ hGE
  apply LinearEquiv.ofBijective L
  constructor
  · intro u v h
    apply Subtype.ext
    apply parameterEuler_injective K m x
    exact congrArg (fun w : G.ker => w.val.val) h
  · intro f
    have hf := LinearMap.mem_ker.mp f.val.property
    have hτ : ambientTraceRelation K m D f.val.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp f.property)
    obtain ⟨_, w, hw, _, _⟩ :=
      exists_assembledRelation_of_ambient_eq_zero a b x z hc f.val.val hf
    change assembledRelation (ambientTraceRelation K m D f.val.val) w = f.val.val at hw
    rw [hτ] at hw
    have hw' : residualEuler K m d w = f.val.val := by
      simpa [assembledRelation] using hw
    have hcoeff (i : Fin q) :=
      (residualEuler_vanishing_iff K m d w (chartPoint K x i) (hxs i) (hxt i)).mp
        (by
          intro j
          rw [hw']
          exact congrFun (congrFun (congrArg (fun v => v.2.1) hf) i) j)
    let v : ResidualParameters K m x d :=
      (fun j => ⟨w.1 j, (mem_pointDegreePiece x (w.1 j)).mpr fun i => (hcoeff i).1 j⟩,
        ⟨w.2, (mem_pointDegreePiece x w.2).mpr fun i => (hcoeff i).2⟩)
    have hv : parameterEuler K m x d v = f.val.val := hw'
    have hvker : pairEvaluation K m a b x d v = 0 := by
      apply (parameterEuler_ambient_eq_zero_iff K m a b x z hc.normalA hc.normalB v).mp
      rw [hv]
      exact hf
    exact ⟨⟨v, hvker⟩, Subtype.ext (Subtype.ext hv)⟩

/-- Compensation at the off-slice points makes ambient trace restriction onto. -/
theorem ambientKernelToTraceKernel_surjective
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d)
    (hX : Function.Surjective (normalFiberEvaluation K m a b x d)) :
    Function.Surjective (ambientKernelToTraceKernel a b x z (d + 1 + 1)) := by
  let D := d + 1 + 1
  intro τ
  have hτ : relationEvaluation z D τ.val = 0 := congrArg Subtype.val τ.property
  let ext := extendTraceRelation K m D τ.val
  let evX := traceFiberEvaluation (fun i => chartPoint K x i) D
  obtain ⟨w, hw⟩ := hX (evX ext)
  let f := ext + (-1 : K) • residualEuler K m d w.val
  have hXval : evX f = 0 := by
    have hw' : evX (residualEuler K m d w.val) = evX ext := hw
    change evX (ext + (-1 : K) • residualEuler K m d w.val) = 0
    rw [map_add, map_smul, hw']
    apply Subtype.ext
    funext i j
    change (evX ext).val i j + (-1 : K) • (evX ext).val i j = 0
    simp
  have hτA (i : Fin p) (j : Fin (m + 2)) :
      eval (sliceARepresentative K m (chartPoint K a i)) (ext.val j).val = 0 :=
    extendTraceRelation_vanishes_at_attached z τ.val hτ
      (sliceARepresentative K m (chartPoint K a i)) (hc.attachedA i) j
  have hτB (i : Fin r) (j : Fin (m + 2)) :
      eval (Fin.cons 0 (chartPoint K b i)) (ext.val j).val = 0 :=
    extendTraceRelation_vanishes_at_attached z τ.val hτ
      (Fin.cons 0 (chartPoint K b i)) (hc.attachedB i) j
  have hτZ (i : Fin k) (j : Fin (m + 2)) :
      eval (Fin.cons 0 (Fin.cons 0 (z i))) (ext.val j).val = 0 :=
    extendTraceRelation_vanishes_at_attached z τ.val hτ _ ⟨i, rfl⟩ j
  obtain ⟨hwA, hwB⟩ := residualEuler_slice_vanishing K m a b d w.val w.property
  have hf : ambientEvaluation K m a b x z D f = 0 := by
    apply Prod.ext <;> apply Prod.ext
    · funext i j
      change eval (sliceARepresentative K m (chartPoint K a i))
        ((ext.val j).val + (-1 : K) • ((residualEuler K m d w.val).val j).val) = 0
      rw [map_add, smul_eq_C_mul, map_mul, hτA i j, hwA i j, mul_zero, add_zero]
    · funext i j
      change eval (Fin.cons 0 (chartPoint K b i))
        ((ext.val j).val + (-1 : K) • ((residualEuler K m d w.val).val j).val) = 0
      rw [map_add, smul_eq_C_mul, map_mul, hτB i j, hwB i j, mul_zero, add_zero]
    · exact congrArg Subtype.val hXval
    · funext i j
      change eval (Fin.cons 0 (Fin.cons 0 (z i)))
        ((ext.val j).val + (-1 : K) • ((residualEuler K m d w.val).val j).val) = 0
      rw [map_add, smul_eq_C_mul, map_mul, hτZ i j,
        residualEuler_trace_vanishing K m z d w.val i j, mul_zero, add_zero]
  refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
  change ambientTraceRelation K m D f = τ.val
  have hnormal : ambientTraceRelation K m D (residualEuler K m d w.val) = 0 := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change restrictTrace K m (X 0 * (X (0 : Fin (m + 1)).succ * (w.val.1 j).val)) = 0
    simp
  change ambientTraceRelation K m D (ext + (-1 : K) • residualEuler K m d w.val) = τ.val
  rw [map_add, map_smul, hnormal, smul_zero, add_zero,
    show ext = extendTraceRelation K m D τ.val from rfl, ambientTraceRelation_extend]

/-- The full fractional kernel has dimension equal to the trace and residual
kernel dimensions added together. -/
theorem finrank_fractional_ambientKernel
    (a : PointCoordinates K m p) (b : PointCoordinates K m r)
    (x : PointCoordinates K (m + 1) q) (z : Fin k → Fin m → K)
    (hc : SliceConditions a b z d)
    (hxs : ∀ i, chartPoint K x i (0 : Fin (m + 2)) ≠ 0)
    (hxt : ∀ i, chartPoint K x i (0 : Fin (m + 1)).succ ≠ 0)
    (hX : Function.Surjective (normalFiberEvaluation K m a b x d)) :
    finrank K (ambientFiberEvaluation a b z (chartPoint K x) (d + 1 + 1)).ker =
      finrank K (traceFiberEvaluation z (d + 1 + 1)).ker +
        finrank K (pairEvaluation K m a b x d).ker := by
  rw [← ambientEvaluation_ker_eq_fiber K m a b x z]
  let G := ambientKernelToTraceKernel a b x z (d + 1 + 1)
  have h := TwoGroup.rank_nullity_monoid G
  rw [LinearMap.range_eq_top.mpr (ambientKernelToTraceKernel_surjective a b x z hc hX),
    finrank_top, ← (residualPairToZeroTraceKernelEquiv a b x z hc hxs hxt).finrank_eq] at h
  exact h.symm

end IdealGeneration.TwoNormalFractional
