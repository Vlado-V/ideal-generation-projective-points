module

public import IdealGeneration.Euler
public import IdealGeneration.HyperplaneEulerScalar
public import IdealGeneration.Rank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Removing the scalar trace

A commutative evaluation square whose scalar quotient is an isomorphism
has the same kernel and cokernel as evaluation on the scalar-trace kernel.
The second part applies this cancellation to the polynomial sequence (3.2)
and to full, scalar, and partial point conditions.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace IdealGeneration
namespace LinearSquare

variable {K E T C Q : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
  [AddCommGroup C] [Module K C] [AddCommGroup Q] [Module K Q]
  (s : LinearSquare K E T C Q)

/-- If the scalar quotient is injective, every zero of evaluation already
belongs to the scalar-trace kernel. -/
def scalarReductionKernelEquiv (hinj : Function.Injective s.right) :
    s.left.ker ≃ₗ[K] s.leftOnKernel.ker where
  toFun x := ⟨⟨x.val, by
    apply hinj
    rw [s.commutes, x.property, map_zero, map_zero]⟩, by
    apply Subtype.ext
    exact x.property⟩
  invFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Inclusion of the lower kernel induces the comparison on cokernels. -/
def scalarReductionCokernelMap :
    (s.bottom.ker ⧸ s.leftOnKernel.range) →ₗ[K] (C ⧸ s.left.range) :=
  s.leftOnKernel.range.liftQ
    (s.left.range.mkQ.comp s.bottom.ker.subtype) (by
      rintro _ ⟨x, rfl⟩
      change s.left.range.mkQ (s.left x.val) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x.val, rfl⟩)

@[simp] theorem scalarReductionCokernelMap_mk (x : s.bottom.ker) :
    s.scalarReductionCokernelMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x.val := rfl

/-- An injective scalar quotient makes the cokernel comparison injective. -/
theorem scalarReductionCokernelMap_injective (hinj : Function.Injective s.right) :
    Function.Injective s.scalarReductionCokernelMap := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change s.left.range.mkQ x.val = 0 at hx
  obtain ⟨e, he⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
  have ht : s.top e = 0 := by
    apply hinj
    rw [s.commutes, he, x.property, map_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨⟨e, ht⟩, Subtype.ext he⟩

/-- Surjectivity of the top and scalar quotient maps makes the comparison onto. -/
theorem scalarReductionCokernelMap_surjective
    (htop : Function.Surjective s.top) (hright : Function.Surjective s.right) :
    Function.Surjective s.scalarReductionCokernelMap := by
  intro z
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨t, ht⟩ := hright (s.bottom c)
  obtain ⟨e, he⟩ := htop t
  have hx : s.bottom (c - s.left e) = 0 := by
    rw [map_sub, ← s.commutes, he, ht, sub_self]
  refine ⟨Submodule.Quotient.mk (⟨c - s.left e, hx⟩ : s.bottom.ker), ?_⟩
  change s.left.range.mkQ (c - s.left e) = s.left.range.mkQ c
  rw [map_sub]
  have hz : s.left.range.mkQ (s.left e) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨e, rfl⟩
  rw [hz, sub_zero]

/-- Cancelling an isomorphic scalar quotient preserves the actual cokernel. -/
def scalarReductionCokernelEquiv
    (htop : Function.Surjective s.top) (hright : Function.Bijective s.right) :
    (s.bottom.ker ⧸ s.leftOnKernel.range) ≃ₗ[K] (C ⧸ s.left.range) :=
  LinearEquiv.ofBijective s.scalarReductionCokernelMap
    ⟨s.scalarReductionCokernelMap_injective hright.1,
      s.scalarReductionCokernelMap_surjective htop hright.2⟩

/-- The cokernel of a map into the reduced condition space. -/
abbrev reducedCokernel {R : Type*} [AddCommMonoid R] [Module K R]
    (f : R →ₗ[K] s.bottom.ker) := s.bottom.ker ⧸ f.range

/-- The cokernel comparison is unchanged by a parametrization with the
same reduced image. -/
def scalarReductionCokernelEquivOfRange {R : Type*} [AddCommMonoid R] [Module K R]
    (f : R →ₗ[K] s.bottom.ker) (hf : f.range = s.leftOnKernel.range)
    (htop : Function.Surjective s.top) (hright : Function.Bijective s.right) :
    s.reducedCokernel f ≃ₗ[K] (C ⧸ s.left.range) :=
  (Submodule.quotEquivOfEq _ _ hf).trans (s.scalarReductionCokernelEquiv htop hright)

/-- Injectivity is unchanged after scalar-trace cancellation. -/
theorem scalarReduction_injective_iff (hinj : Function.Injective s.right) :
    Function.Injective s.left ↔ Function.Injective s.leftOnKernel := by
  constructor
  · intro h x y hxy
    apply Subtype.ext
    apply h
    exact congrArg Subtype.val hxy
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have ht : s.top x = 0 := by
      apply hinj
      rw [s.commutes, hx, map_zero, map_zero]
    have hz : s.leftOnKernel (⟨x, ht⟩ : s.top.ker) = 0 := Subtype.ext hx
    exact congrArg Subtype.val ((map_eq_zero_iff s.leftOnKernel h).mp hz)

/-- Independence of the conditions is unchanged after scalar-trace cancellation. -/
theorem scalarReduction_surjective_iff
    (htop : Function.Surjective s.top) (hright : Function.Bijective s.right) :
    Function.Surjective s.left ↔ Function.Surjective s.leftOnKernel := by
  constructor
  · intro h c
    obtain ⟨e, he⟩ := h c.val
    have ht : s.top e = 0 := by
      apply hright.1
      rw [s.commutes, he, c.property, map_zero]
    exact ⟨⟨e, ht⟩, Subtype.ext he⟩
  · intro h c
    obtain ⟨t, ht⟩ := hright.2 (s.bottom c)
    obtain ⟨e, he⟩ := htop t
    have hx : s.bottom (c - s.left e) = 0 := by
      rw [map_sub, ← s.commutes, he, ht, sub_self]
    obtain ⟨x, hx'⟩ := h ⟨c - s.left e, hx⟩
    refine ⟨e + x.val, ?_⟩
    rw [map_add]
    have hh : s.left x.val = c - s.left e := congrArg Subtype.val hx'
    rw [hh]
    abel

/-- Maximal rank is unchanged by an isomorphic scalar quotient. -/
theorem scalarReduction_maximalRank_iff
    (htop : Function.Surjective s.top) (hright : Function.Bijective s.right) :
    HasMaximalRank s.left ↔ HasMaximalRank s.leftOnKernel := by
  change (Function.Injective s.left ∨ Function.Surjective s.left) ↔
    (Function.Injective s.leftOnKernel ∨ Function.Surjective s.leftOnKernel)
  rw [s.scalarReduction_injective_iff hright.1,
    s.scalarReduction_surjective_iff htop hright]

/-- The removed scalar quotient contributes its dimension to the rank. -/
theorem scalarReduction_rank [FiniteDimensional K E] [FiniteDimensional K T]
    [FiniteDimensional K C] (htop : Function.Surjective s.top)
    (hinj : Function.Injective s.right) :
    Module.finrank K s.left.range =
      Module.finrank K s.leftOnKernel.range + Module.finrank K T := by
  have hk := (s.scalarReductionKernelEquiv hinj).finrank_eq
  have he := s.left.finrank_range_add_finrank_ker
  have hr := s.leftOnKernel.finrank_range_add_finrank_ker
  have ht := s.top.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr htop, finrank_top] at ht
  omega

end LinearSquare

namespace ScalarTraceReduction
open MvPolynomial HyperplaneEulerScalar

variable {K : Type*} [Field K] {n d p q : ℕ}

/-- A tangential value has scalar trace given by its dot product with the point. -/
def pointDot (y : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun v := ∑ j, y j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

/-- The trace fiber at a hyperplane point. -/
abbrev TraceFiber (y : Fin n → K) := (pointDot y).ker

/-- Evaluation of all tangential components at an ambient representative. -/
def tangentEvaluation (x : Fin (n + 1) → K) :
    (Fin n → Forms K (n + 1) d) →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun j => (evaluationLinear K (n + 1) d x).comp (LinearMap.proj j))

/-- Scalar evaluation on the hyperplane. -/
def traceScalarEvaluation (on : Fin q → Fin n → K) :
    Forms K n (d + 1) →ₗ[K] (Fin q → K) :=
  LinearMap.pi (fun i => evaluationLinear K n (d + 1) (on i))

/-- The mixed target has full conditions off the hyperplane and quotient
conditions on it. Taking `L = 0` gives full values, while `L = TraceFiber`
gives scalar values alone. -/
abbrev ConditionSpace (L : Fin q → Submodule K (Fin n → K)) :=
  (Fin p → Fin n → K) × (∀ i, (Fin n → K) ⧸ L i)

/-- Genuine point evaluation for the mixed residual problem. -/
def mixedEvaluation (off : Fin p → Fin (n + 1) → K)
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K)) :
    (Fin n → Forms K (n + 1) d) →ₗ[K] ConditionSpace (p := p) L :=
  (LinearMap.pi (fun i => tangentEvaluation (d := d) (off i))).prod
    (LinearMap.pi (fun i => (L i).mkQ.comp
      (tangentEvaluation (d := d) (Fin.cons 0 (on i)))))

/-- Every allowed hyperplane value lies in the trace fiber, so the scalar
dot product descends to each quotient condition. -/
def conditionScalarProjection (on : Fin q → Fin n → K)
    (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i)) :
    ConditionSpace (p := p) L →ₗ[K] (Fin q → K) where
  toFun c := fun i => (L i).liftQ (pointDot (on i)) (hL i) (c.2 i)
  map_add' c e := by
    ext i
    exact ((L i).liftQ (pointDot (on i)) (hL i)).map_add (c.2 i) (e.2 i)
  map_smul' a c := by
    ext i
    exact ((L i).liftQ (pointDot (on i)) (hL i)).map_smul a (c.2 i)

/-- Polynomial scalar trace commutes with evaluation at every hyperplane point. -/
theorem scalarTrace_evaluation (on : Fin q → Fin n → K)
    (g : Fin n → Forms K (n + 1) d) (i : Fin q) :
    traceScalarEvaluation on (scalarTrace K n d g) i =
      pointDot (on i) (tangentEvaluation (Fin.cons 0 (on i)) g) := by
  change eval (on i) (∑ j, X j * hyperplaneRestrict K n (g j).val) =
    ∑ j, on i j * eval (Fin.cons 0 (on i)) (g j).val
  simp only [map_sum, map_mul, eval_X, eval_hyperplaneRestrict]

/-- The evaluation diagram of sequence (3.2) for all the mixed conditions. -/
def evaluationSquare (off : Fin p → Fin (n + 1) → K)
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i)) :
    LinearSquare K (Fin n → Forms K (n + 1) d) (Forms K n (d + 1))
      (ConditionSpace (p := p) L) (Fin q → K) where
  top := scalarTrace K n d
  left := mixedEvaluation off on L
  right := traceScalarEvaluation on
  bottom := conditionScalarProjection on L hL
  commutes g := by
    ext i
    exact scalarTrace_evaluation on g i

/-- After discarding scalar conditions, the remaining evaluation has values
in the kernel of the scalar condition projection. -/
def relationEvaluation (off : Fin p → Fin (n + 1) → K)
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i)) :
    (formMultiplication K (n + 1) d).ker →ₗ[K]
      (evaluationSquare (d := d) off on L hL).bottom.ker :=
  (evaluationSquare (d := d) off on L hL).leftOnKernel.comp
    (forgetNormalKernelEquiv K n d).toLinearMap

@[simp] theorem relationEvaluation_val
    (off : Fin p → Fin (n + 1) → K) (on : Fin q → Fin n → K)
    (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i))
    (f : (formMultiplication K (n + 1) d).ker) :
    (relationEvaluation off on L hL f).val =
      mixedEvaluation off on L (forgetNormal K n d f) := rfl

/-- Precomposing a linear map by an isomorphism preserves its kernel. -/
def precompKernelEquiv {A B C : Type*} [AddCommMonoid A] [Module K A]
    [AddCommMonoid B] [Module K B] [AddCommMonoid C] [Module K C]
    (e : A ≃ₗ[K] B) (f : B →ₗ[K] C) :
    (f.comp e.toLinearMap).ker ≃ₗ[K] f.ker where
  toFun a := ⟨e a.val, a.property⟩
  invFun b := ⟨e.symm b.val, by
    change f (e (e.symm b.val)) = 0
    rw [e.apply_symm_apply]
    exact b.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)
  map_add' a b := Subtype.ext (e.map_add a.val b.val)
  map_smul' c a := Subtype.ext (e.map_smul c a.val)

variable (off : Fin p → Fin (n + 1) → K) (on : Fin q → Fin n → K)
  (L : Fin q → Submodule K (Fin n → K))
  (hL : ∀ i, L i ≤ TraceFiber (on i))

/-- The kernel statement in Lemma 3.5, with an actual Euler-relation domain. -/
def kernelEquiv (heval : Function.Injective (traceScalarEvaluation (d := d) on)) :
    (mixedEvaluation (d := d) off on L).ker ≃ₗ[K]
      (relationEvaluation (d := d) off on L hL).ker := by
  let e : (relationEvaluation (d := d) off on L hL).ker ≃ₗ[K]
      (evaluationSquare (d := d) off on L hL).leftOnKernel.ker := by
    exact precompKernelEquiv (forgetNormalKernelEquiv K n d) (evaluationSquare (d := d) off on L hL).leftOnKernel
  exact ((evaluationSquare (d := d) off on L hL).scalarReductionKernelEquiv heval).trans
    e.symm

/-- Forgetting the normal component exhausts the same reduced image. -/
theorem relationEvaluation_range :
    (relationEvaluation (d := d) off on L hL).range =
      (evaluationSquare (d := d) off on L hL).leftOnKernel.range := by
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (forgetNormalKernelEquiv K n d).surjective

/-- The cokernel statement in Lemma 3.5. Scalar interpolation is the only
extra hypothesis, in addition to characteristic zero for sequence (3.2). -/
def cokernelEquiv [CharZero K]
    (heval : Function.Bijective (traceScalarEvaluation (d := d) on)) :
    (evaluationSquare (d := d) off on L hL).reducedCokernel
      (relationEvaluation (d := d) off on L hL) ≃ₗ[K]
      (ConditionSpace (p := p) L ⧸ (mixedEvaluation (d := d) off on L).range) :=
  (evaluationSquare (d := d) off on L hL).scalarReductionCokernelEquivOfRange
    (relationEvaluation (d := d) off on L hL) (relationEvaluation_range off on L hL)
    (scalarTrace_surjective K n d) heval

/-- Trivial kernel transfers to and from the relation problem. -/
theorem injective_iff
    (heval : Function.Injective (traceScalarEvaluation (d := d) on)) :
    Function.Injective (mixedEvaluation (d := d) off on L) ↔
      Function.Injective (relationEvaluation (d := d) off on L hL) := by
  change Function.Injective (evaluationSquare (d := d) off on L hL).left ↔ _
  rw [(evaluationSquare (d := d) off on L hL).scalarReduction_injective_iff heval]
  exact ⟨fun h => h.comp (forgetNormalKernelEquiv K n d).injective,
    fun h => (Function.Injective.of_comp_right h
      (forgetNormalKernelEquiv K n d).surjective)⟩

/-- Independence transfers to and from the relation problem. -/
theorem surjective_iff [CharZero K]
    (heval : Function.Bijective (traceScalarEvaluation (d := d) on)) :
    Function.Surjective (mixedEvaluation (d := d) off on L) ↔
      Function.Surjective (relationEvaluation (d := d) off on L hL) := by
  change Function.Surjective (evaluationSquare (d := d) off on L hL).left ↔ _
  rw [(evaluationSquare (d := d) off on L hL).scalarReduction_surjective_iff
    (scalarTrace_surjective K n d) heval]
  exact ⟨fun h => h.comp (forgetNormalKernelEquiv K n d).surjective,
    fun h => Function.Surjective.of_comp h⟩

/-- The two problems in Lemma 3.5 have maximal rank simultaneously. -/
theorem maximalRank_iff [CharZero K]
    (heval : Function.Bijective (traceScalarEvaluation (d := d) on)) :
    HasMaximalRank (mixedEvaluation (d := d) off on L) ↔
      HasMaximalRank (relationEvaluation (d := d) off on L hL) := by
  change (_ ∨ _) ↔ (_ ∨ _)
  rw [injective_iff off on L hL heval.1, surjective_iff off on L hL heval]

/-- The rank difference is precisely the scalar trace dimension. -/
theorem rank_eq [CharZero K]
    (heval : Function.Injective (traceScalarEvaluation (d := d) on)) :
    Module.finrank K (mixedEvaluation (d := d) off on L).range =
      Module.finrank K (relationEvaluation (d := d) off on L hL).range +
        Module.finrank K (Forms K n (d + 1)) := by
  rw [relationEvaluation_range off on L hL]
  exact (evaluationSquare (d := d) off on L hL).scalarReduction_rank
    (scalarTrace_surjective K n d) heval

/-- All components of an Euler relation evaluated at an ambient point. -/
def relationValue (x : Fin (n + 1) → K)
    (f : (formMultiplication K (n + 1) d).ker) : Fin (n + 1) → K :=
  fun j => eval x (f.val j).val

/-- The polynomial Euler equation remains valid at every representative. -/
theorem relationValue_euler (x : Fin (n + 1) → K)
    (f : (formMultiplication K (n + 1) d).ker) :
    ∑ j, x j * relationValue x f j = 0 := by
  have h := congrArg (eval x) (congrArg Subtype.val f.property)
  change eval x (∑ j, X j * (f.val j).val) = eval x 0 at h
  simpa only [map_sum, map_mul, eval_X, map_zero, relationValue] using h

/-- Off the hyperplane, tangential vanishing is the full point condition
on an Euler relation. -/
theorem relationValue_eq_zero_iff (x : Fin (n + 1) → K) (hx : x 0 ≠ 0)
    (f : (formMultiplication K (n + 1) d).ker) :
    relationValue x f = 0 ↔ tangentEvaluation x (forgetNormal K n d f) = 0 := by
  constructor
  · intro h
    ext j
    exact congrFun h j.succ
  · intro h
    have hs (j : Fin n) : relationValue x f j.succ = 0 := congrFun h j
    have he := relationValue_euler x f
    rw [Fin.sum_univ_succ] at he
    have ht : (∑ j : Fin n, x j.succ * relationValue x f j.succ) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hs j, mul_zero]
    rw [ht, add_zero] at he
    have hn : relationValue x f 0 = 0 := (mul_eq_zero.mp he).resolve_left hx
    funext j
    exact Fin.cases hn hs j

/-- On the hyperplane, the tangential value of every relation lies in the
trace fiber, which makes scalar conditions automatic. -/
theorem relation_tangentValue_mem_traceFiber (y : Fin n → K)
    (f : (formMultiplication K (n + 1) d).ker) :
    tangentEvaluation (Fin.cons 0 y) (forgetNormal K n d f) ∈ TraceFiber y := by
  have h := relationValue_euler (Fin.cons 0 y) f
  rw [Fin.sum_univ_succ] at h
  simpa [TraceFiber, pointDot, tangentEvaluation, relationValue] using h

/-- Mixed evaluation vanishes exactly when all off-hyperplane vector
values vanish and all hyperplane values lie in the prescribed subspaces. -/
theorem mixedEvaluation_eq_zero_iff (g : Fin n → Forms K (n + 1) d) :
    mixedEvaluation off on L g = 0 ↔
      (∀ i, tangentEvaluation (off i) g = 0) ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (on i)) g ∈ L i) := by
  change ((fun i => tangentEvaluation (off i) g),
    (fun i => (L i).mkQ (tangentEvaluation (Fin.cons 0 (on i)) g))) = 0 ↔ _
  rw [Prod.mk_eq_zero]
  simp only [funext_iff, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The reduced kernel has exactly the conditions in Lemma 3.5. Full
conditions remain full off the hyperplane, and on the hyperplane only
the tangential trace is tested against the chosen allowed subspace. -/
theorem relationEvaluation_eq_zero_iff
    (hoff : ∀ i, off i 0 ≠ 0)
    (f : (formMultiplication K (n + 1) d).ker) :
    relationEvaluation off on L hL f = 0 ↔
      (∀ i, relationValue (off i) f = 0) ∧
      (∀ i, tangentEvaluation (Fin.cons 0 (on i))
        (forgetNormal K n d f) ∈ L i) := by
  have hz : relationEvaluation off on L hL f = 0 ↔
      mixedEvaluation off on L (forgetNormal K n d f) = 0 := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [hz, mixedEvaluation_eq_zero_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun i => (relationValue_eq_zero_iff (off i) (hoff i) f).mpr (ha i), hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun i => (relationValue_eq_zero_iff (off i) (hoff i) f).mp (ha i), hb⟩

end ScalarTraceReduction
end IdealGeneration
