module

public import IdealGeneration.ScalarInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar interpolation on a fixed space of forms

General points impose the largest possible number of conditions on every fixed
linear subspace of homogeneous forms. This supplies the scalar transversality
used in the ordinary hyperplane transfer.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {K : Type*} [Field K] {n d : ℕ}

/-- Evaluation restricted to a fixed space of homogeneous forms. -/
def subspaceEvaluation (U : Submodule K (Forms K (n + 1) d))
    {p : ℕ} (a : PointCoordinates K n p) : U →ₗ[K] (Fin p → K) :=
  (pointEvaluation K a d).comp U.subtype

/-- A single chart-evaluation functional on the fixed subspace. -/
def subspaceFunctional (U : Submodule K (Forms K (n + 1) d)) (x : Fin n → K) :
    U →ₗ[K] K := (evaluationLinear K (n + 1) d (Fin.snoc x 1)).comp U.subtype

/-- Chart evaluations separate every subspace of homogeneous forms. -/
theorem subspaceFunctionals_span [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) :
    Submodule.span K (Set.range (subspaceFunctional U)) = ⊤ := by
  have : Module.Free K U := by
    with_unfolding_all exact Module.Free.of_divisionRing K U
  have : Module.IsReflexive K U := by
    with_unfolding_all exact Module.IsReflexive.of_finite_of_free (R := K) (M := U)
  with_unfolding_all apply Submodule.span_eq_top_of_ne_zero (R := K) (M := U)
  intro f hf
  by_contra! h
  apply hf
  apply Subtype.ext
  apply homogeneous_eq_zero_of_chart_evaluations
  intro x
  exact h (subspaceFunctional U x) ⟨x, rfl⟩

/-- Choose any allowable number of independent scalar conditions. -/
theorem exists_independent_subspaceFunctionals [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (q : ℕ) (hq : q ≤ finrank K U) :
    ∃ x : Fin q → Fin n → K,
      LinearIndependent K (fun i => subspaceFunctional U (x i)) := by
  classical
  induction q with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  | succ q ih =>
    obtain ⟨x, hx⟩ := ih (by omega)
    let W := Submodule.span K (Set.range (fun i => subspaceFunctional U (x i)))
    have hW : finrank K W = q := by simp [W, finrank_span_eq_card hx]
    have hproper : W ≠ ⊤ := by
      intro heq
      have ht : finrank K W = finrank K U := by
        rw [heq, finrank_top]
        with_unfolding_all exact Subspace.dual_finrank_eq (K := K) (V := U)
      omega
    have hex : ∃ y, subspaceFunctional U y ∉ W := by
      by_contra! h
      have hle : Submodule.span K (Set.range (subspaceFunctional U)) ≤ W := by
        apply Submodule.span_le.mpr
        rintro _ ⟨y, rfl⟩
        exact h y
      rw [subspaceFunctionals_span] at hle
      exact hproper (top_le_iff.mp hle)
    obtain ⟨y, hy⟩ := hex
    refine ⟨Fin.snoc x y, ?_⟩
    have heq : (fun i : Fin (q + 1) =>
        subspaceFunctional U ((Fin.snoc x y : Fin (q + 1) → Fin n → K) i)) =
        Fin.snoc (fun i => subspaceFunctional U (x i)) (subspaceFunctional U y) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [heq]
    exact linearIndependent_finSnoc.mpr ⟨hx, hy⟩

/-- Independent scalar functionals evaluate surjectively, using only the additive-monoid structure. -/
private theorem independentFunctionals_surjective {V : Type*} [AddCommMonoid V]
    [Module K V] {q : ℕ} (α : Fin q → V →ₗ[K] K)
    (hα : LinearIndependent K α) : Function.Surjective (LinearMap.pi α) := by
  have hfun : LinearIndependent K (fun i x => α i x) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    apply (Fintype.linearIndependent_iff.mp hα) c ?_ i
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, LinearMap.zero_apply] using congrFun hc x
  have hspan : Submodule.span K (Set.range (fun x i => α i x)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hfun
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Some actual configuration imposes the maximum number of scalar conditions on `U`. -/
theorem exists_subspaceEvaluation_maximal [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) :
    ∃ a : PointCoordinates K n p,
      finrank K (subspaceEvaluation U a).range = min (finrank K U) p := by
  classical
  let q := min (finrank K U) p
  obtain ⟨x, hx⟩ := exists_independent_subspaceFunctionals U q (min_le_left _ _)
  let a : PointCoordinates K n p := fun ij =>
    if h : ij.1.val < q then x ⟨ij.1.val, h⟩ ij.2 else 0
  refine ⟨a, le_antisymm ?_ ?_⟩
  · apply le_min (subspaceEvaluation U a).finrank_range_le
    simpa using Submodule.finrank_le (subspaceEvaluation U a).range
  · let α : Fin q → U →ₗ[K] K := fun i => subspaceFunctional U (x i)
    have honto := independentFunctionals_surjective α hx
    choose v hv using fun i : Fin q => honto (Pi.single i 1)
    have hrow (i j : Fin q) : subspaceEvaluation U a (v i)
        (Fin.castLE (min_le_right _ _) j) = if j = i then 1 else 0 := by
      have ha : chartPoint K a (Fin.castLE (min_le_right _ _) j) = Fin.snoc (x j) 1 := by
        funext k
        refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [chartPoint, a, j.isLt]
      have hh := congrFun (hv i) j
      simpa [subspaceEvaluation, subspaceFunctional, α, pointEvaluation,
        evaluationLinear, ha, Pi.single_apply] using hh
    have hLI : LinearIndependent K (fun i : Fin q => subspaceEvaluation U a (v i)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hi := congrFun hc (Fin.castLE (min_le_right _ _) i)
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hi
      simpa [hrow] using hi
    have hle : Submodule.span K
        (Set.range (fun i : Fin q => subspaceEvaluation U a (v i))) ≤
        (subspaceEvaluation U a).range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    have hdim := Submodule.finrank_mono hle
    simpa only [finrank_span_eq_card hLI, Fintype.card_fin] using hdim

/-- Scalar evaluation on a fixed subspace varies polynomially with its points. -/
theorem subspaceEvaluation_isPolynomialFamily
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K n p => subspaceEvaluation U a) := by
  apply isPolynomialFamily_linearMap (K := K) (V := U) (W := Fin p → K)
  intro f
  exact (pointEvaluation_isPolynomialFamily (K := K) n p d).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Fin p → K) f.val)

/-- The maximal scalar rank holds on a nonempty principal open. -/
theorem generic_subspaceEvaluation [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        finrank K (subspaceEvaluation U a).range = min (finrank K U) p := by
  obtain ⟨a₀, ha₀⟩ := exists_subspaceEvaluation_maximal U p
  obtain ⟨D, hD, hgood⟩ := rank_polynomial_principal_open (K := K) (V := U)
    (W := Fin p → K)
    (fun a : PointCoordinates K n p => subspaceEvaluation U a)
    (subspaceEvaluation_isPolynomialFamily U p) a₀
  refine ⟨D, ⟨a₀, hD⟩, fun a ha => le_antisymm ?_ ?_⟩
  · apply le_min (subspaceEvaluation U a).finrank_range_le
    simpa using Submodule.finrank_le (subspaceEvaluation U a).range
  · simpa only [ha₀] using hgood a ha

/-- Enough scalar evaluations can separate a fixed space of forms. -/
theorem exists_injective_subspaceEvaluation [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) (hp : finrank K U ≤ p) :
    ∃ a : PointCoordinates K n p, Function.Injective (subspaceEvaluation U a) := by
  classical
  let q := finrank K U
  obtain ⟨x, hx⟩ := exists_independent_subspaceFunctionals U q le_rfl
  let α : Fin q → U →ₗ[K] K := fun i => subspaceFunctional U (x i)
  have hspan : Submodule.span K (Set.range α) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hx, Fintype.card_fin]
    with_unfolding_all exact (Subspace.dual_finrank_eq (K := K) (V := U)).symm
  let a : PointCoordinates K n p := fun ij =>
    if h : ij.1.val < q then x ⟨ij.1.val, h⟩ ij.2 else 0
  have hrow (f : U) (i : Fin q) :
      subspaceEvaluation U a f (Fin.castLE hp i) = α i f := by
    have ha : chartPoint K a (Fin.castLE hp i) = Fin.snoc (x i) 1 := by
      funext j
      refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [chartPoint, a, i.isLt]
    simp [subspaceEvaluation, subspaceFunctional, α, pointEvaluation, evaluationLinear, ha]
  have hzero (f : U) (hf : subspaceEvaluation U a f = 0) : f = 0 := by
    let evf : (U →ₗ[K] K) →ₗ[K] K := LinearMap.applyₗ f
    have hle : Submodule.span K (Set.range α) ≤ evf.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change α i f = 0
      rw [← hrow]
      exact congrFun hf _
    rw [hspan] at hle
    apply Subtype.ext
    apply homogeneous_eq_zero_of_chart_evaluations
    intro y
    have hmem := hle (show subspaceFunctional U y ∈ (⊤ : Submodule K (U →ₗ[K] K)) from trivial)
    exact hmem
  refine ⟨a, ?_⟩
  intro f g hfg
  apply sub_eq_zero.mp
  apply hzero
  ext i
  change eval (chartPoint K a i) (f.val.val - g.val.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hfg i)

/-- General evaluation is injective when there are enough point conditions. -/
theorem generic_subspaceEvaluation_injective [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) (hp : finrank K U ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Injective (subspaceEvaluation U a) := by
  obtain ⟨a₀, ha₀⟩ := exists_injective_subspaceEvaluation U p hp
  obtain ⟨D, hD, hgood⟩ := injective_polynomial_principal_open (K := K) (V := U)
    (W := Fin p → K) (fun a : PointCoordinates K n p => subspaceEvaluation U a)
    (subspaceEvaluation_isPolynomialFamily U p) a₀ ha₀
  exact ⟨D, ⟨a₀, hD⟩, hgood⟩

/-- General evaluation is surjective when the fixed space has enough dimensions. -/
theorem generic_subspaceEvaluation_surjective [Infinite K]
    (U : Submodule K (Forms K (n + 1) d)) (p : ℕ) (hp : p ≤ finrank K U) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (subspaceEvaluation U a) := by
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation U p
  refine ⟨D, hD, fun a ha => ?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [min_eq_right hp] using hgood a ha

end IdealGeneration
