module

public import IdealGeneration.ScalarTraceReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimensions of mixed scalar-trace conditions

Nonzero hyperplane representatives make the scalar condition projection
surjective. Its kernel is the reduced condition space from Lemma 3.5.
-/

noncomputable section
namespace IdealGeneration.ScalarTraceReduction
open Module
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n p q : ℕ}

/-- Dot product with a nonzero representative attains every scalar. -/
theorem pointDot_surjective (y : Fin n → K) (hy : ∃ j, y j ≠ 0) :
    Function.Surjective (pointDot y) := by
  classical
  obtain ⟨j, hj⟩ := hy
  intro c
  refine ⟨Pi.single j (c / y j), ?_⟩
  simp [pointDot, Pi.single_apply]
  field_simp

/-- Every scalar condition value lifts to the mixed condition space. -/
theorem conditionScalarProjection_surjective
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i))
    (hon : ∀ i, ∃ j, on i j ≠ 0) :
    Function.Surjective (conditionScalarProjection (p := p) on L hL) := by
  classical
  intro c
  choose v hv using fun i => pointDot_surjective (on i) (hon i) (c i)
  refine ⟨(0, fun i => (L i).mkQ (v i)), ?_⟩
  ext i
  exact hv i

/-- Quotienting the tangential value space by `L` removes its dimension. -/
theorem valueQuotient_finrank (L : Submodule K (Fin n → K)) :
    finrank K ((Fin n → K) ⧸ L) = n - finrank K L := by
  have h := L.finrank_quotient_add_finrank
  have hv : finrank K (Fin n → K) = n := by simp
  rw [hv] at h
  omega

/-- Full off-hyperplane values and quotient hyperplane values contribute
their usual numbers of independent coordinates to the condition target. -/
theorem conditionSpace_finrank (L : Fin q → Submodule K (Fin n → K)) :
    finrank K (ConditionSpace (p := p) L) =
      p * n + ∑ i, (n - finrank K (L i)) := by
  simp [ConditionSpace, Module.finrank_pi_fintype, valueQuotient_finrank]

/-- The trace fiber has codimension one at a nonzero representative. -/
theorem traceFiber_finrank (y : Fin n → K) (hy : ∃ j, y j ≠ 0) :
    finrank K (TraceFiber y) = n - 1 := by
  have h := (pointDot y).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pointDot_surjective y hy), finrank_top] at h
  have hv : finrank K (Fin n → K) = n := by simp
  simp only [Module.finrank_self] at h
  change 1 + finrank K (TraceFiber y) = finrank K (Fin n → K) at h
  rw [hv] at h
  omega

/-- Removing the scalar quotient subtracts exactly one condition per
hyperplane point. The additive form records the full dimension balance. -/
theorem conditionScalarProjection_ker_finrank_add
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i))
    (hon : ∀ i, ∃ j, on i j ≠ 0) :
    finrank K (conditionScalarProjection (p := p) on L hL).ker + q =
      finrank K (ConditionSpace (p := p) L) := by
  have h := (conditionScalarProjection (p := p) on L hL).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (conditionScalarProjection_surjective (p := p) on L hL hon), finrank_top] at h
  have hq : finrank K (Fin q → K) = q := by simp
  rw [hq] at h
  omega

/-- The reduced target dimension is the mixed target dimension less the
number of scalar trace conditions. -/
theorem conditionScalarProjection_ker_finrank
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i))
    (hon : ∀ i, ∃ j, on i j ≠ 0) :
    finrank K (conditionScalarProjection (p := p) on L hL).ker =
      finrank K (ConditionSpace (p := p) L) - q := by
  have h := conditionScalarProjection_ker_finrank_add (p := p) on L hL hon
  omega

/-- In the reduced target, each hyperplane point contributes the
codimension of its allowed subspace inside the trace fiber. -/
theorem conditionScalarProjection_ker_finrank_eq
    (on : Fin q → Fin n → K) (L : Fin q → Submodule K (Fin n → K))
    (hL : ∀ i, L i ≤ TraceFiber (on i))
    (hon : ∀ i, ∃ j, on i j ≠ 0) :
    finrank K (conditionScalarProjection (p := p) on L hL).ker =
      p * n + ∑ i, (n - 1 - finrank K (L i)) := by
  have hterm (i : Fin q) :
      n - finrank K (L i) = (n - 1 - finrank K (L i)) + 1 := by
    have hdim := Submodule.finrank_mono (hL i)
    rw [traceFiber_finrank (on i) (hon i)] at hdim
    obtain ⟨j, _⟩ := hon i
    have hn := j.isLt
    omega
  have hs : (∑ i, (n - finrank K (L i))) =
      (∑ i, (n - 1 - finrank K (L i))) + q := by
    simp_rw [hterm]
    simp [Finset.sum_add_distrib]
  have h := conditionScalarProjection_ker_finrank_add (p := p) on L hL hon
  rw [conditionSpace_finrank, hs] at h
  omega

end IdealGeneration.ScalarTraceReduction
