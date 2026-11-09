module

public import IdealGeneration.FractionalHyperplane

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The upper critical trace used by the fractional hyperplane transfer. -/

noncomputable section
namespace IdealGeneration.FractionalInitialTrace
open Module MvPolynomial HyperplaneEuler DifferentialPoint FractionalHyperplane
set_option maxHeartbeats 900000
variable {K : Type*} [Field K]

local instance relationGroup {m D : ℕ} : AddCommGroup (EulerRelations K m D) :=
  Module.addCommMonoidToAddCommGroup K
local instance relationSubmoduleGroup {m D : ℕ} (U : Submodule K (EulerRelations K m D)) :
    AddCommGroup U := Module.addCommMonoidToAddCommGroup K

/-- The number of fixed full trace points at the upper critical count. -/
abbrev pointCount (m D : ℕ) := N (m + 1) D - upperCritical (m + 1) D

/-- Adjacent trace interpolation supplies all the data for the first differential move. -/
theorem exists_initial_trace [CharZero K] (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (hIG : ∀ p, IdealGenerationAt K m D p) :
    ∃ (A : PointCoordinates K m (pointCount m D)) (y : Fin m → K),
      Function.Surjective (pointEvaluation K (snocPoints A y) D) ∧
      Function.Surjective (eulerTraceEvaluation A D) ∧
      finrank K (eulerTraceEvaluation A D).ker = fractionalTopTraceDimension (m + 2) D ∧
      Function.Injective ((vectorEvaluation (Fin.snoc y 1)).comp (eulerTraceEvaluation A D).ker.subtype) := by
  let q := pointCount m D
  let b := fractionalTopTraceDimension (m + 2) D
  have hupper := upperCritical_mem_cell (m + 1) D (by omega) hD
  have hp : q + 1 ≤ N (m + 1) D := by
    dsimp [q, pointCount]
    omega
  have hbalance : (m + 1) * N (m + 1) D = N (m + 1) (D + 1) + m * q + b := by
    simpa only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      q, pointCount, b] using fractional_top_dimension_balance (m + 2) D (by omega) hD
  have hsource : finrank K (EulerRelations K m D) = m * q + b := by
    rw [eulerRelations_finrank]
    omega
  have hb : b < m := by
    simpa only [b, show m + 2 - 2 = m by omega] using
      fractionalTopTraceDimension_lt (m + 2) D (by omega)
  have hsize : finrank K (EulerRelations K m D) ≤ m * (q + 1) := by
    rw [hsource, Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨A, y, hscalar, hker, hvalue⟩ := exists_initial_trace_and_scalar hp (hIG q) (hIG (q + 1)) hsize
  have hdim : finrank K (eulerTraceEvaluation A D).ker = b := by
    rw [hker, hsource]
    omega
  have htrace : Function.Surjective (eulerTraceEvaluation A D) := by
    have hr := (eulerTraceEvaluation A D).finrank_range_add_finrank_ker
    rw [hdim, hsource] at hr
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have ht : finrank K (Fin q → Fin m → K) = m * q := by
      simp [Module.finrank_pi_fintype, Nat.mul_comm]
    rw [ht]
    omega
  refine ⟨A, y, hscalar, htrace, hdim, ?_⟩
  intro f g hfg
  apply hvalue
  exact congrArg DifferentialFiber.dropLast hfg

end IdealGeneration.FractionalInitialTrace
