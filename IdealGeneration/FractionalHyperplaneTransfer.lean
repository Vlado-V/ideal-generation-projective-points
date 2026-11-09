module

public import IdealGeneration.FractionalInitialTrace
public import IdealGeneration.FractionalTransferCounts
public import IdealGeneration.FractionalOuterTransfer
public import IdealGeneration.CriticalOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The fractional hyperplane transfer

The ambient space has `m + 2` variables and the top degree is `d + 3`.
This is Proposition 3.8 in the affine-chart indexing convention.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial HyperplaneEuler DifferentialPoint DifferentialFiber
  FractionalHyperplane FractionalCompatibility FractionalTransferCounts
  FractionalInitialTrace FractionalOuterTransfer FractionalOuterResidual
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K] [CharZero K]

/-- The fractional transfer with its arithmetic conditions expressed as natural point counts. -/
theorem fractional_hyperplane_transfer_of_counts (m d : ℕ) (hm : 2 ≤ m)
    (hgap : upperCritical (m + 1) (d + 3) = lowerCritical (m + 1) (d + 3) + 1)
    (hdef : N (m + 1) (d + 4) ≤ (m + 1) * N (m + 1) (d + 2))
    (hI : (fractionalResidualICount (m + 2) (d + 3) : ℚ) = fractionalResidualI (m + 2) (d + 3))
    (hS : (fractionalResidualSCount (m + 2) (d + 3) : ℚ) = fractionalResidualS (m + 2) (d + 3))
    (hpos : 1 ≤ fractionalResidualICount (m + 2) (d + 3))
    (horder : fractionalResidualICount (m + 2) (d + 3) ≤ fractionalResidualSCount (m + 2) (d + 3))
    (hbudget : (m + 1) * fractionalResidualSCount (m + 2) (d + 3) ≤
      lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3))
    (hcell : lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3) + 2 ≤
      N (m + 1) (d + 2))
    (hres : ScalarInjectionAt K (m + 1) (d + 1) (fractionalResidualSCount (m + 2) (d + 3)))
    (htop : ∀ p, IdealGenerationAt K m (d + 3) p)
    (hlower : ∀ p, IdealGenerationAt K m (d + 2) p) :
    ∀ p, IdealGenerationAt K (m + 1) (d + 3) p := by
  obtain ⟨A, y, hscalar, htrace, hBdim, hBvalue⟩ :=
    exists_initial_trace m (d + 3) (by omega) (by omega) htop
  let B := (eulerTraceEvaluation A (d + 3)).ker
  let L := traceImage B (Fin.cons 0 (Fin.snoc y 1))
  have hL : ∀ l ∈ L, dot (Fin.snoc y 1) l = 0 := topTraceImage_tangent y B
  have hLdim : finrank K L = fractionalTopTraceDimension (m + 2) (d + 3) := by
    rw [finrank_traceImage_of_injective B (Fin.snoc y 1) hBvalue]
    exact hBdim
  obtain ⟨hjointI, hjointS⟩ := exists_fractional_joint_witnesses m d hm y L hL hLdim
    hgap hdef hI hS hpos horder hbudget hcell hres hlower
  obtain ⟨aI, haI⟩ := hjointI
  obtain ⟨aS, haS⟩ := hjointS
  have hupper := upperCritical_mem_cell (m + 1) (d + 3) (by omega) (by omega)
  have hcompletionNat : (pointCount m (d + 3) + 1) + lowerCritical (m + 1) (d + 3) =
      N (m + 1) (d + 3) := by
    dsimp [pointCount]
    omega
  have hcompletion : (pointCount m (d + 3) + 1) + lowerCritical (m + 1) (d + 3) =
      (m + (d + 3)).choose (d + 3) := by
    simpa only [N_chart] using hcompletionNat
  have hboundS : fractionalResidualSCount (m + 2) (d + 3) ≤ N (m + 2) (d + 1) :=
    scalarInjectionAt_count_le hres
  have hboundI := horder.trans hboundS
  have hgap' : upperCritical (m + 2 - 1) (d + 3) = lowerCritical (m + 2 - 1) (d + 3) + 1 := by
    simpa using hgap
  have hfloor := fractional_trace_floor_le_critical (m + 2) (d + 3)
  have hcountsI := fractional_point_count_balance (m + 2) (d + 3)
    (lowerCritical (m + 2) (d + 3)) (fractionalResidualICount (m + 2) (d + 3))
    (by omega) (by omega) hgap'
    (by simp only [fractionalResidualICount]) hpos hboundI hfloor.1
  have hcountsS := fractional_point_count_balance (m + 2) (d + 3)
    (upperCritical (m + 2) (d + 3)) (fractionalResidualSCount (m + 2) (d + 3))
    (by omega) (by omega) hgap'
    (by simp only [fractionalResidualSCount]) (hpos.trans horder) hboundS hfloor.2
  simp only [show m + 2 - 1 = m + 1 by omega, show d + 3 - 2 = d + 1 by omega,
    show d + 3 - 1 = d + 2 by omega] at hcountsI hcountsS
  have hGI := injective_joint_to_idealGeneration A y hscalar hBvalue hcompletion
    hcountsI.2.2.2.1 aI haI
  have hGS := surjective_joint_to_idealGeneration A y hscalar htrace hcompletion
    hcountsS.2.2.2.1 aS haS
  have hcountI :
      (N (m + 2) (d + 1) - fractionalResidualICount (m + 2) (d + 3) +
        fractionalTraceRows (m + 2) (d + 3) + 1 + lowerCritical (m + 1) (d + 3)) +
        (pointCount m (d + 3) + 1) =
      N (m + 2) (d + 3) - lowerCritical (m + 2) (d + 3) := by
    have hcount := hcountsI.2.2.2.2
    dsimp [pointCount]
    omega
  have hcountS :
      (N (m + 2) (d + 1) - fractionalResidualSCount (m + 2) (d + 3) +
        fractionalTraceRows (m + 2) (d + 3) + 1 + lowerCritical (m + 1) (d + 3)) +
        (pointCount m (d + 3) + 1) =
      N (m + 2) (d + 3) - upperCritical (m + 2) (d + 3) := by
    have hcount := hcountsS.2.2.2.2
    dsimp [pointCount]
    omega
  apply idealGenerationAt_all_of_critical (by omega) (by omega)
  · exact hcountI ▸ hGI
  · exact hcountS ▸ hGS

/-- Proposition 3.8, with the original fractional residual and scalar-budget hypotheses. -/
theorem fractional_hyperplane_transfer (m d : ℕ) (hm : 2 ≤ m)
    (hfrac : ¬∃ r : ℕ, E (m + 1) (d + 3) = (r : ℚ))
    (hdef : N (m + 1) (d + 4) ≤ (m + 1) * N (m + 1) (d + 2))
    (hpos : 1 ≤ fractionalResidualI (m + 2) (d + 3))
    (hbudget : ((m + 1 : ℕ) : ℚ) * fractionalResidualS (m + 2) (d + 3) ≤
      (lowerCritical (m + 1) (d + 3) : ℚ) + fractionalTraceRows (m + 2) (d + 3))
    (hcell : lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3) + 2 ≤
      N (m + 1) (d + 2))
    (hres : ScalarInjectionAt K (m + 1) (d + 1) (fractionalResidualSCount (m + 2) (d + 3)))
    (htop : ∀ p, IdealGenerationAt K m (d + 3) p)
    (hlower : ∀ p, IdealGenerationAt K m (d + 2) p) :
    ∀ p, IdealGenerationAt K (m + 1) (d + 3) p := by
  have hdef' : N (m + 2 - 1) (d + 3 + 1) ≤
      (m + 2 - 1) * N (m + 2 - 1) (d + 3 - 1) := by simpa using hdef
  have hI := fractionalResidualICount_cast (m + 2) (d + 3) (by omega) hdef' (by linarith)
  have horderR := fractionalResidualI_le_S (m + 2) (d + 3)
  have hS := fractionalResidualSCount_cast (m + 2) (d + 3) (by omega) hdef' (by linarith)
  have hposN : 1 ≤ fractionalResidualICount (m + 2) (d + 3) := by
    have h : (1 : ℚ) ≤ (fractionalResidualICount (m + 2) (d + 3) : ℚ) := by rwa [hI]
    exact_mod_cast h
  have horderN : fractionalResidualICount (m + 2) (d + 3) ≤
      fractionalResidualSCount (m + 2) (d + 3) := by
    have h : (fractionalResidualICount (m + 2) (d + 3) : ℚ) ≤
        (fractionalResidualSCount (m + 2) (d + 3) : ℚ) := by rwa [hI, hS]
    exact_mod_cast h
  have hbudgetN : (m + 1) * fractionalResidualSCount (m + 2) (d + 3) ≤
      lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3) := by
    have h := fractional_scalar_budget_nat (m + 2) (d + 3) hS
      (by simpa using hbudget)
    simpa using h
  exact fractional_hyperplane_transfer_of_counts m d hm
    (fractional_critical_gap (m + 1) (d + 3) hfrac) hdef hI hS hposN horderN
    hbudgetN hcell hres htop hlower

end IdealGeneration
