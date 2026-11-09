module

public import IdealGeneration.FractionalHyperplane
public import IdealGeneration.FractionalPointCounts
public import IdealGeneration.FractionalResidualBridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Instantiation of the lower fractional construction at the two critical counts. -/

noncomputable section
namespace IdealGeneration.FractionalTransferCounts
open Module MvPolynomial DifferentialPoint DifferentialFiber HyperplaneEuler
  FractionalHyperplane FractionalCompatibility

variable {K : Type*} [Field K] [CharZero K]

local instance {n d : ℕ} : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

/-- The fixed first trace has precisely the dimensions required by the second movement. -/
theorem lower_partial_counts (m d : ℕ) (hm : 2 ≤ m)
    (ystar : Fin m → K) (Lstar : Submodule K (Fin (m + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hLdim : finrank K Lstar = fractionalTopTraceDimension (m + 2) (d + 3))
    (hgap : upperCritical (m + 1) (d + 3) = lowerCritical (m + 1) (d + 3) + 1)
    (hdef : N (m + 1) (d + 4) ≤ (m + 1) * N (m + 1) (d + 2)) :
    let p := lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3)
    fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) p =
        fractionalTraceRemainder (m + 2) (d + 3) ∧
      fixedPartialTraceDimension (Lstar.map dropLast) (d + 2) (p + 1) = 0 ∧
      m * p + (m - finrank K (Lstar.map dropLast)) ≤
        finrank K (EulerRelations K m (d + 2)) := by
  have hmap : finrank K (Lstar.map dropLast) =
      fractionalTopTraceDimension (m + 2) (d + 3) := by
    rw [finrank_drop_tangent_subspace (Fin.snoc ystar 1) (by simp) Lstar hLstar]
    exact hLdim
  have hgap' : upperCritical (m + 2 - 1) (d + 3) =
      lowerCritical (m + 2 - 1) (d + 3) + 1 := by simpa using hgap
  have hdef' : N (m + 2 - 1) (d + 3 + 1) ≤
      (m + 2 - 1) * N (m + 2 - 1) (d + 3 - 1) := by
    simpa only [show m + 2 - 1 = m + 1 by omega,
      show d + 3 + 1 = d + 4 by omega, show d + 3 - 1 = d + 2 by omega] using hdef
  have hdim := fractional_inner_expected_dimension (m + 2) (d + 3)
    (by omega) hgap' hdef'
  have hnext := fractional_inner_after_one (m + 2) (d + 3)
    (by omega) hgap' hdef'
  have hbound := fractional_inner_condition_bound (m + 2) (d + 3)
    (by omega) hgap' hdef'
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · rw [fixedPartialTraceDimension, eulerRelations_finrank, hmap]
    simpa only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      show d + 3 - 1 = d + 2 by omega, show d + 2 + 1 = d + 3 by omega] using hdim
  · rw [fixedPartialTraceDimension, eulerRelations_finrank, hmap]
    simpa only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      show d + 3 - 1 = d + 2 by omega, show d + 2 + 1 = d + 3 by omega] using hnext
  · rw [eulerRelations_finrank, hmap]
    simpa only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      show d + 3 - 1 = d + 2 by omega, show d + 2 + 1 = d + 3 by omega] using hbound

/-- The two numerical critical counts give actual lower joint-coordinate witnesses. -/
theorem exists_fractional_joint_witnesses (m d : ℕ) (hm : 2 ≤ m)
    (ystar : Fin m → K) (Lstar : Submodule K (Fin (m + 1) → K))
    (hLstar : ∀ l ∈ Lstar, dot (Fin.snoc ystar 1) l = 0)
    (hLdim : finrank K Lstar = fractionalTopTraceDimension (m + 2) (d + 3))
    (hgap : upperCritical (m + 1) (d + 3) = lowerCritical (m + 1) (d + 3) + 1)
    (hdef : N (m + 1) (d + 4) ≤ (m + 1) * N (m + 1) (d + 2))
    (hI : (fractionalResidualICount (m + 2) (d + 3) : ℚ) =
      fractionalResidualI (m + 2) (d + 3))
    (hS : (fractionalResidualSCount (m + 2) (d + 3) : ℚ) =
      fractionalResidualS (m + 2) (d + 3))
    (hpos : 1 ≤ fractionalResidualICount (m + 2) (d + 3))
    (horder : fractionalResidualICount (m + 2) (d + 3) ≤
      fractionalResidualSCount (m + 2) (d + 3))
    (hbudget : (m + 1) * fractionalResidualSCount (m + 2) (d + 3) ≤
      lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3))
    (hcell : lowerCritical (m + 1) (d + 3) +
      fractionalTraceRows (m + 2) (d + 3) + 2 ≤ N (m + 1) (d + 2))
    (hres : ScalarInjectionAt K (m + 1) (d + 1)
      (fractionalResidualSCount (m + 2) (d + 3)))
    (hlower : ∀ p, IdealGenerationAt K m (d + 2) p) :
    (∃ a : JointCoordinates (K := K) m (lowerCritical (m + 1) (d + 3))
        (N (m + 2) (d + 1) - fractionalResidualICount (m + 2) (d + 3) +
          fractionalTraceRows (m + 2) (d + 3) + 1),
      Function.Injective (twoLevelEvaluation ystar (Lstar.map dropLast) a (d + 2))) ∧
    (∃ a : JointCoordinates (K := K) m (lowerCritical (m + 1) (d + 3))
        (N (m + 2) (d + 1) - fractionalResidualSCount (m + 2) (d + 3) +
          fractionalTraceRows (m + 2) (d + 3) + 1),
      Function.Surjective (twoLevelEvaluation ystar (Lstar.map dropLast) a (d + 2))) := by
  let p := lowerCritical (m + 1) (d + 3) + fractionalTraceRows (m + 2) (d + 3)
  let q := fractionalTraceRows (m + 2) (d + 3)
  let b := fractionalTraceRemainder (m + 2) (d + 3)
  have hpq : p - q = lowerCritical (m + 1) (d + 3) := by dsimp [p, q]; omega
  obtain ⟨hdim, hnext, htraceBound⟩ := lower_partial_counts m d hm
    ystar Lstar hLstar hLdim hgap hdef
  have hrows := fractional_inner_rows_bounds (m + 2) (d + 3)
    (by omega) hpos horder hI hS
  simp only [show m + 2 - 1 = m + 1 by omega] at hrows
  constructor
  · obtain ⟨a, ha, _, hmul, hadim⟩ := scalarInjectionAt_off_witness_of_le
      m (d + 1) (fractionalResidualICount (m + 2) (d + 3))
      (fractionalResidualSCount (m + 2) (d + 3)) horder hres
    have hpositive : 0 < finrank K (pointDegreePiece K a (d + 1)) := by
      rw [hadim]
      omega
    have hbudgetI : (m + 1) * finrank K (pointDegreePiece K a (d + 1)) ≤ p := by
      rw [hadim]
      exact (Nat.mul_le_mul_left (m + 1) horder).trans hbudget
    have hrowsI : (m + 1) * finrank K (pointDegreePiece K a (d + 1)) -
        (m + 1 - b) ≤ q := by
      rw [hadim]
      exact hrows.1
    obtain ⟨P, y, s, t, hcard, _, hmove⟩ := exists_inner_injective
      (p := p) (q := q) (b := b) a ha hmul hpositive ystar Lstar hLstar
      hcell (hlower p) (hlower (p + 1)) (hlower (p + 2)) hdim hnext
      hbudgetI (by dsimp [p, q]; omega) hrowsI
    have hinj := regroupedJoint_injective a P s t y ystar Lstar hLstar hmove
    have hex : ∃ a' : JointCoordinates (K := K) m (p - s.card)
        (N (m + 2) (d + 1) - fractionalResidualICount (m + 2) (d + 3) + s.card + 1),
        Function.Injective (twoLevelEvaluation ystar (Lstar.map dropLast) a' (d + 2)) :=
      ⟨regroupedJoint a P s t y, hinj⟩
    rw [hcard] at hex
    rw [hpq] at hex
    simpa only [q] using hex
  · obtain ⟨a, ha, hscalar, hmul, hadim⟩ := scalarInjectionAt_off_witness
      m (d + 1) (fractionalResidualSCount (m + 2) (d + 3)) hres
    have hpositive : 0 < finrank K (pointDegreePiece K a (d + 1)) := by
      rw [hadim]
      omega
    have hbudgetS : (m + 1) * finrank K (pointDegreePiece K a (d + 1)) ≤ p := by
      rwa [hadim]
    have hrowsS : q ≤ (m + 1) * finrank K (pointDegreePiece K a (d + 1)) -
        (m + 1 - b) := by
      rw [hadim]
      exact hrows.2
    obtain ⟨P, y, s, t, hcard, _, hmove⟩ := exists_inner_independent
      (p := p) (q := q) (b := b) a ha hmul hscalar hpositive ystar Lstar hLstar
      hcell (hlower p) (hlower (p + 1)) (hlower (p + 2)) hdim hnext htraceBound
      hbudgetS (by dsimp [p, q]; omega) hrowsS
    have ha' : ∀ i, chartPoint K a i 0 ≠ 0 := by
      intro i
      simpa only [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl,
        chartPoint_castSucc] using ha i
    have hsurj := regroupedJoint_surjective a ha' P s t y ystar Lstar hLstar hmove
    have hex : ∃ a' : JointCoordinates (K := K) m (p - s.card)
        (N (m + 2) (d + 1) - fractionalResidualSCount (m + 2) (d + 3) + s.card + 1),
        Function.Surjective (twoLevelEvaluation ystar (Lstar.map dropLast) a' (d + 2)) :=
      ⟨regroupedJoint a P s t y, hsurj⟩
    rw [hcard] at hex
    rw [hpq] at hex
    simpa only [q] using hex

end IdealGeneration.FractionalTransferCounts
