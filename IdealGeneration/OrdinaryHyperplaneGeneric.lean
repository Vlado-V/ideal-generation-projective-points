module

public import IdealGeneration.OrdinaryHyperplane
public import IdealGeneration.PolynomialTransversality
public import IdealGeneration.PointAvoidance
public import IdealGeneration.CriticalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# General-point consequences of ordinary hyperplane specialization

A fixed residual configuration determines its scalar trace-product space.
Generic scalar interpolation on that space can be imposed simultaneously
with the trace multiplication condition.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K] {m p q d : ℕ}

/-- An off-hyperplane residual witness and a general injective trace give the
injective ordinary transfer, with the scalar-row inequality stated directly. -/
theorem ordinary_hyperplane_injective_from_fixed_residual
    (a : PointCoordinates K (m + 1) p)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d))
    (hres : Function.Injective (pointMultiplication a d))
    (htrace : ∃ D : MvPolynomial (Fin q × Fin m) K,
      (∃ b : PointCoordinates K m q, eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Injective (pointMultiplication b (d + 1)))
    (hq : (m + 1) * finrank K (pointDegreePiece K a d) ≤ q) :
    IdealGenerationAt K (m + 1) (d + 1) (p + q) := by
  let U := (coordinateProduct (pointPolynomialPiece a d)).range.map
    (hyperplaneRestrict K (m + 1)).toLinearMap
  have ha' : ∀ i, chartPoint K a i (0 : Fin (m + 2)) ≠ 0 := by
    intro i
    change chartPoint K a i (Fin.castSucc 0) ≠ 0
    simpa only [chartPoint_castSucc] using ha i
  have hdim : finrank K U = (m + 1) * finrank K (pointDegreePiece K a d) :=
    finrank_restricted_pointProducts a ha' hres
  have hU : U ≤ Forms K (m + 1) (d + 1) := restricted_pointProducts_le_forms a
  obtain ⟨E, hE, hgoodE⟩ := generic_polynomial_disjoint U hU q (by simpa only [hdim] using hq)
  obtain ⟨D, hD, hgoodD⟩ := htrace
  obtain ⟨b, hbD, hbE⟩ := principal_opens_meet D E hD hE
  have hinj := ordinary_hyperplane_injective a b ha hoff hres (hgoodD b hbD) (hgoodE b hbE)
  exact idealGenerationAt_of_injective_witness (by omega) (hyperplaneConfiguration a b) hinj

/-- An off-hyperplane residual witness and a general surjective trace give the
surjective ordinary transfer, with the scalar-row inequality stated directly. -/
theorem ordinary_hyperplane_surjective_from_fixed_residual
    (a : PointCoordinates K (m + 1) p)
    (ha : ∀ i, a (i, 0) ≠ 0)
    (hoff : Function.Surjective (pointEvaluation K a d))
    (hres : Function.Injective (pointMultiplication a d))
    (htrace : ∃ D : MvPolynomial (Fin q × Fin m) K,
      (∃ b : PointCoordinates K m q, eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 →
        Function.Surjective (pointEvaluation K b (d + 1)) ∧
        Function.Surjective (pointMultiplication b (d + 1)))
    (hq : q ≤ (m + 1) * finrank K (pointDegreePiece K a d)) :
    IdealGenerationAt K (m + 1) (d + 1) (p + q) := by
  let U := (coordinateProduct (pointPolynomialPiece a d)).range.map
    (hyperplaneRestrict K (m + 1)).toLinearMap
  have ha' : ∀ i, chartPoint K a i (0 : Fin (m + 2)) ≠ 0 := by
    intro i
    change chartPoint K a i (Fin.castSucc 0) ≠ 0
    simpa only [chartPoint_castSucc] using ha i
  have hdim : finrank K U = (m + 1) * finrank K (pointDegreePiece K a d) :=
    finrank_restricted_pointProducts a ha' hres
  have hU : U ≤ Forms K (m + 1) (d + 1) := restricted_pointProducts_le_forms a
  obtain ⟨E, hE, hgoodE⟩ := generic_polynomial_sup U hU q (by simpa only [hdim] using hq)
  obtain ⟨D, hD, hgoodD⟩ := htrace
  obtain ⟨b, hbD, hbE⟩ := principal_opens_meet D E hD hE
  obtain ⟨hscalar, hsurj⟩ := hgoodD b hbD
  have hmult := ordinary_hyperplane_surjective a b ha hoff hsurj (hgoodE b hbE)
  have heval := pointEvaluation_hyperplaneConfiguration_surjective a b ha hoff hscalar
  exact idealGenerationAt_of_witness (by omega) (hyperplaneConfiguration a b) heval (Or.inr hmult)

/-- General residual and trace injection hypotheses imply ordinary hyperplane
specialization. The residual ideal dimension is measured by the given `r`. -/
theorem ordinary_hyperplane_injective_from_opens (r : ℕ)
    (hres : ∃ D : MvPolynomial (Fin p × Fin (m + 1)) K,
      (∃ a : PointCoordinates K (m + 1) p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        Function.Surjective (pointEvaluation K a d) ∧
        Function.Injective (pointMultiplication a d) ∧
        finrank K (pointDegreePiece K a d) = r)
    (htrace : ∃ D : MvPolynomial (Fin q × Fin m) K,
      (∃ b : PointCoordinates K m q, eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Injective (pointMultiplication b (d + 1)))
    (hq : (m + 1) * r ≤ q) : IdealGenerationAt K (m + 1) (d + 1) (p + q) := by
  obtain ⟨D, hD, hgood⟩ := hres
  obtain ⟨a, haD, ha⟩ := principal_open_meets_off_hyperplane D hD
  obtain ⟨hscalar, hinj, hdim⟩ := hgood a haD
  apply ordinary_hyperplane_injective_from_fixed_residual a ha hscalar hinj htrace
  simpa only [hdim] using hq

/-- General residual and trace surjection hypotheses imply the surjective
ordinary hyperplane transfer. -/
theorem ordinary_hyperplane_surjective_from_opens (r : ℕ)
    (hres : ∃ D : MvPolynomial (Fin p × Fin (m + 1)) K,
      (∃ a : PointCoordinates K (m + 1) p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        Function.Surjective (pointEvaluation K a d) ∧
        Function.Injective (pointMultiplication a d) ∧
        finrank K (pointDegreePiece K a d) = r)
    (htrace : ∃ D : MvPolynomial (Fin q × Fin m) K,
      (∃ b : PointCoordinates K m q, eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 →
        Function.Surjective (pointEvaluation K b (d + 1)) ∧
        Function.Surjective (pointMultiplication b (d + 1)))
    (hq : q ≤ (m + 1) * r) : IdealGenerationAt K (m + 1) (d + 1) (p + q) := by
  obtain ⟨D, hD, hgood⟩ := hres
  obtain ⟨a, haD, ha⟩ := principal_open_meets_off_hyperplane D hD
  obtain ⟨hscalar, hinj, hdim⟩ := hgood a haD
  apply ordinary_hyperplane_surjective_from_fixed_residual a ha hscalar hinj htrace
  simpa only [hdim] using hq


/-- The residual and trace point counts add to the ambient point count. -/
theorem ordinary_hyperplane_point_count (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ N (m + 2) d) (hr₂ : r₂ ≤ N (m + 1) (d + 1)) :
    (N (m + 2) d - r₁) + (N (m + 1) (d + 1) - r₂) =
      N (m + 2) (d + 1) - (r₁ + r₂) := by
  have hpascal : N (m + 2) (d + 1) = N (m + 1) (d + 1) + N (m + 2) d := by
    simpa only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel] using
      N_pascal (m + 2) (d + 1) (by omega) (by omega)
  omega

/-- The injective scalar-row inequality in the point-count notation of Lemma 3.1. -/
theorem ordinary_hyperplane_injective_cell (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ N (m + 2) d) (hr₂ : r₂ ≤ N (m + 1) (d + 1))
    (hres : ∃ D : MvPolynomial (Fin (N (m + 2) d - r₁) × Fin (m + 1)) K,
      (∃ a : PointCoordinates K (m + 1) (N (m + 2) d - r₁), eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
        Function.Injective (pointMultiplication a d) ∧
        finrank K (pointDegreePiece K a d) = r₁)
    (htrace : ∃ D : MvPolynomial (Fin (N (m + 1) (d + 1) - r₂) × Fin m) K,
      (∃ b : PointCoordinates K m (N (m + 1) (d + 1) - r₂), eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Injective (pointMultiplication b (d + 1)))
    (hbudget : (m + 1) * r₁ + r₂ ≤ N (m + 1) (d + 1)) :
    IdealGenerationAt K (m + 1) (d + 1) (N (m + 2) (d + 1) - (r₁ + r₂)) := by
  have h := ordinary_hyperplane_injective_from_opens r₁ hres htrace (by omega)
  simpa only [ordinary_hyperplane_point_count r₁ r₂ hr₁ hr₂] using h

/-- The surjective scalar-row inequality in the point-count notation of Lemma 3.1. -/
theorem ordinary_hyperplane_surjective_cell (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≤ N (m + 2) d) (hr₂ : r₂ ≤ N (m + 1) (d + 1))
    (hres : ∃ D : MvPolynomial (Fin (N (m + 2) d - r₁) × Fin (m + 1)) K,
      (∃ a : PointCoordinates K (m + 1) (N (m + 2) d - r₁), eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
        Function.Injective (pointMultiplication a d) ∧
        finrank K (pointDegreePiece K a d) = r₁)
    (htrace : ∃ D : MvPolynomial (Fin (N (m + 1) (d + 1) - r₂) × Fin m) K,
      (∃ b : PointCoordinates K m (N (m + 1) (d + 1) - r₂), eval b D ≠ 0) ∧
      ∀ b, eval b D ≠ 0 → Function.Surjective (pointEvaluation K b (d + 1)) ∧
        Function.Surjective (pointMultiplication b (d + 1)))
    (hbudget : N (m + 1) (d + 1) ≤ (m + 1) * r₁ + r₂) :
    IdealGenerationAt K (m + 1) (d + 1) (N (m + 2) (d + 1) - (r₁ + r₂)) := by
  have h := ordinary_hyperplane_surjective_from_opens r₁ hres htrace (by omega)
  simpa only [ordinary_hyperplane_point_count r₁ r₂ hr₁ hr₂] using h

end IdealGeneration
