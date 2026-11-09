module

public import IdealGeneration.Multiplication
public import IdealGeneration.ScalarInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The target theorem

These definitions state the paper's assertion on an affine chart of the
configuration space of ordered projective points. The affine dimension `n`
corresponds to `n+1` variables in the paper. Nonvanishing of a parameter
polynomial specifies a nonempty principal Zariski open set.

The general assertion `IdealGenerationConjecture` is a target statement.
This file does not assert that it has been proved.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable (K : Type*) [Field K]

/-- Maximal-rank multiplication and scalar postulation on a nonempty open set. -/
def IdealGenerationAt (n d p : ℕ) : Prop :=
  ∃ Δ : MvPolynomial (Fin p × Fin n) K,
    (∃ a : PointCoordinates K n p, eval a Δ ≠ 0) ∧
    ∀ a : PointCoordinates K n p, eval a Δ ≠ 0 →
      DistinctPoints K a ∧
      (∀ j, pointHilbertFunction K a j = min ((n + j).choose j) p) ∧
      HasMaximalRank (pointMultiplication a d)

/-- The maximal-rank assertion of Theorem 1.1, using `n+1` variables. -/
def IdealGenerationConjecture : Prop :=
  ∀ (n d p : ℕ), 1 ≤ n → 2 ≤ d →
    (n + d - 1).choose (d - 1) ≤ p → p < (n + d).choose d →
    IdealGenerationAt K n d p

end IdealGeneration
