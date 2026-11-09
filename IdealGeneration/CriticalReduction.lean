module

public import IdealGeneration.PointMonotonicity
public import IdealGeneration.MultiplicationOpen
public import IdealGeneration.Numerics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Reduction to the two critical point counts

Injection witnesses propagate to larger configurations. Surjection witnesses
with scalar interpolation propagate to smaller configurations. Openness turns
both constructions into assertions for general reduced points.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K] {n d p pI pS : ℕ}

/-- An injective witness proves the general-points assertion without a scalar
postulation hypothesis on the witness itself. -/
theorem idealGenerationAt_of_injective_witness [CharZero K] (hn : 1 ≤ n)
    (a₀ : PointCoordinates K n p) (h₀ : Function.Injective (pointMultiplication a₀ d)) :
    IdealGenerationAt K n d p := by
  obtain ⟨D, hD, hgoodD⟩ := pointMultiplication_injective_principal_open a₀ h₀
  obtain ⟨E, hE, hgoodE⟩ := generic_pointHilbertFunction (K := K) hn p
  have hDne : D ≠ 0 := by intro hz; simp [hz] at hD
  have hEne : E ≠ 0 := by
    obtain ⟨a, ha⟩ := hE
    intro hz
    simp [hz] at ha
  have hprod : D * E ≠ 0 := mul_ne_zero hDne hEne
  have hex : ∃ a : PointCoordinates K n p, eval a (D * E) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  refine ⟨D * E, hex, fun a ha => ?_⟩
  have hparts : eval a D ≠ 0 ∧ eval a E ≠ 0 := by simpa using ha
  obtain ⟨hdistinct, hpost⟩ := hgoodE a hparts.2
  exact ⟨hdistinct, hpost, Or.inl (hgoodD a hparts.1)⟩

/-- Extend an ordered configuration by arbitrary zero-coordinate points. -/
def extendPoints (a : PointCoordinates K n pI) (p : ℕ) : PointCoordinates K n p :=
  fun ij => if h : ij.1.val < pI then a (⟨ij.1.val, h⟩, ij.2) else 0

@[simp] theorem restrict_extendPoints (a : PointCoordinates K n pI) (h : pI ≤ p) :
    restrictPoints (extendPoints a p) (Fin.castLE h) = a := by
  funext ij
  simp [restrictPoints, extendPoints, ij.1.isLt]

/-- General injectivity propagates upwards from any one injection witness. -/
theorem idealGenerationAt_above_injective_witness [CharZero K] (hn : 1 ≤ n)
    (aI : PointCoordinates K n pI) (hI : Function.Injective (pointMultiplication aI d))
    (hp : pI ≤ p) : IdealGenerationAt K n d p := by
  apply idealGenerationAt_of_injective_witness hn (extendPoints aI p)
  apply pointMultiplication_injective_of_restriction (extendPoints aI p) (Fin.castLE hp)
  rw [restrict_extendPoints aI hp]
  exact hI

/-- Restricting an interpolating configuration preserves scalar interpolation. -/
theorem pointEvaluation_surjective_restriction
    (a : PointCoordinates K n pS) (hp : p ≤ pS)
    (h : Function.Surjective (pointEvaluation K a d)) :
    Function.Surjective (pointEvaluation K (restrictPoints a (Fin.castLE hp)) d) := by
  intro y
  let yfull : Fin pS → K := fun i => if hi : i.val < p then y ⟨i.val, hi⟩ else 0
  obtain ⟨f, hf⟩ := h yfull
  refine ⟨f, ?_⟩
  ext i
  have hi := congrFun hf (Fin.castLE hp i)
  simpa [pointEvaluation_apply, yfull, i.isLt] using hi

/-- General surjectivity propagates downwards from a scalar-interpolating witness. -/
theorem idealGenerationAt_below_surjective_witness [CharZero K] (hn : 1 ≤ n)
    (aS : PointCoordinates K n pS)
    (hscalar : Function.Surjective (pointEvaluation K aS d))
    (hS : Function.Surjective (pointMultiplication aS d))
    (hp : p ≤ pS) : IdealGenerationAt K n d p := by
  apply idealGenerationAt_of_witness hn (restrictPoints aS (Fin.castLE hp))
  · exact pointEvaluation_surjective_restriction aS hp hscalar
  · exact Or.inr (pointMultiplication_surjective_on_restriction aS (Fin.castLE hp) hscalar hS)

/-- Adjacent injection and surjection witness counts cover every point count. -/
theorem idealGenerationAt_of_adjacent_witnesses [CharZero K] (hn : 1 ≤ n)
    (aI : PointCoordinates K n pI) (hI : Function.Injective (pointMultiplication aI d))
    (aS : PointCoordinates K n pS)
    (hscalar : Function.Surjective (pointEvaluation K aS d))
    (hS : Function.Surjective (pointMultiplication aS d))
    (hgap : pI ≤ pS + 1) (p : ℕ) : IdealGenerationAt K n d p := by
  by_cases hp : pI ≤ p
  · exact idealGenerationAt_above_injective_witness hn aI hI hp
  · exact idealGenerationAt_below_surjective_witness hn aS hscalar hS (by omega)

/-- Lemma 2.1. The floor and ceiling critical ideal dimensions suffice for
all point counts, once their injection/surjection witnesses are supplied. -/
theorem reduction_to_critical_counts [CharZero K] (hn : 1 ≤ n)
    (hI : ∃ aI : PointCoordinates K n (N (n + 1) d - lowerCritical (n + 1) d),
      Function.Injective (pointMultiplication aI d))
    (hS : ∃ aS : PointCoordinates K n (N (n + 1) d - upperCritical (n + 1) d),
      Function.Surjective (pointEvaluation K aS d) ∧
      Function.Surjective (pointMultiplication aS d)) :
    ∀ p, IdealGenerationAt K n d p := by
  obtain ⟨aI, haI⟩ := hI
  obtain ⟨aS, hscalar, haS⟩ := hS
  intro p
  apply idealGenerationAt_of_adjacent_witnesses hn aI haI aS hscalar haS
  have hgap := upperCritical_le_lowerCritical_add_one (n + 1) d
  omega

end IdealGeneration
