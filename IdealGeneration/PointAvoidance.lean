module

public import IdealGeneration.ScalarInterpolation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Principal-open conditions can be imposed with every point off a fixed hyperplane. -/

noncomputable section
namespace IdealGeneration
open MvPolynomial

variable {K : Type*} [Field K]

/-- The first coordinate of every point is nonzero on this principal open. -/
def offHyperplanePolynomial (n p : ℕ) : MvPolynomial (Fin p × Fin (n + 1)) K :=
  ∏ i : Fin p, X (i, 0)

theorem offHyperplanePolynomial_ne_zero (n p : ℕ) :
    offHyperplanePolynomial (K := K) n p ≠ 0 := by
  have h : eval (fun _ => (1 : K)) (offHyperplanePolynomial (K := K) n p) = 1 := by
    simp [offHyperplanePolynomial]
  intro hz
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem eval_offHyperplanePolynomial_ne_zero_iff {n p : ℕ}
    (a : PointCoordinates K (n + 1) p) :
    eval a (offHyperplanePolynomial (K := K) n p) ≠ 0 ↔ ∀ i, a (i, 0) ≠ 0 := by
  simp [offHyperplanePolynomial, Finset.prod_ne_zero_iff]

/-- Any nonempty principal open meets the locus of points off the hyperplane. -/
theorem principal_open_meets_off_hyperplane [Infinite K] {n p : ℕ}
    (D : MvPolynomial (Fin p × Fin (n + 1)) K)
    (hD : ∃ a : PointCoordinates K (n + 1) p, eval a D ≠ 0) :
    ∃ a : PointCoordinates K (n + 1) p, eval a D ≠ 0 ∧ ∀ i, a (i, 0) ≠ 0 := by
  have hDn : D ≠ 0 := by
    obtain ⟨a, ha⟩ := hD
    intro hz
    simp [hz] at ha
  have hprod : D * offHyperplanePolynomial (K := K) n p ≠ 0 :=
    mul_ne_zero hDn (offHyperplanePolynomial_ne_zero n p)
  have hex : ∃ a : PointCoordinates K (n + 1) p,
      eval a (D * offHyperplanePolynomial (K := K) n p) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  obtain ⟨a, ha⟩ := hex
  have hp : eval a D ≠ 0 ∧ eval a (offHyperplanePolynomial (K := K) n p) ≠ 0 := by
    simpa using ha
  exact ⟨a, hp.1, (eval_offHyperplanePolynomial_ne_zero_iff a).mp hp.2⟩

/-- Two independently witnessed principal conditions have a common point. -/
theorem principal_opens_meet [Infinite K] {ι : Type*}
    (D E : MvPolynomial ι K) (hD : ∃ a, eval a D ≠ 0) (hE : ∃ a, eval a E ≠ 0) :
    ∃ a, eval a D ≠ 0 ∧ eval a E ≠ 0 := by
  have hDn : D ≠ 0 := by obtain ⟨a, ha⟩ := hD; intro hz; simp [hz] at ha
  have hEn : E ≠ 0 := by obtain ⟨a, ha⟩ := hE; intro hz; simp [hz] at ha
  have hp := mul_ne_zero hDn hEn
  have hex : ∃ a, eval a (D * E) ≠ 0 := by
    by_contra! h
    exact hp (MvPolynomial.funext h)
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, by simpa using ha⟩

end IdealGeneration
