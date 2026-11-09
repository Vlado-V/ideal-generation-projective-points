module

public import IdealGeneration.RepresentativeNormalization
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Lifting trace principal opens to homogeneous representatives

Clearing a common denominator lifts any affine trace polynomial to a
polynomial in all homogeneous coordinates. Its nonvanishing also forces
the final coordinate of every representative to be nonzero.
-/

noncomputable section
namespace IdealGeneration.HomogeneousTraceOpen
open MvPolynomial

variable {K : Type*} [Field K] {n q : ℕ}

/-- Flat homogeneous coordinates for an ordered family of trace points. -/
abbrev Coordinates (K : Type*) (n q : ℕ) := Fin q × Fin (n + 1) → K

/-- Normalize every point using its final homogeneous coordinate. -/
def normalize (z : Coordinates K n q) : PointCoordinates K n q :=
  normalizedCoordinates (fun i j => z (i, j))

/-- The product of the final homogeneous coordinates. -/
def denominator (n q : ℕ) : MvPolynomial (Fin q × Fin (n + 1)) K :=
  ∏ i : Fin q, X (i, Fin.last n)

/-- The numerator of one affine coordinate after passage to the common denominator. -/
def numerator (ij : Fin q × Fin n) : MvPolynomial (Fin q × Fin (n + 1)) K :=
  X (ij.1, ij.2.castSucc) * ∏ i ∈ Finset.univ.erase ij.1, X (i, Fin.last n)

@[simp] theorem eval_denominator (z : Coordinates K n q) :
    eval z (denominator n q) = ∏ i : Fin q, z (i, Fin.last n) := by
  simp [denominator]

theorem eval_denominator_ne_zero_iff (z : Coordinates K n q) :
    eval z (denominator n q) ≠ 0 ↔ ∀ i, z (i, Fin.last n) ≠ 0 := by
  simp [denominator, Finset.prod_ne_zero_iff]

theorem eval_numerator (z : Coordinates K n q)
    (hz : ∀ i, z (i, Fin.last n) ≠ 0) (ij : Fin q × Fin n) :
    eval z (numerator ij) = eval z (denominator n q) * normalize z ij := by
  classical
  simp only [numerator, map_mul, map_prod, eval_X, eval_denominator]
  change z (ij.1, ij.2.castSucc) * (∏ i ∈ Finset.univ.erase ij.1, z (i, Fin.last n)) =
    (∏ i : Fin q, z (i, Fin.last n)) *
      (z (ij.1, ij.2.castSucc) / z (ij.1, Fin.last n))
  rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin q => z (i, Fin.last n))
    (Finset.mem_univ ij.1)]
  field_simp [hz ij.1]

/-- A power of the common denominator clears the denominators of any affine
polynomial evaluated on the normalized representatives. -/
theorem exists_cleared_polynomial (D : MvPolynomial (Fin q × Fin n) K) :
    ∃ (P : MvPolynomial (Fin q × Fin (n + 1)) K) (N : ℕ),
      ∀ z : Coordinates K n q, (∀ i, z (i, Fin.last n) ≠ 0) →
        eval z P = eval z (denominator n q) ^ N * eval (normalize z) D := by
  classical
  induction D using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C a, 0, ?_⟩
      intro z hz
      simp
  | add D E hD hE =>
      obtain ⟨P, N, hP⟩ := hD
      obtain ⟨Q, M, hQ⟩ := hE
      refine ⟨P * denominator n q ^ M + Q * denominator n q ^ N, N + M, ?_⟩
      intro z hz
      simp only [map_add, map_mul, map_pow, hP z hz, hQ z hz, pow_add]
      ring
  | mul_X D ij hD =>
      obtain ⟨P, N, hP⟩ := hD
      refine ⟨P * numerator ij, N + 1, ?_⟩
      intro z hz
      simp only [map_mul, hP z hz, eval_numerator z hz ij, eval_X, pow_succ]
      ring

/-- Place normalized affine representatives in the full coordinate space. -/
def chartCoordinates (a : PointCoordinates K n q) : Coordinates K n q :=
  fun ij => chartPoint K a ij.1 ij.2

@[simp] theorem chartCoordinates_last (a : PointCoordinates K n q) (i : Fin q) :
    chartCoordinates a (i, Fin.last n) = 1 := by
  simp [chartCoordinates]

@[simp] theorem normalize_chartCoordinates (a : PointCoordinates K n q) :
    normalize (chartCoordinates a) = a := by
  funext ij
  simp [normalize, normalizedCoordinates, chartCoordinates]

@[simp] theorem eval_denominator_chartCoordinates (a : PointCoordinates K n q) :
    eval (chartCoordinates a) (denominator n q) = 1 := by
  simp

/-- Every nonempty affine principal open pulls back to a nonempty homogeneous
principal open on which every representative can be normalized. -/
theorem exists_homogeneous_trace_open (D : MvPolynomial (Fin q × Fin n) K)
    (hD : ∃ a : PointCoordinates K n q, eval a D ≠ 0) :
    ∃ Δ : MvPolynomial (Fin q × Fin (n + 1)) K,
      (∃ z : Coordinates K n q, eval z Δ ≠ 0) ∧
      ∀ z : Coordinates K n q, eval z Δ ≠ 0 →
        (∀ i, z (i, Fin.last n) ≠ 0) ∧ eval (normalize z) D ≠ 0 := by
  obtain ⟨P, N, hP⟩ := exists_cleared_polynomial D
  refine ⟨denominator n q * P, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hD
    refine ⟨chartCoordinates a, ?_⟩
    have hz : ∀ i, chartCoordinates a (i, Fin.last n) ≠ 0 := by simp
    simpa only [map_mul, hP _ hz, eval_denominator_chartCoordinates, one_pow, one_mul,
      normalize_chartCoordinates] using ha
  · intro z hz
    have hparts : eval z (denominator n q) ≠ 0 ∧ eval z P ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hz
    have hlast := (eval_denominator_ne_zero_iff z).mp hparts.1
    refine ⟨hlast, ?_⟩
    rw [hP z hlast] at hparts
    exact (mul_ne_zero_iff.mp hparts.2).2

end IdealGeneration.HomogeneousTraceOpen
