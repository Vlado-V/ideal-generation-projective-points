module

public import IdealGeneration.TripleNormalLeadingMatrix
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Actual edge quadrics and their leading coefficients on the monomial curve. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open Matrix

variable {K V E ι : Type*} [Field K] [Fintype E]
  (ends : E → V × V) (weight : V → ℕ)

/-- The monomial-curve degree of a quadratic edge. -/
def edgeDegree (e : E) : ℕ := weight (ends e).1 + weight (ends e).2

/-- The trace vector quadric represented by its edge coefficient vectors. -/
def edgeQuadric (coeff : E → Fin 3 → K) (a : Fin 3) : MvPolynomial V K :=
  ∑ e, MvPolynomial.C (coeff e a) * (MvPolynomial.X (ends e).1 * MvPolynomial.X (ends e).2)

/-- The same vector quadric on the monomial curve. -/
def edgeCurve (coeff : E → Fin 3 → K) (a : Fin 3) : Polynomial K :=
  ∑ e, Polynomial.monomial (edgeDegree ends weight e) (coeff e a)

theorem eval_edgeCurve (coeff : E → Fin 3 → K) (a : Fin 3) (x : K) :
    (edgeCurve ends weight coeff a).eval x =
      MvPolynomial.eval (fun i => x ^ weight i) (edgeQuadric ends coeff a) := by
  rw [edgeCurve, Polynomial.eval_finsetSum]
  simp [edgeQuadric, edgeDegree, Polynomial.eval_monomial, pow_add]

theorem coeff_edgeCurve (coeff : E → Fin 3 → K) (a : Fin 3) (d : ℕ) :
    (edgeCurve ends weight coeff a).coeff d =
      ∑ e, if edgeDegree ends weight e = d then coeff e a else 0 := by
  simp [edgeCurve, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem natDegree_edgeCurve_le (coeff : E → Fin 3 → K) (a : Fin 3) (d : ℕ)
    (h : ∀ e, d < edgeDegree ends weight e → coeff e a = 0) :
    (edgeCurve ends weight coeff a).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_edgeCurve]
  apply Finset.sum_eq_zero
  intro e _
  split_ifs with he
  · exact h e (he.symm ▸ hn)
  · rfl

theorem coeff_edgeCurve_at_edge (coeff : E → Fin 3 → K) (a : Fin 3) (e : E)
    (hdeg : Function.Injective (edgeDegree ends weight)) :
    (edgeCurve ends weight coeff a).coeff (edgeDegree ends weight e) = coeff e a := by
  classical
  rw [coeff_edgeCurve]
  simp [hdeg.eq_iff]

variable [Infinite K] [Fintype ι] [DecidableEq ι]

/-- A nonsingular weighted leading block gives actual common trace points
interpolating all the supplied edge quadrics. -/
theorem exists_edge_interpolation
    (coeff : ι → E → Fin 3 → K) (lead : ι → E)
    (rowBlock : ι → ℕ) (rowCoordinate : ι → Fin 3) (r c : ι → ℕ)
    (hdeg : Function.Injective (edgeDegree ends weight))
    (hsupport : ∀ j e, edgeDegree ends weight (lead j) < edgeDegree ends weight e → coeff j e = 0)
    (hweight : ∀ i j, (rowBlock i + 1) * edgeDegree ends weight (lead j) ≤ r i + c j)
    (hdet : (Matrix.of fun i j =>
      if r i + c j = (rowBlock i + 1) * edgeDegree ends weight (lead j)
      then coeff j (lead j) (rowCoordinate i) else 0).det ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ (Matrix.of fun i j =>
      MvPolynomial.eval (fun v => (x ^ (rowBlock i + 1)) ^ weight v)
        (edgeQuadric ends (coeff j) (rowCoordinate i))).det ≠ 0 := by
  have htop (i j : ι) :
      (edgeCurve ends weight (coeff j) (rowCoordinate i)).coeff
        (edgeDegree ends weight (lead j)) = coeff j (lead j) (rowCoordinate i) :=
    coeff_edgeCurve_at_edge ends weight (coeff j) (rowCoordinate i) (lead j) hdeg
  obtain ⟨x, hx, hm⟩ := exists_interpolation_of_weightedLeading
    (fun j => edgeCurve ends weight (coeff j)) rowBlock rowCoordinate
    (fun j => edgeDegree ends weight (lead j)) r c
    (fun j a => natDegree_edgeCurve_le ends weight (coeff j) a _
      (fun e he => congrFun (hsupport j e he) a)) hweight
    (by simpa only [htop] using hdet)
  exact ⟨x, hx, by simpa only [eval_edgeCurve] using hm⟩

end IdealGeneration.TripleNormal
