module

public import IdealGeneration.Points
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Reducedness of the homogeneous ideals of chart point configurations. -/

noncomputable section
namespace IdealGeneration

open MvPolynomial

variable {K : Type*} [Field K] {n p : ℕ}

/-- Parametrize the affine cone over one chart point by a single variable. -/
def singlePointConeParam (u : Fin n → K) : Poly K (n + 1) →+* Polynomial K :=
  let v : Fin (n + 1) → K := Fin.snoc u 1
  eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)

/-- The homogeneous equations of the point cut out its parametrized cone. -/
theorem singlePointIdeal_eq_ker (u : Fin n → K) :
    singlePointIdeal K u = RingHom.ker (singlePointConeParam u) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    simp [singlePointConeParam]
  · intro f hf
    let v : Fin (n + 1) → K := Fin.snoc u 1
    let q : Fin (n + 1) → Poly K (n + 1) := fun i => C (v i) * X (Fin.last n)
    have hq : ∀ i, X i - q i ∈ singlePointIdeal K u := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [q, v]
      · exact Ideal.subset_span ⟨j, by simp [q, v]⟩
    let specialize : Polynomial K →+* Poly K (n + 1) :=
      Polynomial.eval₂RingHom C (X (Fin.last n))
    have hcomp : specialize.comp (singlePointConeParam u) = eval₂Hom C q := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [specialize, singlePointConeParam]
      · intro i
        simp [specialize, singlePointConeParam, q, v]
    have hzero : eval₂ C q f = 0 := by
      change (eval₂Hom C q) f = 0
      rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]
    simpa [hzero] using sub_substitution_mem (singlePointIdeal K u) q hq f

/-- Each chart point defines a prime homogeneous ideal. -/
theorem singlePointIdeal_isPrime (u : Fin n → K) : (singlePointIdeal K u).IsPrime := by
  rw [singlePointIdeal_eq_ker]
  exact RingHom.ker_isPrime _

/-- The intersection of the chart point ideals is radical. -/
theorem pointIdeal_isRadical (a : PointCoordinates K n p) : (pointIdeal K a).IsRadical :=
  Ideal.isRadical_iInf _ fun i => (singlePointIdeal_isPrime (fun j => a (i, j))).isRadical

/-- The homogeneous coordinate ring of the chart configuration is reduced. -/
theorem pointIdeal_quotient_isReduced (a : PointCoordinates K n p) :
    IsReduced (Poly K (n + 1) ⧸ pointIdeal K a) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (pointIdeal_isRadical a)

end IdealGeneration
