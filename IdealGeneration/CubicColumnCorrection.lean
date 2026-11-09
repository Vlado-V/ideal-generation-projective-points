module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Adding combinations of the unchanged columns preserves the parameter basis. -/

noncomputable section
namespace IdealGeneration

open Module

variable {K : Type*} [Field K] {I : Type*} [Fintype I] [DecidableEq I]

/-- The unchanged columns are coordinate vectors. A changed column has its
own nonzero coordinate and can have other entries only in unchanged rows. -/
theorem correctedColumns_linearIndependent (v : I → I → K) (changed : I → Bool)
    (hunchanged : ∀ j, changed j = false → v j = Pi.single j 1)
    (hchanged : ∀ i, changed i = true → ∀ j, v j i = if j = i then -1 else 0) :
    LinearIndependent K v := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hentry (i : I) : ∑ j, a j * v j i = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun ha i
  have hzero (i : I) (hi : changed i = true) : a i = 0 := by
    have hsum := hentry i
    simp only [hchanged i hi, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
    simpa using hsum
  intro i
  by_cases hi : changed i = true
  · exact hzero i hi
  · have hsum := hentry i
    have he (j : I) : a j * v j i = if j = i then a i else 0 := by
      by_cases hj : changed j = true
      · have hne : j ≠ i := by rintro rfl; contradiction
        simp [hzero j hj, hne]
      · rw [hunchanged j (Bool.eq_false_of_not_eq_true hj)]
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hsum

/-- The corrected coordinate columns give a basis of the full coordinate space. -/
def correctedColumnBasis (v : I → I → K) (changed : I → Bool)
    (hunchanged : ∀ j, changed j = false → v j = Pi.single j 1)
    (hchanged : ∀ i, changed i = true → ∀ j, v j i = if j = i then -1 else 0) :
    Basis I K (I → K) :=
  basisOfLinearIndependentOfCardEqFinrank' v
    (correctedColumns_linearIndependent v changed hunchanged hchanged)
    (Module.finrank_fintype_fun_eq_card K).symm

@[simp] theorem correctedColumnBasis_apply (v : I → I → K) (changed : I → Bool)
    (hunchanged : ∀ j, changed j = false → v j = Pi.single j 1)
    (hchanged : ∀ i, changed i = true → ∀ j, v j i = if j = i then -1 else 0)
    (i : I) : correctedColumnBasis v changed hunchanged hchanged i = v i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := K) v _ _) i

end IdealGeneration
