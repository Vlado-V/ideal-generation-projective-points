module

public import IdealGeneration.TripleNormalConic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact coefficient planes of the degree-ordered conic chords. -/

namespace IdealGeneration.TripleNormal
open scoped Matrix

variable {K : Type*} [Field K]

theorem chordNormal_dot_conic_left (t u : K) :
    chordNormal t u ⬝ᵥ conicVector t = 0 := by
  simp [dotProduct, Fin.sum_univ_three, conicVector, chordNormal]
  ring

theorem chordNormal_dot_conic_right (t u : K) :
    chordNormal t u ⬝ᵥ conicVector u = 0 := by
  simp [dotProduct, Fin.sum_univ_three, conicVector, chordNormal]
  ring

/-- A chord plane is exactly the span of its two endpoint directions. -/
theorem exists_eq_smul_conicVector_add (t u : K) (htu : t ≠ u)
    (w : Fin 3 → K) (hw : chordNormal t u ⬝ᵥ w = 0) :
    ∃ a b : K, w = a • conicVector t + b • conicVector u := by
  let b := (w 1 - t * w 0) / (u - t)
  let a := w 0 - b
  have hb : (u - t) * b = w 1 - t * w 0 :=
    mul_div_cancel₀ _ (sub_ne_zero.mpr htu.symm)
  have h₀ : a + b = w 0 := sub_add_cancel _ _
  have h₁ : a * t + b * u = w 1 := by
    dsimp only [a]
    linear_combination hb
  have h₂ : a * t ^ 2 + b * u ^ 2 = w 2 := by
    calc
      _ = (t + u) * (a * t + b * u) - t * u * (a + b) := by ring
      _ = _ := by
        rw [h₀, h₁]
        simp [dotProduct, Fin.sum_univ_three, chordNormal] at hw
        linear_combination -hw
  refine ⟨a, b, ?_⟩
  funext j
  fin_cases j
  · simpa [conicVector] using h₀.symm
  · simpa [conicVector] using h₁.symm
  · simpa [conicVector] using h₂.symm

end IdealGeneration.TripleNormal
