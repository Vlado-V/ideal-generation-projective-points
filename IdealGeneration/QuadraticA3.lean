module

public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normal-degree elimination in the quadratic construction

The identity in Appendix A, equation (A.3), cancels the pure normal terms
and the terms of normal degree two. The remaining expression is the
normal-linear polynomial with the displayed coefficient pair. The proof
works in an arbitrary commutative ring and therefore also after any
coefficient-algebra extension.
-/

namespace IdealGeneration.QuadraticA3

variable {R : Type*} [CommRing R]

/-- The expanded polynomial identity underlying equation (A.3). -/
theorem normalElimination_expanded
    (s t U₁ V₁ U₂ V₂ U₃ V₃ Qs Qt us vs ut vt : R)
    (hQ : s * Qs + t * Qt = 0) :
    -(s ^ 2 + s * U₁ + t * V₁) * us -
      (s * t + s * U₂ + t * V₂) * (vs + ut) -
      (t ^ 2 + s * U₃ + t * V₃) * vt +
      s * (Qs + s * us + t * vs) + t * (Qt + s * ut + t * vt) =
    s * (-U₁ * us - U₂ * (vs + ut) - U₃ * vt) +
      t * (-V₁ * us - V₂ * (vs + ut) - V₃ * vt) := by
  linear_combination hQ

/-- Equation (A.3) in terms of arbitrary chosen quadratic lifts and two
kernel elements, with their pure normal parts specified separately. -/
theorem normalElimination_of_lifts
    (s t U₁ V₁ U₂ V₂ U₃ V₃ Qs Qt us vs ut vt K₁ K₂ K₃ ks kt : R)
    (hK₁ : K₁ = s ^ 2 + s * U₁ + t * V₁)
    (hK₂ : K₂ = s * t + s * U₂ + t * V₂)
    (hK₃ : K₃ = t ^ 2 + s * U₃ + t * V₃)
    (hks : ks = Qs + s * us + t * vs)
    (hkt : kt = Qt + s * ut + t * vt)
    (hQ : s * Qs + t * Qt = 0) :
    -K₁ * us - K₂ * (vs + ut) - K₃ * vt + s * ks + t * kt =
      s * (-U₁ * us - U₂ * (vs + ut) - U₃ * vt) +
        t * (-V₁ * us - V₂ * (vs + ut) - V₃ * vt) := by
  rw [hK₁, hK₂, hK₃, hks, hkt]
  exact normalElimination_expanded s t U₁ V₁ U₂ V₂ U₃ V₃ Qs Qt us vs ut vt hQ

end IdealGeneration.QuadraticA3
