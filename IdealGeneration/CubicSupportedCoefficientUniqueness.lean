module

public import IdealGeneration.CubicSupportedHomogeneous

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Recovering the coefficients of the supported cubic from actual evaluations. -/

namespace IdealGeneration.CubicSupported

open MvPolynomial

variable {K : Type*} [Field K]

private theorem normalLinear_coefficients_eq_zero (a : Fin 2 → K)
    (h : ∀ t, normalLinear a 1 t = 0) : a = 0 := by
  have h₀ : a 0 = 0 := by simpa [normalLinear] using h 0
  have h₁ : a 1 = 0 := by simpa [normalLinear, h₀] using h 1
  funext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem normalQuadratic_coefficients_eq_zero (htwo : (2 : K) ≠ 0) (a : Fin 3 → K)
    (h : ∀ t, normalQuadratic a 1 t = 0) : a = 0 := by
  have h₀ := h 0
  have hPos := h 1
  have hNeg := h (-1)
  norm_num [normalQuadratic] at h₀ hPos hNeg
  have h₁' : (2 : K) * a 1 = 0 := by linear_combination hPos - hNeg
  have h₂' : (2 : K) * a 2 = 0 := by linear_combination hPos + hNeg - 2 * h₀
  have h₁ : a 1 = 0 := (mul_eq_zero.mp h₁').resolve_left htwo
  have h₂ : a 2 = 0 := (mul_eq_zero.mp h₂').resolve_left htwo
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

private theorem normalCubic_coefficients_eq_zero
    (htwo : (2 : K) ≠ 0) (hsix : (6 : K) ≠ 0) (a : Fin 4 → K)
    (h : ∀ t, normalCubic a 1 t = 0) : a = 0 := by
  have h₀ := h 0
  have hPos := h 1
  have hNeg := h (-1)
  have hTwo := h 2
  norm_num [normalCubic] at h₀ hPos hNeg hTwo
  have h₃' : (6 : K) * a 3 = 0 := by
    linear_combination hTwo - 3 * hPos - hNeg + 3 * h₀
  have h₃ : a 3 = 0 := (mul_eq_zero.mp h₃').resolve_left hsix
  have h₁' : (2 : K) * a 1 = 0 := by linear_combination hPos - hNeg - 2 * h₃
  have h₂' : (2 : K) * a 2 = 0 := by linear_combination hPos + hNeg - 2 * h₀
  have h₁ : a 1 = 0 := (mul_eq_zero.mp h₁').resolve_left htwo
  have h₂ : a 2 = 0 := (mul_eq_zero.mp h₂').resolve_left htwo
  funext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃

/-- The actual polynomial determines all four families of supported cubic coefficients. -/
theorem polynomial_coefficients_eq_zero_of_ne {m : ℕ}
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K)
    (h : polynomial C₀ B diagonal offDiagonal = 0) :
    C₀ = 0 ∧ B = 0 ∧ diagonal = 0 ∧ offDiagonal = 0 := by
  have hValue (s t : K) (y : Fin m → K) :
      cubicValue C₀ B diagonal offDiagonal s t y = 0 := by
    have hEval := congrArg (eval (Fin.addCases ![s, t] y)) h
    simpa [eval_polynomial] using hEval
  have hC : C₀ = 0 := normalCubic_coefficients_eq_zero h₂ h₆ C₀ (fun t => by
    simpa [cubicValue, traceQuadratic] using hValue 1 t 0)
  have hVertex (i : Fin m) (t μ : K) :
      μ * normalQuadratic (B i) 1 t + μ ^ 2 * normalLinear (diagonal i) 1 t = 0 := by
    have hEval := hValue 1 t (vertexSupport i μ)
    rw [cubicValue_vertex] at hEval
    simpa [hC, normalCubic, normalLinear] using hEval
  have hVertexParts (i : Fin m) (t : K) :
      normalQuadratic (B i) 1 t = 0 ∧ normalLinear (diagonal i) 1 t = 0 := by
    have hPos := hVertex i t 1
    have hNeg := hVertex i t (-1)
    norm_num at hPos hNeg
    have hB' : (2 : K) * normalQuadratic (B i) 1 t = 0 := by
      linear_combination hPos - hNeg
    have hDiag' : (2 : K) * normalLinear (diagonal i) 1 t = 0 := by
      linear_combination hPos + hNeg
    exact ⟨(mul_eq_zero.mp hB').resolve_left h₂,
      (mul_eq_zero.mp hDiag').resolve_left h₂⟩
  have hB : B = 0 := by
    funext i
    exact normalQuadratic_coefficients_eq_zero h₂ (B i) (fun t => (hVertexParts i t).1)
  have hDiagonal : diagonal = 0 := by
    funext i
    exact normalLinear_coefficients_eq_zero (diagonal i) (fun t => (hVertexParts i t).2)
  have hOffDiagonal : offDiagonal = 0 := by
    funext e
    apply normalLinear_coefficients_eq_zero
    intro t
    have hEval := hValue 1 t (edgeSupport e 1 1)
    rw [cubicValue_edge] at hEval
    simpa [hC, hB, hDiagonal, normalCubic, normalQuadratic, normalLinear] using hEval
  exact ⟨hC, hB, hDiagonal, hOffDiagonal⟩

/-- Coefficient recovery over characteristic zero. -/
theorem polynomial_coefficients_eq_zero [CharZero K] {m : ℕ}
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K)
    (h : polynomial C₀ B diagonal offDiagonal = 0) :
    C₀ = 0 ∧ B = 0 ∧ diagonal = 0 ∧ offDiagonal = 0 :=
  polynomial_coefficients_eq_zero_of_ne (by norm_num) (by norm_num)
    C₀ B diagonal offDiagonal h

end IdealGeneration.CubicSupported
