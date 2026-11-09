module

public import IdealGeneration.CubicSupportedHomogeneous

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Coefficient coordinates for the supported cubic kernel. -/

namespace IdealGeneration.CubicSupported

/-- All coefficients of a cubic with positive normal degree. -/
abbrev Coefficients (K : Type*) (m : ℕ) :=
  (Fin 4 → K) × (Fin m → Fin 3 → K) × (Fin m → Fin 2 → K) × (Edge m → Fin 2 → K)

section Linearity

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem upperCoefficient_add
    (a a' : Fin m → Fin 2 → R) (b b' : Edge m → Fin 2 → R)
    (i j : Fin m) (k : Fin 2) :
    upperCoefficient (a + a') (b + b') i j k =
      upperCoefficient a b i j k + upperCoefficient a' b' i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h, Pi.add_apply]
  · by_cases hij : i = j <;> simp [upperCoefficient, h, hij, Pi.add_apply]

private theorem upperCoefficient_mul (r : R)
    (a : Fin m → Fin 2 → R) (b : Edge m → Fin 2 → R)
    (i j : Fin m) (k : Fin 2) :
    upperCoefficient (fun i k => r * a i k) (fun e k => r * b e k) i j k =
      r * upperCoefficient a b i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h]
  · by_cases hij : i = j <;> simp [upperCoefficient, h, hij]

private theorem cubicValue_add
    (C C' : Fin 4 → R) (B B' : Fin m → Fin 3 → R)
    (a a' : Fin m → Fin 2 → R) (b b' : Edge m → Fin 2 → R)
    (s t : R) (y : Fin m → R) :
    cubicValue (C + C') (B + B') (a + a') (b + b') s t y =
      cubicValue C B a b s t y + cubicValue C' B' a' b' s t y := by
  simp only [cubicValue, normalCubic, normalQuadratic, traceQuadratic, Pi.add_apply,
    upperCoefficient_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem cubicValue_mul (r : R)
    (C : Fin 4 → R) (B : Fin m → Fin 3 → R) (a : Fin m → Fin 2 → R) (b : Edge m → Fin 2 → R)
    (s t : R) (y : Fin m → R) :
    cubicValue (fun q => r * C q) (fun i q => r * B i q) (fun i k => r * a i k)
      (fun e k => r * b e k) s t y = r * cubicValue C B a b s t y := by
  have hC : normalCubic (fun q => r * C q) s t = r * normalCubic C s t := by
    unfold normalCubic
    ring
  have hB (i : Fin m) : normalQuadratic (fun q => r * B i q) s t =
      r * normalQuadratic (B i) s t := by
    unfold normalQuadratic
    ring
  have hS : (∑ i, y i * normalQuadratic (fun q => r * B i q) s t) =
      r * ∑ i, y i * normalQuadratic (B i) s t := by
    simp only [hB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hQ (k : Fin 2) :
      traceQuadratic (fun i j => upperCoefficient (fun i l => r * a i l)
        (fun e l => r * b e l) i j k) y =
      r * traceQuadratic (fun i j => upperCoefficient a b i j k) y := by
    simp only [traceQuadratic, upperCoefficient_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [cubicValue, hC, hS, hQ]
  ring

end Linearity

section PolynomialMap

open MvPolynomial
variable {K : Type*} [Field K] {m : ℕ}

/-- The coefficient map produces the actual homogeneous polynomial. -/
noncomputable def coefficientPolynomial : Coefficients K m →ₗ[K] Poly K (2 + m) where
  toFun u := polynomial u.1 u.2.1 u.2.2.1 u.2.2.2
  map_add' u v := by
    change polynomial (u.1 + v.1) (u.2.1 + v.2.1) (u.2.2.1 + v.2.2.1)
      (u.2.2.2 + v.2.2.2) = _
    simp only [polynomial, Pi.add_apply, map_add]
    apply cubicValue_add
  map_smul' r u := by
    change polynomial (r • u.1) (r • u.2.1) (r • u.2.2.1) (r • u.2.2.2) =
      r • polynomial u.1 u.2.1 u.2.2.1 u.2.2.2
    simp only [polynomial, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def,
      MvPolynomial.algebraMap_eq]
    apply cubicValue_mul

@[simp] theorem coefficientPolynomial_apply (u : Coefficients K m) :
    coefficientPolynomial u = polynomial u.1 u.2.1 u.2.2.1 u.2.2.2 := rfl

namespace Parameters

variable (P : Parameters K m)

/-- Every vertex slot and every valid edge slot labels an actual cone point. -/
abbrev ConeLabel := (Fin m × Fin 2) ⊕ {p : Edge m × Fin 2 // P.EdgeSlot p.1 p.2}

def conePoint : P.ConeLabel → Fin (2 + m) → K
  | .inl (i, d) => P.vertexPoint i d
  | .inr e => P.edgePoint e.val.1 e.val.2

/-- Evaluate a coefficient cubic at all supported cone points. -/
noncomputable def coefficientEvaluation : Coefficients K m →ₗ[K] (P.ConeLabel → K) where
  toFun u a := eval (P.conePoint a) (coefficientPolynomial u)
  map_add' u v := by
    funext a
    change eval (P.conePoint a) (coefficientPolynomial (u + v)) = _
    simp only [map_add, Pi.add_apply]
  map_smul' r u := by funext a; simp

/-- The supported cone kernel in coefficient coordinates. -/
noncomputable def coefficientKernel : Submodule K (Coefficients K m) :=
  P.coefficientEvaluation.ker

@[simp] theorem mem_coefficientKernel (u : Coefficients K m) :
    u ∈ P.coefficientKernel ↔ ∀ a, eval (P.conePoint a) (coefficientPolynomial u) = 0 := by
  rw [coefficientKernel, LinearMap.mem_ker]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

/-- The deterministic local solves land in the actual cone evaluation kernel. -/
noncomputable def coefficientLift (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) : P.coefficientKernel := by
  refine ⟨(C, B, P.diagonalLift C B, P.offDiagonalLift C B z), (P.mem_coefficientKernel _).2 ?_⟩
  intro a
  cases a with
  | inl v => exact P.liftPolynomial_vertex C B z v.1 v.2
  | inr e => exact P.liftPolynomial_edge C B z e.val.1 e.val.2 e.property

/-- Project a kernel cubic onto its two highest normal degrees. -/
def topProjection : P.coefficientKernel →ₗ[K] ((Fin 4 → K) × (Fin m → Fin 3 → K)) where
  toFun u := (u.val.1, u.val.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection onto the `C,B` coefficients is onto, as required in B.2. -/
theorem topProjection_surjective : Function.Surjective P.topProjection := by
  intro p
  exact ⟨P.coefficientLift p.1 p.2 0, rfl⟩

end Parameters
end PolynomialMap
end IdealGeneration.CubicSupported
