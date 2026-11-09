module

public import IdealGeneration.CubicSupportedGraph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Homogeneity and normal-ideal membership of the supported cubic construction. -/

namespace IdealGeneration.CubicSupported

open MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- Every supported cubic is homogeneous of degree three. -/
theorem polynomial_isHomogeneous (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K) :
    (polynomial C₀ B diagonal offDiagonal).IsHomogeneous 3 := by
  let s : Poly K (2 + m) := X (Fin.castAdd m 0)
  let t : Poly K (2 + m) := X (Fin.castAdd m 1)
  let y : Fin m → Poly K (2 + m) := fun i => X (Fin.natAdd 2 i)
  have hs : s.IsHomogeneous 1 := isHomogeneous_X K _
  have ht : t.IsHomogeneous 1 := isHomogeneous_X K _
  have hy (i : Fin m) : (y i).IsHomogeneous 1 := isHomogeneous_X K _
  have hC : (normalCubic (fun q => C (C₀ q)) s t).IsHomogeneous 3 := by
    unfold normalCubic
    exact ((((hs.pow 3).C_mul _).add (((hs.pow 2).C_mul _).mul ht)).add
      ((hs.C_mul _).mul (ht.pow 2))).add ((ht.pow 3).C_mul _)
  have hB (i : Fin m) :
      (normalQuadratic (fun q => C (B i q)) s t).IsHomogeneous 2 := by
    unfold normalQuadratic
    exact (((hs.pow 2).C_mul _).add ((hs.C_mul _).mul ht)).add ((ht.pow 2).C_mul _)
  have hsum : (∑ i, y i * normalQuadratic (fun q => C (B i q)) s t).IsHomogeneous 3 :=
    IsHomogeneous.sum _ _ _ (fun i _ => (hy i).mul (hB i))
  have htrace (k : Fin 2) :
      (traceQuadratic (fun i j =>
        upperCoefficient (fun i l => C (diagonal i l))
          (fun e l => C (offDiagonal e l)) i j k) y).IsHomogeneous 2 := by
    unfold traceQuadratic
    apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    simpa only [map_upperCoefficient] using
      ((isHomogeneous_C (Fin (2 + m)) (upperCoefficient diagonal offDiagonal i j k)).mul
        (hy i)).mul (hy j)
  unfold polynomial cubicValue
  exact ((hC.add hsum).add (hs.mul (htrace 0))).add (ht.mul (htrace 1))

/-- Setting both normal variables to zero annihilates the supported cubic. -/
@[simp] theorem polynomial_coneRestrict_zero
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K) :
    coneRestrict K 2 m (polynomial C₀ B diagonal offDiagonal) = 0 := by
  simp [polynomial, cubicValue, normalCubic, normalQuadratic]

/-- The supported cubic belongs to the ideal of the two normal coordinates. -/
theorem polynomial_mem_coneNormalIdeal
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K) :
    polynomial C₀ B diagonal offDiagonal ∈ coneNormalIdeal K 2 m :=
  (coneRestrict_eq_zero_iff K 2 m _).mp
    (polynomial_coneRestrict_zero C₀ B diagonal offDiagonal)

namespace Parameters

variable (P : Parameters K m)

/-- The primitive-data lift is an actual homogeneous cubic. -/
theorem liftPolynomial_isHomogeneous
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    (P.liftPolynomial C₀ B z).IsHomogeneous 3 :=
  polynomial_isHomogeneous C₀ B (P.diagonalLift C₀ B) (P.offDiagonalLift C₀ B z)

/-- The primitive-data lift restricts to zero on the trace space. -/
@[simp] theorem liftPolynomial_coneRestrict_zero
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    coneRestrict K 2 m (P.liftPolynomial C₀ B z) = 0 :=
  polynomial_coneRestrict_zero C₀ B (P.diagonalLift C₀ B) (P.offDiagonalLift C₀ B z)

/-- The primitive-data lift belongs to the normal-coordinate ideal. -/
theorem liftPolynomial_mem_coneNormalIdeal
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    P.liftPolynomial C₀ B z ∈ coneNormalIdeal K 2 m :=
  polynomial_mem_coneNormalIdeal C₀ B (P.diagonalLift C₀ B) (P.offDiagonalLift C₀ B z)

/-- The primitive-data lift as an element of the cubic homogeneous piece. -/
noncomputable def liftPolynomialForm
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    Forms K (2 + m) 3 :=
  ⟨P.liftPolynomial C₀ B z, P.liftPolynomial_isHomogeneous C₀ B z⟩

@[simp] theorem liftPolynomialForm_val
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    (P.liftPolynomialForm C₀ B z).val = P.liftPolynomial C₀ B z := rfl

/-- Homogeneous restriction of the lifted form is zero. -/
@[simp] theorem liftPolynomialForm_coneRestrict
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K) :
    coneRestrictForm K 2 m 3 (P.liftPolynomialForm C₀ B z) = 0 := by
  apply Subtype.ext
  exact P.liftPolynomial_coneRestrict_zero C₀ B z

@[simp] theorem liftPolynomialForm_vertex
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K)
    (i : Fin m) (d : Fin 2) :
    eval (P.vertexPoint i d) (P.liftPolynomialForm C₀ B z).val = 0 :=
  P.liftPolynomial_vertex C₀ B z i d

@[simp] theorem liftPolynomialForm_edge
    (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K) (z : P.SingleEdge → K)
    (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    eval (P.edgePoint e d) (P.liftPolynomialForm C₀ B z).val = 0 :=
  P.liftPolynomial_edge C₀ B z e d hd

end Parameters
end IdealGeneration.CubicSupported
