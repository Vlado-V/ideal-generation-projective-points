module

public import IdealGeneration.ConeSplitting

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Supported cone points and actual cubic equations for Appendix B. -/

namespace IdealGeneration.CubicSupported

/-- An unordered edge is represented by its increasing pair of coordinates. -/
abbrev Edge (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

section Coefficients

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The four normal cubic coefficients, ordered `s³,s²t,st²,t³`. -/
def normalCubic (a : Fin 4 → R) (s t : R) : R :=
  a 0 * s ^ 3 + a 1 * s ^ 2 * t + a 2 * s * t ^ 2 + a 3 * t ^ 3

/-- The three normal quadratic coefficients, ordered `s²,st,t²`. -/
def normalQuadratic (a : Fin 3 → R) (s t : R) : R :=
  a 0 * s ^ 2 + a 1 * s * t + a 2 * t ^ 2

/-- The normal-linear coefficients of the diagonal and increasing-edge monomials. -/
def upperCoefficient (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (i j : Fin m) (k : Fin 2) : R :=
  if h : i < j then offDiagonal ⟨(i, j), h⟩ k else if i = j then diagonal i k else 0

@[simp] theorem upperCoefficient_diagonal
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R) (i : Fin m) (k : Fin 2) :
    upperCoefficient diagonal offDiagonal i i k = diagonal i k := by
  simp [upperCoefficient]

@[simp] theorem upperCoefficient_edge
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R) (e : Edge m) (k : Fin 2) :
    upperCoefficient diagonal offDiagonal e.val.1 e.val.2 k = offDiagonal e k := by
  simp [upperCoefficient, e.property]

@[simp] theorem upperCoefficient_reverse
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R) (e : Edge m) (k : Fin 2) :
    upperCoefficient diagonal offDiagonal e.val.2 e.val.1 k = 0 := by
  simp [upperCoefficient, not_lt_of_ge e.property.le, ne_of_gt e.property]

/-- Evaluate one trace-quadratic coefficient of the normal-linear part. -/
def traceQuadratic (a : Fin m → Fin m → R) (y : Fin m → R) : R :=
  ∑ i, ∑ j, a i j * y i * y j

/-- The supported cubic retains all three positive normal degrees. -/
def cubicValue (C : Fin 4 → R) (B : Fin m → Fin 3 → R)
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (s t : R) (y : Fin m → R) : R :=
  normalCubic C s t + ∑ i, y i * normalQuadratic (B i) s t +
    s * traceQuadratic (fun i j => upperCoefficient diagonal offDiagonal i j 0) y +
    t * traceQuadratic (fun i j => upperCoefficient diagonal offDiagonal i j 1) y

/-- A scaled coordinate vertex in the trace space. -/
def vertexSupport (i : Fin m) (μ : R) (j : Fin m) : R := if j = i then μ else 0

/-- A scaled edge support in the trace space. -/
def edgeSupport (e : Edge m) (μ lam : R) (j : Fin m) : R :=
  vertexSupport e.val.1 μ j + vertexSupport e.val.2 (μ * lam) j

@[simp] theorem traceQuadratic_vertex (a : Fin m → Fin m → R) (i : Fin m) (μ : R) :
    traceQuadratic a (vertexSupport i μ) = μ ^ 2 * a i i := by
  simp [traceQuadratic, vertexSupport, mul_ite, ite_mul]
  ring

theorem traceQuadratic_pair (a : Fin m → Fin m → R) (i j : Fin m) (μ ν : R) :
    traceQuadratic a (fun k => vertexSupport i μ k + vertexSupport j ν k) =
      μ ^ 2 * a i i + μ * ν * a i j + ν * μ * a j i + ν ^ 2 * a j j := by
  simp [traceQuadratic, vertexSupport, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul]
  ring

/-- Vertex evaluation separates the normal cubic, mixed quadratic, and diagonal coefficient. -/
theorem cubicValue_vertex (C : Fin 4 → R) (B : Fin m → Fin 3 → R)
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (i : Fin m) (s t μ : R) :
    cubicValue C B diagonal offDiagonal s t (vertexSupport i μ) =
      normalCubic C s t + μ * normalQuadratic (B i) s t +
        μ ^ 2 * (diagonal i 0 * s + diagonal i 1 * t) := by
  simp [cubicValue, vertexSupport, mul_ite, ite_mul, traceQuadratic]
  ring

/-- Edge evaluation has exactly one increasing-edge coefficient. -/
theorem cubicValue_edge (C : Fin 4 → R) (B : Fin m → Fin 3 → R)
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (e : Edge m) (s t μ lam : R) :
    cubicValue C B diagonal offDiagonal s t (edgeSupport e μ lam) =
      normalCubic C s t + μ * (normalQuadratic (B e.val.1) s t +
        lam * normalQuadratic (B e.val.2) s t) +
      μ ^ 2 * ((diagonal e.val.1 0 * s + diagonal e.val.1 1 * t) +
        lam * (offDiagonal e 0 * s + offDiagonal e 1 * t) +
        lam ^ 2 * (diagonal e.val.2 0 * s + diagonal e.val.2 1 * t)) := by
  unfold cubicValue edgeSupport
  rw [traceQuadratic_pair, traceQuadratic_pair]
  simp only [upperCoefficient_diagonal, upperCoefficient_edge, upperCoefficient_reverse]
  simp [vertexSupport, add_mul, Finset.sum_add_distrib, ite_mul]
  ring

@[simp] theorem map_upperCoefficient {S : Type*} [CommRing S] (f : R →+* S)
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (i j : Fin m) (k : Fin 2) :
    f (upperCoefficient diagonal offDiagonal i j k) =
      upperCoefficient (fun i k => f (diagonal i k)) (fun e k => f (offDiagonal e k)) i j k := by
  by_cases h : i < j
  · simp [upperCoefficient, h]
  · by_cases hij : i = j <;> simp [upperCoefficient, h, hij]

/-- Evaluation and coefficient maps commute with the cubic formula. -/
theorem map_cubicValue {S : Type*} [CommRing S] (f : R →+* S)
    (C : Fin 4 → R) (B : Fin m → Fin 3 → R)
    (diagonal : Fin m → Fin 2 → R) (offDiagonal : Edge m → Fin 2 → R)
    (s t : R) (y : Fin m → R) :
    f (cubicValue C B diagonal offDiagonal s t y) =
      cubicValue (fun q => f (C q)) (fun i q => f (B i q))
        (fun i k => f (diagonal i k)) (fun e k => f (offDiagonal e k))
        (f s) (f t) (fun i => f (y i)) := by
  simp [cubicValue, normalCubic, normalQuadratic, traceQuadratic, map_sum]

end Coefficients

section Polynomial

open MvPolynomial
variable {K : Type*} [Field K] {m : ℕ}

/-- The genuine cubic polynomial in the two normal and `m` trace variables. -/
noncomputable def polynomial (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K) :
    Poly K (2 + m) :=
  cubicValue (fun q => C (C₀ q)) (fun i q => C (B i q))
    (fun i k => C (diagonal i k)) (fun e k => C (offDiagonal e k))
    (X (Fin.castAdd m 0)) (X (Fin.castAdd m 1)) (fun i => X (Fin.natAdd 2 i))

/-- The polynomial evaluates by the explicit normal-degree formula. -/
theorem eval_polynomial (C₀ : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (diagonal : Fin m → Fin 2 → K) (offDiagonal : Edge m → Fin 2 → K)
    (x : Fin (2 + m) → K) :
    eval x (polynomial C₀ B diagonal offDiagonal) =
      cubicValue C₀ B diagonal offDiagonal (x (Fin.castAdd m 0)) (x (Fin.castAdd m 1))
        (fun i => x (Fin.natAdd 2 i)) := by
  simpa only [polynomial, eval_C, eval_X] using
    map_cubicValue (eval x) (fun q => C (C₀ q)) (fun i q => C (B i q))
      (fun i k => C (diagonal i k)) (fun e k => C (offDiagonal e k))
      (X (Fin.castAdd m 0)) (X (Fin.castAdd m 1)) (fun i => X (Fin.natAdd 2 i))

end Polynomial

section ConeData

variable (K : Type*) [Field K] (m : ℕ)

/-- Primitive parameters for vertex and edge cones on the coordinate simplex. -/
structure Parameters where
  single : Edge m → Bool
  vertexSlope : Fin m → Fin 2 → K
  vertexHeight : Fin m → Fin 2 → K
  edgeSlope : Edge m → Fin 2 → K
  edgeHeight : Edge m → Fin 2 → K
  edgeLambda : Edge m → K
  vertexSlope_ne : ∀ i, vertexSlope i 0 ≠ vertexSlope i 1
  vertexHeight_ne : ∀ i d, vertexHeight i d ≠ 0
  edgeSlope_ne : ∀ e, single e = false → edgeSlope e 0 ≠ edgeSlope e 1
  edgeHeight_ne : ∀ e d, edgeHeight e d ≠ 0
  edgeLambda_ne : ∀ e, edgeLambda e ≠ 0

namespace Parameters

variable {K m} (P : Parameters K m)

/-- The second slot at a single edge is omitted. -/
def EdgeSlot (e : Edge m) (d : Fin 2) : Prop := P.single e = false ∨ d = 0

instance (e : Edge m) (d : Fin 2) : Decidable (P.EdgeSlot e d) := inferInstanceAs (Decidable (_ ∨ _))

/-- A vertex cone point has normal coordinates `(1,τ)` and trace coordinates `μ e_i`. -/
def vertexPoint (i : Fin m) (d : Fin 2) : Fin (2 + m) → K :=
  Fin.addCases ![1, P.vertexSlope i d] (vertexSupport i (P.vertexHeight i d))

/-- An edge cone point has trace coordinates `μ(e_i+lam e_j)`. -/
def edgePoint (e : Edge m) (d : Fin 2) : Fin (2 + m) → K :=
  Fin.addCases ![1, P.edgeSlope e d] (edgeSupport e (P.edgeHeight e d) (P.edgeLambda e))

@[simp] theorem vertexPoint_normal_zero (i : Fin m) (d : Fin 2) :
    P.vertexPoint i d (Fin.castAdd m 0) = 1 := by simp [vertexPoint]

@[simp] theorem edgePoint_normal_zero (e : Edge m) (d : Fin 2) :
    P.edgePoint e d (Fin.castAdd m 0) = 1 := by simp [edgePoint]

@[simp] theorem vertexPoint_normal_one (i : Fin m) (d : Fin 2) :
    P.vertexPoint i d (Fin.castAdd m 1) = P.vertexSlope i d := by simp [vertexPoint]

@[simp] theorem vertexPoint_trace (i : Fin m) (d : Fin 2) (j : Fin m) :
    P.vertexPoint i d (Fin.natAdd 2 j) = vertexSupport i (P.vertexHeight i d) j := by
  simp [vertexPoint]

@[simp] theorem edgePoint_normal_one (e : Edge m) (d : Fin 2) :
    P.edgePoint e d (Fin.castAdd m 1) = P.edgeSlope e d := by simp [edgePoint]

@[simp] theorem edgePoint_trace (e : Edge m) (d : Fin 2) (j : Fin m) :
    P.edgePoint e d (Fin.natAdd 2 j) = edgeSupport e (P.edgeHeight e d) (P.edgeLambda e) j := by
  simp [edgePoint]

end Parameters
end ConeData
end IdealGeneration.CubicSupported

namespace IdealGeneration.CubicSupported

section TwoEquations

variable {K : Type*} [Field K]

def normalLinear (a : Fin 2 → K) (s t : K) : K := a 0 * s + a 1 * t

/-- The linear solve used at every double support. -/
def solveTwo (t₀ t₁ r₀ r₁ : K) : Fin 2 → K :=
  let y := (r₁ - r₀) / (t₁ - t₀)
  ![r₀ - t₀ * y, y]

theorem solveTwo_first (t₀ t₁ r₀ r₁ : K) :
    normalLinear (solveTwo t₀ t₁ r₀ r₁) 1 t₀ = r₀ := by
  simp only [normalLinear, solveTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one]
  ring

theorem solveTwo_second (t₀ t₁ r₀ r₁ : K) (ht : t₀ ≠ t₁) :
    normalLinear (solveTwo t₀ t₁ r₀ r₁) 1 t₁ = r₁ := by
  have hden : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr ht.symm
  simp only [normalLinear, solveTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one]
  field_simp
  ring

theorem solveTwo_slot (t r : Fin 2 → K) (ht : t 0 ≠ t 1) (d : Fin 2) :
    normalLinear (solveTwo (t 0) (t 1) (r 0) (r 1)) 1 (t d) = r d := by
  fin_cases d
  · exact solveTwo_first _ _ _ _
  · exact solveTwo_second _ _ _ _ ht

end TwoEquations

namespace Parameters

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

/-- One free coefficient for each single edge of the supported graph. -/
abbrev SingleEdge := {e : Edge m // P.single e = true}

/-- Vertex equations determine the diagonal coefficients for arbitrary `C,B`. -/
def diagonalRhs (C : Fin 4 → K) (B : Fin m → Fin 3 → K) (i : Fin m) (d : Fin 2) : K :=
  -(normalCubic C 1 (P.vertexSlope i d) +
    P.vertexHeight i d * normalQuadratic (B i) 1 (P.vertexSlope i d)) / (P.vertexHeight i d) ^ 2

def diagonalLift (C : Fin 4 → K) (B : Fin m → Fin 3 → K) (i : Fin m) : Fin 2 → K :=
  solveTwo (P.vertexSlope i 0) (P.vertexSlope i 1)
    (P.diagonalRhs C B i 0) (P.diagonalRhs C B i 1)

/-- The remaining edge equation after the two endpoint diagonals have been solved. -/
def edgeRhs (C : Fin 4 → K) (B : Fin m → Fin 3 → K) (e : Edge m) (d : Fin 2) : K :=
  let t := P.edgeSlope e d;
  let μ := P.edgeHeight e d;
  let lam := P.edgeLambda e;
  -(normalCubic C 1 t + μ * (normalQuadratic (B e.val.1) 1 t +
      lam * normalQuadratic (B e.val.2) 1 t) +
    μ ^ 2 * (normalLinear (P.diagonalLift C B e.val.1) 1 t +
      lam ^ 2 * normalLinear (P.diagonalLift C B e.val.2) 1 t)) / (μ ^ 2 * lam)

/-- On a single edge the free parameter multiplies `τs-t`; double edges use the unique solve. -/
def offDiagonalLift (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (e : Edge m) : Fin 2 → K :=
  if h : P.single e = true then
    ![P.edgeRhs C B e 0 + P.edgeSlope e 0 * z ⟨e, h⟩, -z ⟨e, h⟩]
  else
    solveTwo (P.edgeSlope e 0) (P.edgeSlope e 1) (P.edgeRhs C B e 0) (P.edgeRhs C B e 1)

theorem diagonalLift_normal (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (i : Fin m) (d : Fin 2) :
    normalLinear (P.diagonalLift C B i) 1 (P.vertexSlope i d) = P.diagonalRhs C B i d :=
  solveTwo_slot (P.vertexSlope i) (P.diagonalRhs C B i) (P.vertexSlope_ne i) d

theorem offDiagonalLift_normal (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    normalLinear (P.offDiagonalLift C B z e) 1 (P.edgeSlope e d) = P.edgeRhs C B e d := by
  by_cases hs : P.single e = true
  · have hd₀ : d = 0 := hd.resolve_left (by simp [hs])
    subst d
    simp only [offDiagonalLift, dite_eq_left hs, normalLinear, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
    ring
  · have hf : P.single e = false := Bool.eq_false_of_not_eq_true hs
    simp only [offDiagonalLift, dite_eq_right hs]
    exact solveTwo_slot (P.edgeSlope e) (P.edgeRhs C B e) (P.edgeSlope_ne e hf) d

/-- All vertex cone equations hold for the constructed coefficients. -/
theorem diagonalLift_constraint (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (i : Fin m) (d : Fin 2) :
    normalCubic C 1 (P.vertexSlope i d) +
      P.vertexHeight i d * normalQuadratic (B i) 1 (P.vertexSlope i d) +
      (P.vertexHeight i d) ^ 2 * normalLinear (P.diagonalLift C B i) 1 (P.vertexSlope i d) = 0 := by
  rw [P.diagonalLift_normal]
  have hden : (P.vertexHeight i d) ^ 2 ≠ 0 := pow_ne_zero _ (P.vertexHeight_ne i d)
  unfold diagonalRhs
  rw [mul_div_cancel₀ _ hden]
  ring

/-- All valid edge cone equations hold, including the freely chosen single-edge kernel. -/
theorem offDiagonalLift_constraint (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    normalCubic C 1 (P.edgeSlope e d) +
      P.edgeHeight e d * (normalQuadratic (B e.val.1) 1 (P.edgeSlope e d) +
        P.edgeLambda e * normalQuadratic (B e.val.2) 1 (P.edgeSlope e d)) +
      (P.edgeHeight e d) ^ 2 *
        (normalLinear (P.diagonalLift C B e.val.1) 1 (P.edgeSlope e d) +
          P.edgeLambda e * normalLinear (P.offDiagonalLift C B z e) 1 (P.edgeSlope e d) +
          (P.edgeLambda e) ^ 2 * normalLinear (P.diagonalLift C B e.val.2) 1 (P.edgeSlope e d)) = 0 := by
  rw [P.offDiagonalLift_normal C B z e d hd]
  have hden : (P.edgeHeight e d) ^ 2 * P.edgeLambda e ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (P.edgeHeight_ne e d)) (P.edgeLambda_ne e)
  have hc : (P.edgeHeight e d) ^ 2 * P.edgeLambda e * P.edgeRhs C B e d +
      (normalCubic C 1 (P.edgeSlope e d) +
        P.edgeHeight e d * (normalQuadratic (B e.val.1) 1 (P.edgeSlope e d) +
          P.edgeLambda e * normalQuadratic (B e.val.2) 1 (P.edgeSlope e d)) +
        (P.edgeHeight e d) ^ 2 *
          (normalLinear (P.diagonalLift C B e.val.1) 1 (P.edgeSlope e d) +
            (P.edgeLambda e) ^ 2 * normalLinear (P.diagonalLift C B e.val.2) 1 (P.edgeSlope e d))) = 0 := by
    unfold edgeRhs
    rw [mul_div_cancel₀ _ hden]
    ring
  linear_combination hc

/-- The actual polynomial lift with arbitrary top two normal degrees and graph kernel parameters. -/
noncomputable def liftPolynomial (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) : Poly K (2 + m) :=
  polynomial C B (P.diagonalLift C B) (P.offDiagonalLift C B z)

theorem liftPolynomial_vertex (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (i : Fin m) (d : Fin 2) :
    MvPolynomial.eval (P.vertexPoint i d) (P.liftPolynomial C B z) = 0 := by
  rw [liftPolynomial, eval_polynomial]
  simp only [vertexPoint_normal_zero, vertexPoint_normal_one, vertexPoint_trace]
  rw [cubicValue_vertex]
  simpa only [normalLinear, mul_one] using P.diagonalLift_constraint C B i d

theorem liftPolynomial_edge (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) (e : Edge m) (d : Fin 2) (hd : P.EdgeSlot e d) :
    MvPolynomial.eval (P.edgePoint e d) (P.liftPolynomial C B z) = 0 := by
  rw [liftPolynomial, eval_polynomial]
  simp only [edgePoint_normal_zero, edgePoint_normal_one, edgePoint_trace]
  rw [cubicValue_edge]
  simpa only [normalLinear, mul_one] using P.offDiagonalLift_constraint C B z e d hd

end Parameters
end IdealGeneration.CubicSupported
