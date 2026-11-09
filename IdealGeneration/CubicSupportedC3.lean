module

public import IdealGeneration.CubicSupportedGraph
public import IdealGeneration.CubicPairRationalConstruction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The rational C.3 data specialize the supported-graph lift of Appendix B.3. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace IdealGeneration.CubicSupported

open IdealGeneration.CubicPair
open IdealGeneration.CubicPair.RationalConstruction

/-- The seven trace coordinates and primitive cone parameters of the rational C.3 witness. -/
def c3Parameters : Parameters ℚ 7 where
  single e := singleEdge e.val.1 e.val.2
  vertexSlope := vertexSlopeQ
  vertexHeight := vertexHeightQ
  edgeSlope e := edgeSlopeQ e.val.1 e.val.2
  edgeHeight e := edgeHeightQ e.val.1 e.val.2
  edgeLambda e := edgeLambdaQ e.val.1 e.val.2
  vertexSlope_ne := vertexSlopeQ_ne
  vertexHeight_ne := vertexHeightQ_ne_zero
  edgeSlope_ne e hs := edgeSlopeQ_ne e.val.1 e.val.2 (ne_of_lt e.property) hs
  edgeHeight_ne e := edgeHeightQ_ne_zero e.val.1 e.val.2
  edgeLambda_ne e := edgeLambdaQ_ne_zero e.val.1 e.val.2

/-- A pure mixed quadratic at one of the four lift centers. -/
def c3Mixed (c : Fin 4) (q : Fin 3) (i : Fin 7) (r : Fin 3) : ℚ :=
  if i = centerIndex c then if r = q then 1 else 0 else 0

/-- The square-trace coefficient of the C.3 lift at its center. -/
def c3Diagonal (c : Fin 4) (q : Fin 3) (i : Fin 7) (k : Fin 2) : ℚ :=
  if i = centerIndex c then liftCoefficientsQ c q i k else 0

/-- On an edge incident to the center, use the lift coefficient of its other endpoint. -/
def c3OffDiagonal (c : Fin 4) (q : Fin 3) (e : Edge 7) (k : Fin 2) : ℚ :=
  if e.val.1 = centerIndex c then liftCoefficientsQ c q e.val.2 k
  else if e.val.2 = centerIndex c then liftCoefficientsQ c q e.val.1 k else 0

private theorem diagonal_center_0 : ∀ (q : Fin 3) (i : Fin 7) (k : Fin 2),
    c3Parameters.diagonalLift 0 (c3Mixed 0 q) i k = c3Diagonal 0 q i k := by decide +kernel

private theorem diagonal_center_1 : ∀ (q : Fin 3) (i : Fin 7) (k : Fin 2),
    c3Parameters.diagonalLift 0 (c3Mixed 1 q) i k = c3Diagonal 1 q i k := by decide +kernel

private theorem diagonal_center_2 : ∀ (q : Fin 3) (i : Fin 7) (k : Fin 2),
    c3Parameters.diagonalLift 0 (c3Mixed 2 q) i k = c3Diagonal 2 q i k := by decide +kernel

private theorem diagonal_center_3 : ∀ (q : Fin 3) (i : Fin 7) (k : Fin 2),
    c3Parameters.diagonalLift 0 (c3Mixed 3 q) i k = c3Diagonal 3 q i k := by decide +kernel

private theorem offDiagonal_center_0 : ∀ (q : Fin 3) (e : Edge 7) (k : Fin 2),
    c3Parameters.offDiagonalLift 0 (c3Mixed 0 q) 0 e k = c3OffDiagonal 0 q e k := by decide +kernel

private theorem offDiagonal_center_1 : ∀ (q : Fin 3) (e : Edge 7) (k : Fin 2),
    c3Parameters.offDiagonalLift 0 (c3Mixed 1 q) 0 e k = c3OffDiagonal 1 q e k := by decide +kernel

private theorem offDiagonal_center_2 : ∀ (q : Fin 3) (e : Edge 7) (k : Fin 2),
    c3Parameters.offDiagonalLift 0 (c3Mixed 2 q) 0 e k = c3OffDiagonal 2 q e k := by decide +kernel

private theorem offDiagonal_center_3 : ∀ (q : Fin 3) (e : Edge 7) (k : Fin 2),
    c3Parameters.offDiagonalLift 0 (c3Mixed 3 q) 0 e k = c3OffDiagonal 3 q e k := by decide +kernel

/-- The generic vertex solve gives the C.3 diagonal coefficient, and zero away from the center. -/
theorem c3DiagonalLift_eq (c : Fin 4) (q : Fin 3) :
    c3Parameters.diagonalLift 0 (c3Mixed c q) = c3Diagonal c q := by
  funext i k
  fin_cases c
  · exact diagonal_center_0 q i k
  · exact diagonal_center_1 q i k
  · exact diagonal_center_2 q i k
  · exact diagonal_center_3 q i k

/-- The generic edge solve in the zero single-edge gauge gives the C.3 edge coefficient. -/
theorem c3OffDiagonalLift_eq (c : Fin 4) (q : Fin 3) :
    c3Parameters.offDiagonalLift 0 (c3Mixed c q) 0 = c3OffDiagonal c q := by
  funext e k
  fin_cases c
  · exact offDiagonal_center_0 q e k
  · exact offDiagonal_center_1 q e k
  · exact offDiagonal_center_2 q e k
  · exact offDiagonal_center_3 q e k

/-- The actual supported cubic for the pure mixed quadratic in C.3. -/
noncomputable def c3LiftPolynomial (c : Fin 4) (q : Fin 3) : Poly ℚ 9 :=
  c3Parameters.liftPolynomial 0 (c3Mixed c q) 0

/-- Its normal-degree coefficients are precisely the checked C.3 coefficients. -/
theorem c3LiftPolynomial_coefficients (c : Fin 4) (q : Fin 3) :
    c3LiftPolynomial c q = polynomial 0 (c3Mixed c q) (c3Diagonal c q) (c3OffDiagonal c q) := by
  rw [c3LiftPolynomial, Parameters.liftPolynomial, c3DiagonalLift_eq, c3OffDiagonalLift_eq]


/-- Only the center contributes a diagonal coefficient in a pure mixed lift. -/
def starDiagonal {R : Type*} [Zero R] {m : ℕ} (c : Fin m)
    (a : Fin m → Fin 2 → R) (i : Fin m) (k : Fin 2) : R :=
  if i = c then a i k else 0

/-- On each increasing edge through the center, retain the other endpoint's coefficient. -/
def starOffDiagonal {R : Type*} [Zero R] {m : ℕ} (c : Fin m)
    (a : Fin m → Fin 2 → R) (e : Edge m) (k : Fin 2) : R :=
  if e.val.1 = c then a e.val.2 k else if e.val.2 = c then a e.val.1 k else 0

section Star

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem starTerm (c : Fin m) (a : Fin m → Fin 2 → R) (k : Fin 2)
    (y : Fin m → R) (i j : Fin m) :
    upperCoefficient (starDiagonal c a) (starOffDiagonal c a) i j k * y i * y j =
      (if i = c then if c ≤ j then y c * (a j k * y j) else 0 else 0) +
        (if j = c then if i < c then y c * (a i k * y i) else 0 else 0) := by
  by_cases hi : i = c
  · subst i
    rcases lt_trichotomy c j with h | rfl | h
    · simp [upperCoefficient, h, starOffDiagonal, le_of_lt h]
      ring
    · simp [starDiagonal]
      ring
    · simp [upperCoefficient, not_lt_of_ge h.le, ne_of_gt h, not_le_of_gt h, ne_of_lt h]
  · by_cases hj : j = c
    · subst j
      by_cases h : i < c
      · simp [upperCoefficient, h, hi, starOffDiagonal]
        ring
      · simp [upperCoefficient, h, hi]
    · unfold upperCoefficient
      split
      · simp [starOffDiagonal, hi, hj]
      · split <;> simp [starDiagonal, hi]

/-- The supported star coefficients evaluate to a trace coordinate times a linear form. -/
theorem traceQuadratic_star (c : Fin m) (a : Fin m → Fin 2 → R) (k : Fin 2) (y : Fin m → R) :
    traceQuadratic (fun i j => upperCoefficient (starDiagonal c a) (starOffDiagonal c a) i j k) y =
      y c * ∑ j, a j k * y j := by
  simp only [traceQuadratic, starTerm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j =>
    if i = c then if c ≤ j then y c * (a j k * y j) else 0 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : c ≤ j
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

/-- Concentrating a normal quadratic coefficient at the center gives the mixed star term. -/
theorem sum_normalQuadratic_star (c : Fin m) (b : Fin 3 → R) (s t : R) (y : Fin m → R) :
    (∑ i, y i * normalQuadratic (if i = c then b else 0) s t) =
      y c * normalQuadratic b s t := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro i _ hi
    simp [hi, normalQuadratic]
  · simp

/-- The supported cubic of a pure mixed lift factors through its center coordinate. -/
theorem cubicValue_star (c : Fin m) (b : Fin 3 → R) (a : Fin m → Fin 2 → R)
    (s t : R) (y : Fin m → R) :
    cubicValue 0 (fun i => if i = c then b else 0) (starDiagonal c a) (starOffDiagonal c a) s t y =
      y c * (normalQuadratic b s t + ∑ j, y j * (s * a j 0 + t * a j 1)) := by
  have hlinear : (∑ j, y j * (s * a j 0 + t * a j 1)) =
      s * (∑ j, a j 0 * y j) + t * (∑ j, a j 1 * y j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [cubicValue, sum_normalQuadratic_star, traceQuadratic_star, normalCubic,
    Pi.zero_apply, zero_mul, zero_add, hlinear]
  ring

end Star

open MvPolynomial in
/-- The supported pure mixed lift is the literal center coordinate times its lifted quadratic. -/
theorem polynomial_star {K : Type*} [Field K] {m : ℕ} (c : Fin m)
    (b : Fin 3 → K) (a : Fin m → Fin 2 → K) :
    polynomial 0 (fun i => if i = c then b else 0) (starDiagonal c a) (starOffDiagonal c a) =
      X (Fin.natAdd 2 c) *
        (normalQuadratic (fun q => C (b q)) (X (Fin.castAdd m 0)) (X (Fin.castAdd m 1)) +
          ∑ j, X (Fin.natAdd 2 j) *
            (X (Fin.castAdd m 0) * C (a j 0) + X (Fin.castAdd m 1) * C (a j 1))) := by
  unfold polynomial
  have hC : (fun q => (C ((0 : Fin 4 → K) q) : Poly K (2 + m))) = 0 := by
    funext q
    simp
  have hB : (fun i q => (C ((if i = c then b else 0) q) : Poly K (2 + m))) =
      (fun i => if i = c then (fun q => C (b q)) else 0) := by
    funext i q
    by_cases hi : i = c <;> simp [hi]
  have hD : (fun i k => (C (starDiagonal c a i k) : Poly K (2 + m))) =
      starDiagonal c (fun i k => C (a i k)) := by
    funext i k
    by_cases hi : i = c <;> simp [starDiagonal, hi]
  have hE : (fun e k => (C (starOffDiagonal c a e k) : Poly K (2 + m))) =
      starOffDiagonal c (fun i k => C (a i k)) := by
    funext e k
    by_cases hi : e.val.1 = c
    · simp [starOffDiagonal, hi]
    · by_cases hj : e.val.2 = c <;> simp [starOffDiagonal, hi, hj]
  rw [hC, hB, hD, hE, cubicValue_star]


open MvPolynomial

/-- One coordinate vector in the ordered normal quadratic basis. -/
def c3Basis (q r : Fin 3) : ℚ := if r = q then 1 else 0

private theorem c3Mixed_eq (c : Fin 4) (q : Fin 3) :
    c3Mixed c q = fun i => if i = centerIndex c then c3Basis q else 0 := by
  funext i r
  by_cases hi : i = centerIndex c
  · simp [c3Mixed, c3Basis, hi]
  · simp [c3Mixed, hi]

/-- The factored C.3 cubic `y_c (Q + s L_c(Q)_s + t L_c(Q)_t)`. -/
noncomputable def c3FactoredLift (c : Fin 4) (q : Fin 3) : Poly ℚ 9 :=
  let s : Poly ℚ 9 := X (Fin.castAdd 7 (0 : Fin 2))
  let t : Poly ℚ 9 := X (Fin.castAdd 7 (1 : Fin 2))
  let y : Fin 7 → Poly ℚ 9 := fun j => X (Fin.natAdd 2 j)
  y (centerIndex c) * (normalQuadratic (fun r => C (c3Basis q r)) s t +
    ∑ j, y j * (s * C (liftCoefficientsQ c q j 0) + t * C (liftCoefficientsQ c q j 1)))

/-- The generic supported lift is exactly the factored polynomial used in C.3. -/
theorem c3LiftPolynomial_eq_factored (c : Fin 4) (q : Fin 3) :
    c3LiftPolynomial c q = c3FactoredLift c q := by
  rw [c3LiftPolynomial_coefficients, c3Mixed_eq]
  exact polynomial_star (centerIndex c) (c3Basis q) (liftCoefficientsQ c q)

private theorem linearLiftQ_c3Basis (c : Fin 4) (q : Fin 3) (j : Fin 7) (k : Fin 2) :
    linearLiftQ (c3Basis q) c j k = liftCoefficientsQ c q j k := by
  simp [linearLiftQ, c3Basis, ite_mul]

/-- The supported polynomial also gives the earlier rational cubic evaluation formula. -/
theorem c3LiftPolynomial_eval (c : Fin 4) (q : Fin 3) (x : Fin 9 → ℚ) :
    eval x (c3LiftPolynomial c q) = liftedCubicValueQ (c3Basis q) c
      (x (Fin.castAdd 7 (0 : Fin 2))) (x (Fin.castAdd 7 (1 : Fin 2)))
      (fun i => x (Fin.natAdd 2 i)) := by
  rw [c3LiftPolynomial_eq_factored]
  simp only [c3FactoredLift, liftedCubicValueQ, normalQuadraticValueQ, normalQuadratic,
    map_mul, map_add, map_sum, eval_X, eval_C, linearLiftQ_c3Basis, pow_two, mul_assoc]

/-- Recover the linear factor coefficients from the generic graph lift. -/
def c3GraphLiftCoefficients (c : Fin 4) (q : Fin 3) (i : Fin 7) (k : Fin 2) : ℚ :=
  if h : i < centerIndex c then
    c3Parameters.offDiagonalLift 0 (c3Mixed c q) 0 ⟨(i, centerIndex c), h⟩ k
  else if h : centerIndex c < i then
    c3Parameters.offDiagonalLift 0 (c3Mixed c q) 0 ⟨(centerIndex c, i), h⟩ k
  else
    c3Parameters.diagonalLift 0 (c3Mixed c q) i k

/-- Extracting the linear factor recovers the checked C.3 coefficient tensor. -/
theorem c3GraphLiftCoefficients_eq (c : Fin 4) (q : Fin 3) (i : Fin 7) (k : Fin 2) :
    c3GraphLiftCoefficients c q i k = liftCoefficientsQ c q i k := by
  unfold c3GraphLiftCoefficients
  split_ifs with hlt hgt
  · rw [c3OffDiagonalLift_eq]
    simp [c3OffDiagonal, ne_of_lt hlt]
  · rw [c3OffDiagonalLift_eq]
    simp [c3OffDiagonal]
  · have heq : i = centerIndex c := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
    rw [c3DiagonalLift_eq]
    simp [c3Diagonal, heq]

/-- The old-coordinate linear coefficients extracted from the supported graph solver. -/
def c3GraphPairCoefficients : PairLiftCoefficients ℚ :=
  fun c q i k => c3GraphLiftCoefficients c q (Fin.castAdd 2 i) k

private theorem c3GraphPairCoefficients_eq :
    c3GraphPairCoefficients = restrictedLiftCoefficientsQ := by
  funext c q i k
  exact c3GraphLiftCoefficients_eq c q (Fin.castAdd 2 i) k

/-- The two single edges in the direction order of C.3. -/
def c3PairEdgeOne : Edge 7 := ⟨(4, 5), by decide⟩
def c3PairEdgeTwo : Edge 7 := ⟨(3, 6), by decide⟩

theorem c3PairEdges_single : c3Parameters.single c3PairEdgeOne = true ∧
    c3Parameters.single c3PairEdgeTwo = true := by decide +kernel

private theorem c3PairSlopes_eq : c3Parameters.edgeSlope c3PairEdgeOne 0 = 810 ∧
    c3Parameters.edgeSlope c3PairEdgeTwo 0 = 479 := by decide +kernel

/-- The C.3 polynomial columns from the generic graph lifts are independent over characteristic zero. -/
theorem c3GraphPairColumns_linearIndependent_over (K : Type*) [Field K] [CharZero K] :
    LinearIndependent K
      (polynomialColumn (fun c q j k => (c3GraphPairCoefficients c q j k : K))
        (c3Parameters.edgeSlope c3PairEdgeOne 0 : K) (c3Parameters.edgeSlope c3PairEdgeTwo 0 : K)) := by
  rw [c3GraphPairCoefficients_eq, c3PairSlopes_eq.1, c3PairSlopes_eq.2]
  simpa only [Rat.cast_ofNat] using pairColumns_linearIndependent_over K

end IdealGeneration.CubicSupported
