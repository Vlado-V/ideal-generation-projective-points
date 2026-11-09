module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace IdealGeneration.CubicPair

abbrev F := ZMod 1009

private theorem prime1009 : Nat.Prime 1009 := by decide +kernel
local instance : Fact (Nat.Prime 1009) := ⟨prime1009⟩

/-- Coordinates follow the order `0, 5, 6, 10, 11, 12, 13` of Appendix C.3. -/
def coordinateLabel : Fin 7 → ℕ := ![0, 5, 6, 10, 11, 12, 13]

/-- Lift centers follow the order `10, 11, 12, 13`. -/
def centerIndex (c : Fin 4) : Fin 7 := Fin.natAdd 3 c

/-- The two normal slopes at each vertex. -/
def vertexSlope : Fin 7 → Fin 2 → F :=
  ![![469, 749], ![936, 705], ![794, 897], ![482, 163], ![954, 102], ![921, 950], ![186, 42]]

/-- The two nonzero heights at each vertex. -/
def vertexHeight : Fin 7 → Fin 2 → F :=
  ![![938, 714], ![289, 839], ![364, 253], ![649, 682], ![166, 209], ![799, 58], ![888, 750]]

/-- Symmetric edge slopes. On a single edge, the second slot repeats the first. -/
def edgeSlope : Fin 7 → Fin 7 → Fin 2 → F :=
  ![![![0, 1], ![305, 396], ![316, 627], ![101, 577], ![142, 994], ![184, 267], ![151, 605]], ![![305, 396], ![0, 1], ![752, 981], ![428, 934], ![862, 534], ![913, 765], ![359, 25]], ![![316, 627], ![752, 981], ![0, 1], ![710, 101], ![192, 749], ![428, 151], ![750, 217]], ![![101, 577], ![428, 934], ![710, 101], ![0, 1], ![536, 817], ![197, 575], ![479, 479]], ![![142, 994], ![862, 534], ![192, 749], ![536, 817], ![0, 1], ![810, 810], ![465, 336]], ![![184, 267], ![913, 765], ![428, 151], ![197, 575], ![810, 810], ![0, 1], ![114, 997]], ![![151, 605], ![359, 25], ![750, 217], ![479, 479], ![465, 336], ![114, 997], ![0, 1]]]

/-- Symmetric edge heights, with the same slot convention as the slopes. -/
def edgeHeight : Fin 7 → Fin 7 → Fin 2 → F :=
  ![![![1, 1], ![868, 348], ![729, 920], ![365, 243], ![548, 266], ![111, 989], ![453, 351]], ![![868, 348], ![1, 1], ![985, 969], ![647, 309], ![623, 624], ![140, 527], ![415, 758]], ![![729, 920], ![985, 969], ![1, 1], ![56, 271], ![555, 31], ![931, 81], ![945, 273]], ![![365, 243], ![647, 309], ![56, 271], ![1, 1], ![713, 462], ![78, 612], ![51, 51]], ![![548, 266], ![623, 624], ![555, 31], ![713, 462], ![1, 1], ![66, 66], ![206, 669]], ![![111, 989], ![140, 527], ![931, 81], ![78, 612], ![66, 66], ![1, 1], ![361, 487]], ![![453, 351], ![415, 758], ![945, 273], ![51, 51], ![206, 669], ![361, 487], ![1, 1]]]

/-- The parameter of the support at the unordered edge, oriented by increasing index. -/
def edgeLambda : Fin 7 → Fin 7 → F :=
  ![![1, 709, 166, 213, 980, 377, 920], ![709, 1, 543, 847, 637, 129, 842], ![166, 543, 1, 587, 965, 276, 966], ![213, 847, 587, 1, 441, 165, 977], ![980, 637, 965, 441, 1, 705, 574], ![377, 129, 276, 165, 705, 1, 822], ![920, 842, 966, 977, 574, 822, 1]]

/-- The two single edges are `{11,12}` and `{10,13}`. -/
def singleEdge (i j : Fin 7) : Bool :=
  (i == 4 && j == 5) || (i == 5 && j == 4) ||
  (i == 3 && j == 6) || (i == 6 && j == 3)

/-- Only slot zero is used at a single edge. -/
def edgeSlot (i j : Fin 7) (d : Fin 2) : Prop :=
  singleEdge i j = false ∨ d = 0

instance (i j : Fin 7) (d : Fin 2) : Decidable (edgeSlot i j d) :=
  inferInstanceAs (Decidable (singleEdge i j = false ∨ d = 0))

/-- Slopes appearing in the two extra and half-face families. -/
def singleSlopeOne : F := edgeSlope 4 5 0
def singleSlopeTwo : F := edgeSlope 3 6 0

/-- Coefficients of the four linear lifts for the quadratic basis `s², st, t²`. -/
def liftCoefficients : Fin 4 → Fin 3 → Fin 7 → Fin 2 → F :=
  ![![![![962, 115], ![821, 857], ![924, 28], ![207, 247], ![590, 128], ![370, 960], ![780, 0]], ![![375, 913], ![219, 510], ![12, 922], ![295, 100], ![555, 650], ![121, 59], ![166, 0]], ![![687, 499], ![966, 855], ![610, 372], ![483, 219], ![161, 345], ![850, 555], ![243, 0]]], ![![![940, 975], ![641, 885], ![642, 740], ![214, 900], ![606, 35], ![304, 0], ![926, 230]], ![![928, 178], ![144, 768], ![562, 288], ![884, 359], ![604, 233], ![736, 0], ![310, 112]], ![![380, 591], ![36, 737], ![534, 617], ![242, 709], ![475, 456], ![873, 0], ![473, 288]]], ![![![399, 138], ![451, 9], ![773, 939], ![740, 145], ![388, 0], ![379, 25], ![266, 824]], ![![643, 964], ![331, 546], ![263, 318], ![46, 743], ![940, 0], ![361, 740], ![52, 674]], ![![167, 490], ![987, 907], ![347, 383], ![81, 549], ![478, 0], ![192, 553], ![890, 530]]], ![![![492, 108], ![161, 492], ![699, 959], ![123, 0], ![531, 440], ![460, 633], ![56, 892]], ![![978, 434], ![525, 301], ![706, 525], ![918, 0], ![286, 538], ![929, 284], ![859, 623]], ![![287, 267], ![21, 452], ![971, 363], ![135, 0], ![359, 625], ![327, 830], ![540, 634]]]]

/-- Value of a normal quadratic basis monomial at `(1,t)`. -/
def normalBasisValue (q : Fin 3) (t : F) : F := ![1, t, t * t] q

/-- Pairing with the normal direction `(1,t)`. -/
def normalPair (a : Fin 2 → F) (t : F) : F := a 0 + t * a 1

/-- Denominator-cleared expression from the edge equations in (B.4). -/
def edgeExpression (c : Fin 4) (j : Fin 7) (a : Fin 7 → Fin 2 → F) (t : F) : F :=
  if centerIndex c < j then
    normalPair (a (centerIndex c)) t + edgeLambda (centerIndex c) j * normalPair (a j) t
  else
    edgeLambda (centerIndex c) j * normalPair (a (centerIndex c)) t + normalPair (a j) t

/-- Every primitive vertex height is invertible. -/
theorem vertexHeight_ne_zero : ∀ i d, vertexHeight i d ≠ 0 := by decide +kernel

/-- Every primitive edge height is invertible. -/
theorem edgeHeight_ne_zero : ∀ i j d, edgeHeight i j d ≠ 0 := by decide +kernel

/-- Every edge support parameter is invertible. -/
theorem edgeLambda_ne_zero : ∀ i j, edgeLambda i j ≠ 0 := by decide +kernel

/-- The two normal directions at a vertex are independent. -/
theorem vertexSlope_ne : ∀ i, vertexSlope i 0 ≠ vertexSlope i 1 := by decide +kernel

/-- The two normal directions at a double edge are independent. -/
theorem edgeSlope_ne : ∀ i j, i ≠ j → singleEdge i j = false →
    edgeSlope i j 0 ≠ edgeSlope i j 1 := by decide +kernel

/-- The stored basis lifts satisfy the vertex equations in (B.4). -/
theorem lift_vertex_equations : ∀ c q d,
    vertexHeight (centerIndex c) d *
      normalPair (liftCoefficients c q (centerIndex c)) (vertexSlope (centerIndex c) d) +
      normalBasisValue q (vertexSlope (centerIndex c) d) = 0 := by decide +kernel

/-- The stored basis lifts satisfy every incident edge equation in (B.4). -/
theorem lift_edge_equations : ∀ c q j d, j ≠ centerIndex c → edgeSlot (centerIndex c) j d →
    edgeHeight (centerIndex c) j d *
      edgeExpression c j (liftCoefficients c q) (edgeSlope (centerIndex c) j d) +
      normalBasisValue q (edgeSlope (centerIndex c) j d) = 0 := by decide +kernel

/-- At a single edge the chosen solution has zero t-component. -/
theorem lift_single_gauge : ∀ c q j, j ≠ centerIndex c → singleEdge (centerIndex c) j = true →
    liftCoefficients c q j 1 = 0 := by decide +kernel

/-- The two slopes match the values used in the extra and half-face columns. -/
theorem singleSlopes : singleSlopeOne = 810 ∧ singleSlopeTwo = 479 := by decide +kernel

/-- The normal quadratic with arbitrary coefficients in the stated basis. -/
def quadraticValue (Q : Fin 3 → F) (t : F) : F := ∑ q, Q q * normalBasisValue q t

/-- The lift is linear in the three normal quadratic coefficients. -/
def linearLift (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7) (k : Fin 2) : F :=
  ∑ q, Q q * liftCoefficients c q j k

/-- The linear extension satisfies the vertex equation for every normal quadratic. -/
theorem linearLift_vertex (Q : Fin 3 → F) (c : Fin 4) (d : Fin 2) :
    vertexHeight (centerIndex c) d *
      normalPair (linearLift Q c (centerIndex c)) (vertexSlope (centerIndex c) d) +
      quadraticValue Q (vertexSlope (centerIndex c) d) = 0 := by
  have h0 := lift_vertex_equations c 0 d
  have h1 := lift_vertex_equations c 1 d
  have h2 := lift_vertex_equations c 2 d
  simp only [linearLift, quadraticValue, normalPair, Fin.sum_univ_three] at *
  linear_combination Q 0 * h0 + Q 1 * h1 + Q 2 * h2

/-- The same linear extension satisfies all incident edge equations. -/
theorem linearLift_edge (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    edgeHeight (centerIndex c) j d *
      edgeExpression c j (linearLift Q c) (edgeSlope (centerIndex c) j d) +
      quadraticValue Q (edgeSlope (centerIndex c) j d) = 0 := by
  have h0 := lift_edge_equations c 0 j d hj hd
  have h1 := lift_edge_equations c 1 j d hj hd
  have h2 := lift_edge_equations c 2 j d hj hd
  simp only [edgeExpression] at *
  split_ifs at * <;>
    simp only [linearLift, quadraticValue, normalPair, Fin.sum_univ_three] at * <;>
    linear_combination Q 0 * h0 + Q 1 * h1 + Q 2 * h2

/-- The single-edge gauge is preserved by the linear extension. -/
theorem linearLift_single_gauge (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7)
    (hj : j ≠ centerIndex c) (hs : singleEdge (centerIndex c) j = true) :
    linearLift Q c j 1 = 0 := by
  simp [linearLift, lift_single_gauge c _ j hj hs]

private theorem clearedVertex {a q mu : F} (hm : mu ≠ 0)
    (h : mu * a + q = 0) : a = -q / mu := by
  apply (eq_div_iff hm).2
  linear_combination h

private theorem clearedUpper {a b q mu lam : F} (hm : mu ≠ 0) (hl : lam ≠ 0)
    (h : mu * (a + lam * b) + q = 0) : b = -(q / mu + a) / lam := by
  field_simp
  linear_combination h

private theorem clearedLower {a b q mu lam : F} (hm : mu ≠ 0)
    (h : mu * (lam * a + b) + q = 0) : b = -q / mu - lam * a := by
  field_simp
  linear_combination h

/-- The vertex lift equation in the divided form of (B.4). -/
theorem linearLift_vertex_divided (Q : Fin 3 → F) (c : Fin 4) (d : Fin 2) :
    normalPair (linearLift Q c (centerIndex c)) (vertexSlope (centerIndex c) d) =
      -quadraticValue Q (vertexSlope (centerIndex c) d) / vertexHeight (centerIndex c) d :=
  clearedVertex (vertexHeight_ne_zero _ _) (linearLift_vertex Q c d)

/-- The incident edge lift equation in the divided form of (B.4). -/
theorem linearLift_edge_divided (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    normalPair (linearLift Q c j) (edgeSlope (centerIndex c) j d) =
      if centerIndex c < j then
        -(quadraticValue Q (edgeSlope (centerIndex c) j d) / edgeHeight (centerIndex c) j d +
          normalPair (linearLift Q c (centerIndex c)) (edgeSlope (centerIndex c) j d)) /
            edgeLambda (centerIndex c) j
      else
        -quadraticValue Q (edgeSlope (centerIndex c) j d) / edgeHeight (centerIndex c) j d -
          edgeLambda (centerIndex c) j *
            normalPair (linearLift Q c (centerIndex c)) (edgeSlope (centerIndex c) j d) := by
  have h := linearLift_edge Q c j d hj hd
  by_cases hlt : centerIndex c < j
  · simp only [edgeExpression, hlt, ite_true] at h ⊢
    exact clearedUpper (edgeHeight_ne_zero _ _ _) (edgeLambda_ne_zero _ _) h
  · simp only [edgeExpression, hlt, ite_false] at h ⊢
    exact clearedLower (edgeHeight_ne_zero _ _ _) h

/-- Solve two equations `x + t₀ y = r₀`, `x + t₁ y = r₁`. -/
def solveTwo (t₀ t₁ r₀ r₁ : F) : Fin 2 → F :=
  let y := (r₁ - r₀) / (t₁ - t₀)
  ![r₀ - t₀ * y, y]

/-- The central coefficient obtained by solving the two vertex equations. -/
def computedCenter (c : Fin 4) (q : Fin 3) : Fin 2 → F :=
  solveTwo (vertexSlope (centerIndex c) 0) (vertexSlope (centerIndex c) 1)
    (-normalBasisValue q (vertexSlope (centerIndex c) 0) / vertexHeight (centerIndex c) 0)
    (-normalBasisValue q (vertexSlope (centerIndex c) 1) / vertexHeight (centerIndex c) 1)

/-- The right hand side in the incident-edge equation (B.4). -/
def computedEdgeRhs (c : Fin 4) (q : Fin 3) (j : Fin 7) (d : Fin 2) : F :=
  let t := edgeSlope (centerIndex c) j d
  let central := normalPair (computedCenter c q) t
  let quadratic := normalBasisValue q t / edgeHeight (centerIndex c) j d
  if centerIndex c < j then
    -(quadratic + central) / edgeLambda (centerIndex c) j
  else
    -quadratic - edgeLambda (centerIndex c) j * central

/-- The deterministic lift algorithm from the primitive cone parameters. -/
def computedCoefficients (c : Fin 4) (q : Fin 3) (j : Fin 7) : Fin 2 → F :=
  if j = centerIndex c then computedCenter c q
  else if singleEdge (centerIndex c) j then ![computedEdgeRhs c q j 0, 0]
  else solveTwo (edgeSlope (centerIndex c) j 0) (edgeSlope (centerIndex c) j 1)
    (computedEdgeRhs c q j 0) (computedEdgeRhs c q j 1)

/-- The stored coefficients are exactly the output of the primitive-data lift algorithm. -/
theorem computedCoefficients_eq : ∀ c q j k, computedCoefficients c q j k = liftCoefficients c q j k :=
  by decide +kernel


/-- The binary normal quadratic with its three ordered coefficients. -/
def normalQuadraticValue (Q : Fin 3 → F) (s t : F) : F :=
  Q 0 * s * s + Q 1 * s * t + Q 2 * t * t

@[simp] theorem normalQuadraticValue_one (Q : Fin 3 → F) (t : F) :
    normalQuadraticValue Q 1 t = quadraticValue Q t := by
  simp [normalQuadraticValue, quadraticValue, normalBasisValue, Fin.sum_univ_three]
  ring

/-- Evaluate the cubic `y_c (Q(s,t) + s L_c(Q)_s(y) + t L_c(Q)_t(y))`. -/
def liftedCubicValue (Q : Fin 3 → F) (c : Fin 4) (s t : F) (y : Fin 7 → F) : F :=
  y (centerIndex c) * (normalQuadraticValue Q s t +
    ∑ j, y j * (s * linearLift Q c j 0 + t * linearLift Q c j 1))

/-- The trace coordinates `μ e_i` of an actual vertex cone point. -/
def vertexTracePoint (i : Fin 7) (d : Fin 2) (j : Fin 7) : F :=
  if j = i then vertexHeight i d else 0

/-- The trace coordinates `μ (e_low + λ e_high)` of an actual incident edge cone point. -/
def incidentTracePoint (c : Fin 4) (j : Fin 7) (d : Fin 2) (k : Fin 7) : F :=
  let mu := edgeHeight (centerIndex c) j d
  let lam := edgeLambda (centerIndex c) j
  if centerIndex c < j then
    (if k = centerIndex c then mu else 0) + (if k = j then mu * lam else 0)
  else
    (if k = j then mu else 0) + (if k = centerIndex c then mu * lam else 0)

/-- Every vertex cone point annihilates every chosen cubic lift. -/
theorem liftedCubicValue_vertex (Q : Fin 3 → F) (c : Fin 4) (i : Fin 7) (d : Fin 2) :
    liftedCubicValue Q c 1 (vertexSlope i d) (vertexTracePoint i d) = 0 := by
  by_cases hc : centerIndex c = i
  · subst i
    have h := linearLift_vertex Q c d
    simp only [normalPair] at h
    simp [-mul_eq_zero, liftedCubicValue, vertexTracePoint, normalQuadraticValue_one, ite_mul]
    linear_combination vertexHeight (centerIndex c) d * h
  · simp [liftedCubicValue, vertexTracePoint, hc]

/-- At an incident edge, cubic evaluation is the cleared equation (B.4) times `y_c`. -/
theorem liftedCubicValue_incident_formula (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (t : F) (hj : j ≠ centerIndex c) :
    liftedCubicValue Q c 1 t (incidentTracePoint c j d) =
      incidentTracePoint c j d (centerIndex c) *
        (quadraticValue Q t + edgeHeight (centerIndex c) j d *
          edgeExpression c j (linearLift Q c) t) := by
  by_cases hlt : centerIndex c < j
  · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff, liftedCubicValue, incidentTracePoint, hlt, Ne.symm hj,
      add_mul, ite_mul, Finset.sum_add_distrib, edgeExpression, normalPair]
    ring
  · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff, liftedCubicValue, incidentTracePoint, hlt, Ne.symm hj,
      add_mul, ite_mul, Finset.sum_add_distrib, edgeExpression, normalPair]
    ring

/-- Every incident edge cone point annihilates the chosen cubic lift. -/
theorem liftedCubicValue_incident (Q : Fin 3 → F) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    liftedCubicValue Q c 1 (edgeSlope (centerIndex c) j d) (incidentTracePoint c j d) = 0 := by
  rw [liftedCubicValue_incident_formula Q c j d _ hj]
  have h := linearLift_edge Q c j d hj hd
  rw [add_comm] at h
  rw [h, mul_zero]

/-- The cubic lift vanishes on the trace plane. -/
theorem liftedCubicValue_trace (Q : Fin 3 → F) (c : Fin 4) (y : Fin 7 → F) :
    liftedCubicValue Q c 0 0 y = 0 := by
  simp [liftedCubicValue, normalQuadraticValue]


end IdealGeneration.CubicPair
