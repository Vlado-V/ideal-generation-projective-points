module

public import IdealGeneration.CubicPairLifts
public import IdealGeneration.CubicPairPolynomial
public import IdealGeneration.CubicPairRationalCertificate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace IdealGeneration.CubicPair.RationalConstruction

/-- The primitive cone parameters lifted to their integer representatives. -/
def vertexSlopeQ (i : Fin 7) (d : Fin 2) : ℚ := (vertexSlope i d).val
def vertexHeightQ (i : Fin 7) (d : Fin 2) : ℚ := (vertexHeight i d).val
def edgeSlopeQ (i j : Fin 7) (d : Fin 2) : ℚ := (edgeSlope i j d).val
def edgeHeightQ (i j : Fin 7) (d : Fin 2) : ℚ := (edgeHeight i j d).val
def edgeLambdaQ (i j : Fin 7) : ℚ := (edgeLambda i j).val

/-- Exact rational solutions of the same vertex and edge lift equations. -/
def liftCoefficientsQ : Fin 4 → Fin 3 → Fin 7 → Fin 2 → ℚ :=
  ![![![![((40881490190027 : ℚ) / 135479370113010), ((3176480437 : ℚ) / 67739685056505)], ![((3245037235433 : ℚ) / 2682841308279), ((1044263041 : ℚ) / 5365682616558)], ![((1711983546431 : ℚ) / 2045378498856), ((233030393 : ℚ) / 2045378498856)], ![((-9166 : ℚ) / 6417961), ((-3 : ℚ) / 12835922)], ![((1288398115 : ℚ) / 384139630074123), ((-2158451 : ℚ) / 384139630074123)], ![((-332411479441 : ℚ) / 3184693138546920), ((575709581 : ℚ) / 3184693138546920)], ![((-11827703 : ℚ) / 639575485494), 0]], ![![((-507069778681153 : ℚ) / 135479370113010), ((22483115299132 : ℚ) / 67739685056505)], ![((-38142696539809 : ℚ) / 2682841308279), ((7150769858125 : ℚ) / 5365682616558)], ![((-9317242087399 : ℚ) / 1022689249428), ((927194815853 : ℚ) / 1022689249428)], ![((117849 : ℚ) / 6417961), ((-20267 : ℚ) / 12835922)], ![((1018368870049 : ℚ) / 384139630074123), ((-1776123914 : ℚ) / 384139630074123)], ![((-65056928683907 : ℚ) / 3184693138546920), ((111463413487 : ℚ) / 3184693138546920)], ![((-5665324693 : ℚ) / 639575485494), 0]], ![![((-3544930812815339023 : ℚ) / 135479370113010), ((14238222834658012 : ℚ) / 67739685056505)], ![((-276882798224375977 : ℚ) / 2682841308279), ((4518009068628745 : ℚ) / 5365682616558)], ![((-36493834155603403 : ℚ) / 511344624714), ((146323248958987 : ℚ) / 255672312357)], ![((796148561 : ℚ) / 6417961), ((-12836517 : ℚ) / 12835922)], ![((1272012144548161 : ℚ) / 384139630074123), ((-2358473892107 : ℚ) / 384139630074123)], ![((-11568255708375673 : ℚ) / 3184693138546920), ((17122480747301 : ℚ) / 3184693138546920)], ![((-2712710659031 : ℚ) / 639575485494), 0]]], ![![![((42918661003 : ℚ) / 9449119064), ((80695787 : ℚ) / 56694714384)], ![((2604269493731 : ℚ) / 882285628224), ((145525617467 : ℚ) / 157046841823872)], ![((211638978521393 : ℚ) / 47212020895380), ((42462799407 : ℚ) / 31474680596920)], ![((42381826091729 : ℚ) / 20728022100324), ((26482642705 : ℚ) / 41456044200648)], ![((-22841 : ℚ) / 4926548), ((-43 : ℚ) / 29559288)], ![((-34499 : ℚ) / 2604912255), 0], ![((173593761293 : ℚ) / 8378888457414552), ((-2153582681 : ℚ) / 50273330744487312)]], ![![((-93413118889 : ℚ) / 674937076), ((8159914725 : ℚ) / 1349874152)], ![((-13258763764277 : ℚ) / 147047604704), ((102872433862115 : ℚ) / 26174473637312)], ![((-1012985809746089 : ℚ) / 7868670149230), ((93065642188187 : ℚ) / 15737340298460)], ![((-634671010659467 : ℚ) / 10364011050162), ((56347967832071 : ℚ) / 20728022100324)], ![((348687 : ℚ) / 2463274), ((-30409 : ℚ) / 4926548)], ![((-3044022 : ℚ) / 289434695), 0], ![((9555117438931 : ℚ) / 1396481409569092), ((-108494642293 : ℚ) / 8378888457414552)]], ![![((-198445856408275 : ℚ) / 337468538), ((221831655669 : ℚ) / 35523004)], ![((-28075899063118695 : ℚ) / 73523802352), ((53129454157279777 : ℚ) / 13087236818656)], ![((-2256185730603014649 : ℚ) / 3934335074615), ((48164363454628957 : ℚ) / 7868670149230)], ![((-1364391281670048991 : ℚ) / 5182005525081), ((14552959769612555 : ℚ) / 5182005525081)], ![((739759743 : ℚ) / 1231637), ((-15707265 : ℚ) / 2463274)], ![((-2207302956 : ℚ) / 289434695), 0], ![((1855090660830459 : ℚ) / 698240704784546), ((-549793333651 : ℚ) / 698240704784546)]]], ![![![((-1168849454333 : ℚ) / 6119600126), ((87813280157 : ℚ) / 422252408694)], ![((-5638709144603 : ℚ) / 86322540976), ((30684066291 : ℚ) / 431612704880)], ![((-1962714530738477 : ℚ) / 14036448741273), ((2136622881676 : ℚ) / 14036448741273)], ![((-9937900607723 : ℚ) / 118872234936), ((10818101683 : ℚ) / 118872234936)], ![((-19947976 : ℚ) / 471801), 0], ![((680779 : ℚ) / 1343918), ((-741 : ℚ) / 1343918)], ![((-35426567385343 : ℚ) / 57163682750766092), ((38400127063 : ℚ) / 57163682750766092)]], ![![((-556511798550031 : ℚ) / 3059800063), ((41795128736425 : ℚ) / 211126204347)], ![((-5369944757858739 : ℚ) / 86322540976), ((29219294618603 : ℚ) / 431612704880)], ![((-1868975362635737900 : ℚ) / 14036448741273), ((2034168935503519 : ℚ) / 14036448741273)], ![((-9462618568773325 : ℚ) / 118872234936), ((10298901465773 : ℚ) / 118872234936)], ![((-6335952570 : ℚ) / 157267), 0], ![((324168975 : ℚ) / 671959), ((-352816 : ℚ) / 671959)], ![((-883032115390671 : ℚ) / 1504307440809634), ((957294012815 : ℚ) / 1504307440809634)]], ![![((-529938157429730728 : ℚ) / 3059800063), ((39794359383203056 : ℚ) / 211126204347)], ![((-5113606294614310947 : ℚ) / 86322540976), ((27822429969090779 : ℚ) / 431612704880)], ![((-1779738440155534350476 : ℚ) / 14036448741273), ((1936862765093257585 : ℚ) / 14036448741273)], ![((-9010643920680924575 : ℚ) / 118872234936), ((9806077902144871 : ℚ) / 118872234936)], ![((-6036777087300 : ℚ) / 157267), 0], ![((308696359200 : ℚ) / 671959), ((-335949761 : ℚ) / 671959)], ![((-22113586354483617 : ℚ) / 39587037916043), ((524851458637 : ℚ) / 866869443417)]]], ![![![((113984098597 : ℚ) / 89031079800), ((-235974529 : ℚ) / 178062159600)], ![((8203186090187 : ℚ) / 6997420908000), ((-51004950677 : ℚ) / 41984525448000)], ![((260037286511 : ℚ) / 193817988000), ((-536925427 : ℚ) / 387635976000)], ![((181705949 : ℚ) / 271728000), 0], ![((1062034128877 : ℚ) / 1315572444000), ((-6725161867 : ℚ) / 7893434664000)], ![((78769101000661 : ℚ) / 68925485964000), ((-488817953731 : ℚ) / 413552915784000)], ![((-3713 : ℚ) / 2664000), ((23 : ℚ) / 15984000)]], ![![((3086841787 : ℚ) / 294804900), ((576268741 : ℚ) / 589609800)], ![((11072502186809 : ℚ) / 1166236818000), ((6261434331661 : ℚ) / 6997420908000)], ![((46439843911 : ℚ) / 4614714000), ((66509256211 : ℚ) / 64605996000)], ![((22658284643 : ℚ) / 45288000), 0], ![((2306933481139 : ℚ) / 219262074000), ((786845851931 : ℚ) / 1315572444000)], ![((5530873045033 : ℚ) / 604609526000), ((3170706174257 : ℚ) / 3627657156000)], ![((-4991 : ℚ) / 444000), ((-2839 : ℚ) / 2664000)]], ![![((-1087741540973 : ℚ) / 147402450), ((68304799861 : ℚ) / 294804900)], ![((-1358168088212587 : ℚ) / 194372803000), ((248553765684727 : ℚ) / 1166236818000)], ![((-6185633813623 : ℚ) / 769119000), ((2635729600477 : ℚ) / 10767666000)], ![((802634557501 : ℚ) / 7548000), 0], ![((-96950834231027 : ℚ) / 36543679000), ((30497787631517 : ℚ) / 219262074000)], ![((-105336139215753 : ℚ) / 15910777000), ((6577413867621 : ℚ) / 31821554000)], ![((616063 : ℚ) / 74000), ((-112873 : ℚ) / 444000)]]]]

def normalBasisValueQ (q : Fin 3) (t : ℚ) : ℚ := ![1, t, t*t] q
def normalPairQ (a : Fin 2 → ℚ) (t : ℚ) : ℚ := a 0 + t*a 1

def edgeExpressionQ (c : Fin 4) (j : Fin 7) (a : Fin 7 → Fin 2 → ℚ) (t : ℚ) : ℚ :=
  if centerIndex c < j then
    normalPairQ (a (centerIndex c)) t + edgeLambdaQ (centerIndex c) j * normalPairQ (a j) t
  else
    edgeLambdaQ (centerIndex c) j * normalPairQ (a (centerIndex c)) t + normalPairQ (a j) t

/-- Solve the two normal equations over the rationals. -/
def solveTwoQ (t₀ t₁ r₀ r₁ : ℚ) : Fin 2 → ℚ :=
  let y := (r₁-r₀)/(t₁-t₀)
  ![r₀-t₀*y, y]

def computedCenterQ (c : Fin 4) (q : Fin 3) : Fin 2 → ℚ :=
  solveTwoQ (vertexSlopeQ (centerIndex c) 0) (vertexSlopeQ (centerIndex c) 1)
    (-normalBasisValueQ q (vertexSlopeQ (centerIndex c) 0) / vertexHeightQ (centerIndex c) 0)
    (-normalBasisValueQ q (vertexSlopeQ (centerIndex c) 1) / vertexHeightQ (centerIndex c) 1)

def computedEdgeRhsQ (c : Fin 4) (q : Fin 3) (j : Fin 7) (d : Fin 2) : ℚ :=
  let t := edgeSlopeQ (centerIndex c) j d
  let central := normalPairQ (computedCenterQ c q) t
  let quadratic := normalBasisValueQ q t / edgeHeightQ (centerIndex c) j d
  if centerIndex c < j then -(quadratic+central)/edgeLambdaQ (centerIndex c) j
  else -quadratic-edgeLambdaQ (centerIndex c) j*central

/-- The rational version of the primitive-data lift algorithm. -/
def computedCoefficientsQ (c : Fin 4) (q : Fin 3) (j : Fin 7) : Fin 2 → ℚ :=
  if j = centerIndex c then computedCenterQ c q
  else if singleEdge (centerIndex c) j then ![computedEdgeRhsQ c q j 0, 0]
  else solveTwoQ (edgeSlopeQ (centerIndex c) j 0) (edgeSlopeQ (centerIndex c) j 1)
    (computedEdgeRhsQ c q j 0) (computedEdgeRhsQ c q j 1)

theorem computedCoefficientsQ_eq : ∀ c q j k,
    computedCoefficientsQ c q j k = liftCoefficientsQ c q j k := by decide +kernel

theorem vertexHeightQ_ne_zero : ∀ i d, vertexHeightQ i d ≠ 0 := by decide +kernel
theorem edgeHeightQ_ne_zero : ∀ i j d, edgeHeightQ i j d ≠ 0 := by decide +kernel
theorem edgeLambdaQ_ne_zero : ∀ i j, edgeLambdaQ i j ≠ 0 := by decide +kernel
theorem vertexSlopeQ_ne : ∀ i, vertexSlopeQ i 0 ≠ vertexSlopeQ i 1 := by decide +kernel
theorem edgeSlopeQ_ne : ∀ i j, i ≠ j → singleEdge i j = false →
    edgeSlopeQ i j 0 ≠ edgeSlopeQ i j 1 := by decide +kernel

/-- The exact rational lifts satisfy every vertex equation. -/
theorem lift_vertex_equationsQ : ∀ c q d,
    vertexHeightQ (centerIndex c) d *
      normalPairQ (liftCoefficientsQ c q (centerIndex c)) (vertexSlopeQ (centerIndex c) d) +
      normalBasisValueQ q (vertexSlopeQ (centerIndex c) d) = 0 := by decide +kernel

/-- The exact rational lifts satisfy every incident edge equation. -/
theorem lift_edge_equationsQ : ∀ c q j d, j ≠ centerIndex c → edgeSlot (centerIndex c) j d →
    edgeHeightQ (centerIndex c) j d *
      edgeExpressionQ c j (liftCoefficientsQ c q) (edgeSlopeQ (centerIndex c) j d) +
      normalBasisValueQ q (edgeSlopeQ (centerIndex c) j d) = 0 := by decide +kernel

theorem lift_single_gaugeQ : ∀ c q j, j ≠ centerIndex c → singleEdge (centerIndex c) j = true →
    liftCoefficientsQ c q j 1 = 0 := by decide +kernel

/-- The rational lift extends linearly to every normal quadratic. -/
def linearLiftQ (Q : Fin 3 → ℚ) (c : Fin 4) (j : Fin 7) (k : Fin 2) : ℚ :=
  ∑ q, Q q * liftCoefficientsQ c q j k

def quadraticValueQ (Q : Fin 3 → ℚ) (t : ℚ) : ℚ :=
  ∑ q, Q q * normalBasisValueQ q t

theorem linearLiftQ_vertex (Q : Fin 3 → ℚ) (c : Fin 4) (d : Fin 2) :
    vertexHeightQ (centerIndex c) d *
      normalPairQ (linearLiftQ Q c (centerIndex c)) (vertexSlopeQ (centerIndex c) d) +
      quadraticValueQ Q (vertexSlopeQ (centerIndex c) d) = 0 := by
  have h0 := lift_vertex_equationsQ c 0 d
  have h1 := lift_vertex_equationsQ c 1 d
  have h2 := lift_vertex_equationsQ c 2 d
  simp only [linearLiftQ, quadraticValueQ, normalPairQ, Fin.sum_univ_three] at *
  linear_combination Q 0 * h0 + Q 1 * h1 + Q 2 * h2

theorem linearLiftQ_edge (Q : Fin 3 → ℚ) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    edgeHeightQ (centerIndex c) j d *
      edgeExpressionQ c j (linearLiftQ Q c) (edgeSlopeQ (centerIndex c) j d) +
      quadraticValueQ Q (edgeSlopeQ (centerIndex c) j d) = 0 := by
  have h0 := lift_edge_equationsQ c 0 j d hj hd
  have h1 := lift_edge_equationsQ c 1 j d hj hd
  have h2 := lift_edge_equationsQ c 2 j d hj hd
  simp only [edgeExpressionQ] at *
  split_ifs at * <;>
    simp only [linearLiftQ, quadraticValueQ, normalPairQ, Fin.sum_univ_three] at * <;>
    linear_combination Q 0 * h0 + Q 1 * h1 + Q 2 * h2

theorem linearLiftQ_single_gauge (Q : Fin 3 → ℚ) (c : Fin 4) (j : Fin 7)
    (hj : j ≠ centerIndex c) (hs : singleEdge (centerIndex c) j = true) :
    linearLiftQ Q c j 1 = 0 := by
  simp [linearLiftQ, lift_single_gaugeQ c _ j hj hs]

def normalQuadraticValueQ (Q : Fin 3 → ℚ) (s t : ℚ) : ℚ :=
  Q 0 * s * s + Q 1 * s * t + Q 2 * t * t

@[simp] theorem normalQuadraticValue_oneQ (Q : Fin 3 → ℚ) (t : ℚ) :
    normalQuadraticValueQ Q 1 t = quadraticValueQ Q t := by
  simp [normalQuadraticValueQ, quadraticValueQ, normalBasisValueQ, Fin.sum_univ_three]
  ring

/-- Evaluate the cubic `y_c (Q(s,t) + s L_c(Q)_s(y) + t L_c(Q)_t(y))`. -/
def liftedCubicValueQ (Q : Fin 3 → ℚ) (c : Fin 4) (s t : ℚ) (y : Fin 7 → ℚ) : ℚ :=
  y (centerIndex c) * (normalQuadraticValueQ Q s t +
    ∑ j, y j * (s * linearLiftQ Q c j 0 + t * linearLiftQ Q c j 1))

/-- The trace coordinates `μ e_i` of an actual vertex cone point. -/
def vertexTracePointQ (i : Fin 7) (d : Fin 2) (j : Fin 7) : ℚ :=
  if j = i then vertexHeightQ i d else 0

/-- The trace coordinates `μ (e_low + λ e_high)` of an actual incident edge cone point. -/
def incidentTracePointQ (c : Fin 4) (j : Fin 7) (d : Fin 2) (k : Fin 7) : ℚ :=
  let mu := edgeHeightQ (centerIndex c) j d
  let lam := edgeLambdaQ (centerIndex c) j
  if centerIndex c < j then
    (if k = centerIndex c then mu else 0) + (if k = j then mu * lam else 0)
  else
    (if k = j then mu else 0) + (if k = centerIndex c then mu * lam else 0)

/-- Every vertex cone point annihilates every chosen cubic lift. -/
theorem liftedCubicValue_vertexQ (Q : Fin 3 → ℚ) (c : Fin 4) (i : Fin 7) (d : Fin 2) :
    liftedCubicValueQ Q c 1 (vertexSlopeQ i d) (vertexTracePointQ i d) = 0 := by
  by_cases hc : centerIndex c = i
  · subst i
    have h := linearLiftQ_vertex Q c d
    simp only [normalPairQ] at h
    simp [-mul_eq_zero, liftedCubicValueQ, vertexTracePointQ, normalQuadraticValue_oneQ, ite_mul]
    linear_combination vertexHeightQ (centerIndex c) d * h
  · simp [liftedCubicValueQ, vertexTracePointQ, hc]

/-- At an incident edge, cubic evaluation is the cleared equation (B.4) times `y_c`. -/
theorem liftedCubicValue_incident_formulaQ (Q : Fin 3 → ℚ) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (t : ℚ) (hj : j ≠ centerIndex c) :
    liftedCubicValueQ Q c 1 t (incidentTracePointQ c j d) =
      incidentTracePointQ c j d (centerIndex c) *
        (quadraticValueQ Q t + edgeHeightQ (centerIndex c) j d *
          edgeExpressionQ c j (linearLiftQ Q c) t) := by
  by_cases hlt : centerIndex c < j
  · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff, liftedCubicValueQ, incidentTracePointQ, hlt, Ne.symm hj,
      add_mul, ite_mul, Finset.sum_add_distrib, edgeExpressionQ, normalPairQ]
    ring
  · simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff, liftedCubicValueQ, incidentTracePointQ, hlt, Ne.symm hj,
      add_mul, ite_mul, Finset.sum_add_distrib, edgeExpressionQ, normalPairQ]
    ring

/-- Every incident edge cone point annihilates the chosen cubic lift. -/
theorem liftedCubicValue_incidentQ (Q : Fin 3 → ℚ) (c : Fin 4) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    liftedCubicValueQ Q c 1 (edgeSlopeQ (centerIndex c) j d) (incidentTracePointQ c j d) = 0 := by
  rw [liftedCubicValue_incident_formulaQ Q c j d _ hj]
  have h := linearLiftQ_edge Q c j d hj hd
  rw [add_comm] at h
  rw [h, mul_zero]

/-- The cubic lift vanishes on the trace plane. -/
theorem liftedCubicValue_traceQ (Q : Fin 3 → ℚ) (c : Fin 4) (y : Fin 7 → ℚ) :
    liftedCubicValueQ Q c 0 0 y = 0 := by
  simp [liftedCubicValueQ, normalQuadraticValueQ]


/-- Restriction to old trace coordinates. -/
def restrictedLiftCoefficientsQ : PairLiftCoefficients ℚ :=
  fun c q i k => liftCoefficientsQ c q (Fin.castAdd 2 i) k

/-- The same thirteen trace points and direction weights, lifted to integers. -/
def samplePointsQ : Matrix (Fin 13) (Fin 7) ℚ :=
  !![322, 985, 489, 715, 584, 19, 818;
    747, 56, 603, 674, 829, 204, 520;
    386, 839, 409, 877, 410, 877, 967;
    83, 709, 562, 589, 47, 548, 430;
    941, 797, 281, 868, 517, 159, 407;
    687, 378, 770, 921, 741, 795, 615;
    616, 235, 629, 330, 818, 900, 548;
    117, 170, 312, 105, 444, 290, 307;
    375, 413, 846, 991, 744, 103, 649;
    324, 726, 933, 368, 117, 531, 21;
    302, 35, 190, 887, 255, 979, 743;
    180, 226, 366, 253, 233, 813, 79;
    130, 24, 154, 624, 671, 108, 910]

def rowPointQ (r : Fin 26) : Fin 7 → ℚ :=
  samplePointsQ ⟨r.val / 2, by have := r.isLt; omega⟩

def rowComponentQ (r : Fin 26) : Fin 2 :=
  ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Evaluation of the actual rational polynomial construction. -/
def constructionMatrixQ : Matrix (Fin 26) (Fin 26) ℚ :=
  Matrix.of fun r c => functionColumn restrictedLiftCoefficientsQ 810 479 c
    (rowPointQ r) (rowComponentQ r)

private theorem constructionMatrixQ_row_0 :
    ∀ c, constructionMatrixQ 0 c = RationalCertificate.rationalEvaluation 0 c := by
  decide +kernel

private theorem constructionMatrixQ_row_1 :
    ∀ c, constructionMatrixQ 1 c = RationalCertificate.rationalEvaluation 1 c := by
  decide +kernel

private theorem constructionMatrixQ_row_2 :
    ∀ c, constructionMatrixQ 2 c = RationalCertificate.rationalEvaluation 2 c := by
  decide +kernel

private theorem constructionMatrixQ_row_3 :
    ∀ c, constructionMatrixQ 3 c = RationalCertificate.rationalEvaluation 3 c := by
  decide +kernel

private theorem constructionMatrixQ_row_4 :
    ∀ c, constructionMatrixQ 4 c = RationalCertificate.rationalEvaluation 4 c := by
  decide +kernel

private theorem constructionMatrixQ_row_5 :
    ∀ c, constructionMatrixQ 5 c = RationalCertificate.rationalEvaluation 5 c := by
  decide +kernel

private theorem constructionMatrixQ_row_6 :
    ∀ c, constructionMatrixQ 6 c = RationalCertificate.rationalEvaluation 6 c := by
  decide +kernel

private theorem constructionMatrixQ_row_7 :
    ∀ c, constructionMatrixQ 7 c = RationalCertificate.rationalEvaluation 7 c := by
  decide +kernel

private theorem constructionMatrixQ_row_8 :
    ∀ c, constructionMatrixQ 8 c = RationalCertificate.rationalEvaluation 8 c := by
  decide +kernel

private theorem constructionMatrixQ_row_9 :
    ∀ c, constructionMatrixQ 9 c = RationalCertificate.rationalEvaluation 9 c := by
  decide +kernel

private theorem constructionMatrixQ_row_10 :
    ∀ c, constructionMatrixQ 10 c = RationalCertificate.rationalEvaluation 10 c := by
  decide +kernel

private theorem constructionMatrixQ_row_11 :
    ∀ c, constructionMatrixQ 11 c = RationalCertificate.rationalEvaluation 11 c := by
  decide +kernel

private theorem constructionMatrixQ_row_12 :
    ∀ c, constructionMatrixQ 12 c = RationalCertificate.rationalEvaluation 12 c := by
  decide +kernel

private theorem constructionMatrixQ_row_13 :
    ∀ c, constructionMatrixQ 13 c = RationalCertificate.rationalEvaluation 13 c := by
  decide +kernel

private theorem constructionMatrixQ_row_14 :
    ∀ c, constructionMatrixQ 14 c = RationalCertificate.rationalEvaluation 14 c := by
  decide +kernel

private theorem constructionMatrixQ_row_15 :
    ∀ c, constructionMatrixQ 15 c = RationalCertificate.rationalEvaluation 15 c := by
  decide +kernel

private theorem constructionMatrixQ_row_16 :
    ∀ c, constructionMatrixQ 16 c = RationalCertificate.rationalEvaluation 16 c := by
  decide +kernel

private theorem constructionMatrixQ_row_17 :
    ∀ c, constructionMatrixQ 17 c = RationalCertificate.rationalEvaluation 17 c := by
  decide +kernel

private theorem constructionMatrixQ_row_18 :
    ∀ c, constructionMatrixQ 18 c = RationalCertificate.rationalEvaluation 18 c := by
  decide +kernel

private theorem constructionMatrixQ_row_19 :
    ∀ c, constructionMatrixQ 19 c = RationalCertificate.rationalEvaluation 19 c := by
  decide +kernel

private theorem constructionMatrixQ_row_20 :
    ∀ c, constructionMatrixQ 20 c = RationalCertificate.rationalEvaluation 20 c := by
  decide +kernel

private theorem constructionMatrixQ_row_21 :
    ∀ c, constructionMatrixQ 21 c = RationalCertificate.rationalEvaluation 21 c := by
  decide +kernel

private theorem constructionMatrixQ_row_22 :
    ∀ c, constructionMatrixQ 22 c = RationalCertificate.rationalEvaluation 22 c := by
  decide +kernel

private theorem constructionMatrixQ_row_23 :
    ∀ c, constructionMatrixQ 23 c = RationalCertificate.rationalEvaluation 23 c := by
  decide +kernel

private theorem constructionMatrixQ_row_24 :
    ∀ c, constructionMatrixQ 24 c = RationalCertificate.rationalEvaluation 24 c := by
  decide +kernel

private theorem constructionMatrixQ_row_25 :
    ∀ c, constructionMatrixQ 25 c = RationalCertificate.rationalEvaluation 25 c := by
  decide +kernel

/-- The actual rational construction is the certified row-scaled matrix. -/
theorem constructionMatrixQ_eq : constructionMatrixQ = RationalCertificate.rationalEvaluation := by
  ext r c
  fin_cases r
  · exact constructionMatrixQ_row_0 c
  · exact constructionMatrixQ_row_1 c
  · exact constructionMatrixQ_row_2 c
  · exact constructionMatrixQ_row_3 c
  · exact constructionMatrixQ_row_4 c
  · exact constructionMatrixQ_row_5 c
  · exact constructionMatrixQ_row_6 c
  · exact constructionMatrixQ_row_7 c
  · exact constructionMatrixQ_row_8 c
  · exact constructionMatrixQ_row_9 c
  · exact constructionMatrixQ_row_10 c
  · exact constructionMatrixQ_row_11 c
  · exact constructionMatrixQ_row_12 c
  · exact constructionMatrixQ_row_13 c
  · exact constructionMatrixQ_row_14 c
  · exact constructionMatrixQ_row_15 c
  · exact constructionMatrixQ_row_16 c
  · exact constructionMatrixQ_row_17 c
  · exact constructionMatrixQ_row_18 c
  · exact constructionMatrixQ_row_19 c
  · exact constructionMatrixQ_row_20 c
  · exact constructionMatrixQ_row_21 c
  · exact constructionMatrixQ_row_22 c
  · exact constructionMatrixQ_row_23 c
  · exact constructionMatrixQ_row_24 c
  · exact constructionMatrixQ_row_25 c


theorem constructionMatrixQ_det_ne_zero : constructionMatrixQ.det ≠ 0 := by
  rw [constructionMatrixQ_eq]
  exact RationalCertificate.rationalEvaluation_det_ne_zero

/-- The actual rational pair columns are linearly independent. -/
theorem pairColumnsQ_linearIndependent :
    LinearIndependent ℚ (polynomialColumn restrictedLiftCoefficientsQ 810 479) := by
  apply polynomialColumn_linearIndependent_of_matrix restrictedLiftCoefficientsQ 810 479
    rowPointQ rowComponentQ constructionMatrixQ
  · intro r c
    rfl
  · exact constructionMatrixQ_det_ne_zero

/-- The same explicit construction works over every characteristic-zero field. -/
theorem pairColumns_linearIndependent_over (K : Type*) [Field K] [CharZero K] :
    LinearIndependent K
      (polynomialColumn
        (fun a q j k => (restrictedLiftCoefficientsQ a q j k : K)) (810 : K) (479 : K)) := by
  let f : ℚ →+* K := Rat.castHom K
  let A : Matrix (Fin 26) (Fin 26) K := constructionMatrixQ.map f
  apply polynomialColumn_linearIndependent_of_matrix
    (fun a q j k => (restrictedLiftCoefficientsQ a q j k : K)) (810 : K) (479 : K)
    (fun r i => (rowPointQ r i : K)) rowComponentQ A
  · intro r c
    have h := map_functionColumn f restrictedLiftCoefficientsQ 810 479 c
      (rowPointQ r) (rowComponentQ r)
    simpa [A, f, constructionMatrixQ] using h.symm
  · change (constructionMatrixQ.map (fun x : ℚ => (x : K))).det ≠ 0
    rw [← Rat.cast_det]
    exact_mod_cast constructionMatrixQ_det_ne_zero

/-- Restricted rational coefficients obtained directly from the primitive equations. -/
def primitiveLiftCoefficientsQ : PairLiftCoefficients ℚ :=
  fun c q i k => computedCoefficientsQ c q (Fin.castAdd 2 i) k

theorem primitiveLiftCoefficientsQ_eq : primitiveLiftCoefficientsQ = restrictedLiftCoefficientsQ := by
  funext c q i k
  exact computedCoefficientsQ_eq c q (Fin.castAdd 2 i) k

/-- The prescribed primitive-parameter construction gives independent columns
in every characteristic-zero field. -/
theorem primitivePairColumns_linearIndependent_over (K : Type*) [Field K] [CharZero K] :
    LinearIndependent K
      (polynomialColumn
        (fun a q j k => (primitiveLiftCoefficientsQ a q j k : K)) (810 : K) (479 : K)) := by
  simpa only [primitiveLiftCoefficientsQ_eq] using pairColumns_linearIndependent_over K

end IdealGeneration.CubicPair.RationalConstruction
