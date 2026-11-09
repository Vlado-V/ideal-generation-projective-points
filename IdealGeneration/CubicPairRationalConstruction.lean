module

public import IdealGeneration.CertifiedFinCases
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

private theorem solveTwoQ_eq_of_normalPair (t r : Fin 2 → ℚ) (a : Fin 2 → ℚ)
    (ht : t 0 ≠ t 1) (h : ∀ d, normalPairQ a (t d) = r d) :
    solveTwoQ (t 0) (t 1) (r 0) (r 1) = a := by
  have h₀ := h 0
  have h₁ := h 1
  simp only [normalPairQ] at h₀ h₁
  have hslope : (r 1 - r 0) / (t 1 - t 0) = a 1 := by
    apply (div_eq_iff (sub_ne_zero.mpr ht.symm)).2
    linear_combination h₀ - h₁
  funext k
  fin_cases k
  · change r 0 - t 0 * ((r 1 - r 0) / (t 1 - t 0)) = a 0
    rw [hslope]
    linear_combination -h₀
  · exact hslope

private theorem computedCenterQ_eq_of_vertex (c : Fin 4) (q : Fin 3) :
    computedCenterQ c q = liftCoefficientsQ c q (centerIndex c) := by
  exact solveTwoQ_eq_of_normalPair (vertexSlopeQ (centerIndex c))
    (fun d => -normalBasisValueQ q (vertexSlopeQ (centerIndex c) d) /
      vertexHeightQ (centerIndex c) d)
    (liftCoefficientsQ c q (centerIndex c)) (vertexSlopeQ_ne (centerIndex c)) fun d => by
      apply (eq_div_iff (vertexHeightQ_ne_zero (centerIndex c) d)).2
      linear_combination lift_vertex_equationsQ c q d

private theorem computedEdgeRhsQ_eq_of_edge (c : Fin 4) (q : Fin 3) (j : Fin 7) (d : Fin 2)
    (hj : j ≠ centerIndex c) (hd : edgeSlot (centerIndex c) j d) :
    normalPairQ (liftCoefficientsQ c q j) (edgeSlopeQ (centerIndex c) j d) =
      computedEdgeRhsQ c q j d := by
  have hedge : edgeExpressionQ c j (liftCoefficientsQ c q) (edgeSlopeQ (centerIndex c) j d) =
      -(normalBasisValueQ q (edgeSlopeQ (centerIndex c) j d) /
        edgeHeightQ (centerIndex c) j d) := by
    rw [← neg_div]
    apply (eq_div_iff (edgeHeightQ_ne_zero (centerIndex c) j d)).2
    linear_combination lift_edge_equationsQ c q j d hj hd
  unfold computedEdgeRhsQ
  rw [computedCenterQ_eq_of_vertex]
  by_cases hlt : centerIndex c < j
  · rw [ite_eq_left hlt]
    simp only [edgeExpressionQ, ite_eq_left hlt] at hedge
    apply (eq_div_iff (edgeLambdaQ_ne_zero (centerIndex c) j)).2
    linear_combination hedge
  · rw [ite_eq_right hlt]
    simp only [edgeExpressionQ, ite_eq_right hlt] at hedge
    linear_combination hedge

theorem computedCoefficientsQ_eq : ∀ c q j k,
    computedCoefficientsQ c q j k = liftCoefficientsQ c q j k := by
  intro c q j k
  apply congrFun ?_ k
  by_cases hj : j = centerIndex c
  · subst j
    rw [computedCoefficientsQ, ite_eq_left rfl]
    exact computedCenterQ_eq_of_vertex c q
  · rw [computedCoefficientsQ, ite_eq_right hj]
    by_cases hs : singleEdge (centerIndex c) j = true
    · rw [ite_eq_left hs]
      have h₀ := computedEdgeRhsQ_eq_of_edge c q j 0 hj (Or.inr rfl)
      have h₁ := lift_single_gaugeQ c q j hj hs
      rw [normalPairQ, h₁, mul_zero, add_zero] at h₀
      funext d
      fin_cases d
      · exact h₀.symm
      · exact h₁.symm
    · rw [ite_eq_right hs]
      have hf := Bool.eq_false_of_not_eq_true hs
      exact solveTwoQ_eq_of_normalPair (edgeSlopeQ (centerIndex c) j) (computedEdgeRhsQ c q j)
        (liftCoefficientsQ c q j) (edgeSlopeQ_ne (centerIndex c) j (Ne.symm hj) hf)
        (fun d => computedEdgeRhsQ_eq_of_edge c q j d hj (Or.inl hf))

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

set_option Elab.async false

local macro "check_rational_matrix_entry" : tactic => `(tactic|
  (norm_num [constructionMatrixQ, functionColumn, rowPointQ, rowComponentQ, halfFaceValue,
    RationalCertificate.rationalEvaluation];
   norm_num [basisLiftValue, restrictedLiftCoefficientsQ, samplePointsQ, liftCoefficientsQ,
    Fin.sum_univ_succ, RationalCertificate.integralEvaluation, RationalCertificate.rowScale]))

private theorem constructionMatrixQ_entry_0_0 :
    constructionMatrixQ 0 0 = RationalCertificate.rationalEvaluation 0 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_1 :
    constructionMatrixQ 0 1 = RationalCertificate.rationalEvaluation 0 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_2 :
    constructionMatrixQ 0 2 = RationalCertificate.rationalEvaluation 0 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_3 :
    constructionMatrixQ 0 3 = RationalCertificate.rationalEvaluation 0 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_4 :
    constructionMatrixQ 0 4 = RationalCertificate.rationalEvaluation 0 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_5 :
    constructionMatrixQ 0 5 = RationalCertificate.rationalEvaluation 0 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_6 :
    constructionMatrixQ 0 6 = RationalCertificate.rationalEvaluation 0 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_7 :
    constructionMatrixQ 0 7 = RationalCertificate.rationalEvaluation 0 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_8 :
    constructionMatrixQ 0 8 = RationalCertificate.rationalEvaluation 0 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_9 :
    constructionMatrixQ 0 9 = RationalCertificate.rationalEvaluation 0 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_10 :
    constructionMatrixQ 0 10 = RationalCertificate.rationalEvaluation 0 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_11 :
    constructionMatrixQ 0 11 = RationalCertificate.rationalEvaluation 0 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_12 :
    constructionMatrixQ 0 12 = RationalCertificate.rationalEvaluation 0 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_13 :
    constructionMatrixQ 0 13 = RationalCertificate.rationalEvaluation 0 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_14 :
    constructionMatrixQ 0 14 = RationalCertificate.rationalEvaluation 0 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_15 :
    constructionMatrixQ 0 15 = RationalCertificate.rationalEvaluation 0 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_16 :
    constructionMatrixQ 0 16 = RationalCertificate.rationalEvaluation 0 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_17 :
    constructionMatrixQ 0 17 = RationalCertificate.rationalEvaluation 0 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_18 :
    constructionMatrixQ 0 18 = RationalCertificate.rationalEvaluation 0 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_19 :
    constructionMatrixQ 0 19 = RationalCertificate.rationalEvaluation 0 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_20 :
    constructionMatrixQ 0 20 = RationalCertificate.rationalEvaluation 0 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_21 :
    constructionMatrixQ 0 21 = RationalCertificate.rationalEvaluation 0 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_22 :
    constructionMatrixQ 0 22 = RationalCertificate.rationalEvaluation 0 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_23 :
    constructionMatrixQ 0 23 = RationalCertificate.rationalEvaluation 0 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_24 :
    constructionMatrixQ 0 24 = RationalCertificate.rationalEvaluation 0 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_0_25 :
    constructionMatrixQ 0 25 = RationalCertificate.rationalEvaluation 0 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_0 :
    ∀ c, constructionMatrixQ 0 c = RationalCertificate.rationalEvaluation 0 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_0_25))))))

private theorem constructionMatrixQ_entry_1_0 :
    constructionMatrixQ 1 0 = RationalCertificate.rationalEvaluation 1 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_1 :
    constructionMatrixQ 1 1 = RationalCertificate.rationalEvaluation 1 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_2 :
    constructionMatrixQ 1 2 = RationalCertificate.rationalEvaluation 1 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_3 :
    constructionMatrixQ 1 3 = RationalCertificate.rationalEvaluation 1 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_4 :
    constructionMatrixQ 1 4 = RationalCertificate.rationalEvaluation 1 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_5 :
    constructionMatrixQ 1 5 = RationalCertificate.rationalEvaluation 1 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_6 :
    constructionMatrixQ 1 6 = RationalCertificate.rationalEvaluation 1 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_7 :
    constructionMatrixQ 1 7 = RationalCertificate.rationalEvaluation 1 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_8 :
    constructionMatrixQ 1 8 = RationalCertificate.rationalEvaluation 1 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_9 :
    constructionMatrixQ 1 9 = RationalCertificate.rationalEvaluation 1 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_10 :
    constructionMatrixQ 1 10 = RationalCertificate.rationalEvaluation 1 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_11 :
    constructionMatrixQ 1 11 = RationalCertificate.rationalEvaluation 1 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_12 :
    constructionMatrixQ 1 12 = RationalCertificate.rationalEvaluation 1 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_13 :
    constructionMatrixQ 1 13 = RationalCertificate.rationalEvaluation 1 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_14 :
    constructionMatrixQ 1 14 = RationalCertificate.rationalEvaluation 1 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_15 :
    constructionMatrixQ 1 15 = RationalCertificate.rationalEvaluation 1 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_16 :
    constructionMatrixQ 1 16 = RationalCertificate.rationalEvaluation 1 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_17 :
    constructionMatrixQ 1 17 = RationalCertificate.rationalEvaluation 1 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_18 :
    constructionMatrixQ 1 18 = RationalCertificate.rationalEvaluation 1 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_19 :
    constructionMatrixQ 1 19 = RationalCertificate.rationalEvaluation 1 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_20 :
    constructionMatrixQ 1 20 = RationalCertificate.rationalEvaluation 1 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_21 :
    constructionMatrixQ 1 21 = RationalCertificate.rationalEvaluation 1 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_22 :
    constructionMatrixQ 1 22 = RationalCertificate.rationalEvaluation 1 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_23 :
    constructionMatrixQ 1 23 = RationalCertificate.rationalEvaluation 1 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_24 :
    constructionMatrixQ 1 24 = RationalCertificate.rationalEvaluation 1 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_1_25 :
    constructionMatrixQ 1 25 = RationalCertificate.rationalEvaluation 1 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_1 :
    ∀ c, constructionMatrixQ 1 c = RationalCertificate.rationalEvaluation 1 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_1_25))))))

private theorem constructionMatrixQ_entry_2_0 :
    constructionMatrixQ 2 0 = RationalCertificate.rationalEvaluation 2 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_1 :
    constructionMatrixQ 2 1 = RationalCertificate.rationalEvaluation 2 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_2 :
    constructionMatrixQ 2 2 = RationalCertificate.rationalEvaluation 2 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_3 :
    constructionMatrixQ 2 3 = RationalCertificate.rationalEvaluation 2 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_4 :
    constructionMatrixQ 2 4 = RationalCertificate.rationalEvaluation 2 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_5 :
    constructionMatrixQ 2 5 = RationalCertificate.rationalEvaluation 2 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_6 :
    constructionMatrixQ 2 6 = RationalCertificate.rationalEvaluation 2 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_7 :
    constructionMatrixQ 2 7 = RationalCertificate.rationalEvaluation 2 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_8 :
    constructionMatrixQ 2 8 = RationalCertificate.rationalEvaluation 2 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_9 :
    constructionMatrixQ 2 9 = RationalCertificate.rationalEvaluation 2 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_10 :
    constructionMatrixQ 2 10 = RationalCertificate.rationalEvaluation 2 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_11 :
    constructionMatrixQ 2 11 = RationalCertificate.rationalEvaluation 2 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_12 :
    constructionMatrixQ 2 12 = RationalCertificate.rationalEvaluation 2 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_13 :
    constructionMatrixQ 2 13 = RationalCertificate.rationalEvaluation 2 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_14 :
    constructionMatrixQ 2 14 = RationalCertificate.rationalEvaluation 2 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_15 :
    constructionMatrixQ 2 15 = RationalCertificate.rationalEvaluation 2 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_16 :
    constructionMatrixQ 2 16 = RationalCertificate.rationalEvaluation 2 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_17 :
    constructionMatrixQ 2 17 = RationalCertificate.rationalEvaluation 2 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_18 :
    constructionMatrixQ 2 18 = RationalCertificate.rationalEvaluation 2 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_19 :
    constructionMatrixQ 2 19 = RationalCertificate.rationalEvaluation 2 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_20 :
    constructionMatrixQ 2 20 = RationalCertificate.rationalEvaluation 2 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_21 :
    constructionMatrixQ 2 21 = RationalCertificate.rationalEvaluation 2 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_22 :
    constructionMatrixQ 2 22 = RationalCertificate.rationalEvaluation 2 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_23 :
    constructionMatrixQ 2 23 = RationalCertificate.rationalEvaluation 2 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_24 :
    constructionMatrixQ 2 24 = RationalCertificate.rationalEvaluation 2 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_2_25 :
    constructionMatrixQ 2 25 = RationalCertificate.rationalEvaluation 2 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_2 :
    ∀ c, constructionMatrixQ 2 c = RationalCertificate.rationalEvaluation 2 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_2_25))))))

private theorem constructionMatrixQ_entry_3_0 :
    constructionMatrixQ 3 0 = RationalCertificate.rationalEvaluation 3 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_1 :
    constructionMatrixQ 3 1 = RationalCertificate.rationalEvaluation 3 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_2 :
    constructionMatrixQ 3 2 = RationalCertificate.rationalEvaluation 3 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_3 :
    constructionMatrixQ 3 3 = RationalCertificate.rationalEvaluation 3 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_4 :
    constructionMatrixQ 3 4 = RationalCertificate.rationalEvaluation 3 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_5 :
    constructionMatrixQ 3 5 = RationalCertificate.rationalEvaluation 3 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_6 :
    constructionMatrixQ 3 6 = RationalCertificate.rationalEvaluation 3 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_7 :
    constructionMatrixQ 3 7 = RationalCertificate.rationalEvaluation 3 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_8 :
    constructionMatrixQ 3 8 = RationalCertificate.rationalEvaluation 3 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_9 :
    constructionMatrixQ 3 9 = RationalCertificate.rationalEvaluation 3 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_10 :
    constructionMatrixQ 3 10 = RationalCertificate.rationalEvaluation 3 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_11 :
    constructionMatrixQ 3 11 = RationalCertificate.rationalEvaluation 3 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_12 :
    constructionMatrixQ 3 12 = RationalCertificate.rationalEvaluation 3 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_13 :
    constructionMatrixQ 3 13 = RationalCertificate.rationalEvaluation 3 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_14 :
    constructionMatrixQ 3 14 = RationalCertificate.rationalEvaluation 3 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_15 :
    constructionMatrixQ 3 15 = RationalCertificate.rationalEvaluation 3 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_16 :
    constructionMatrixQ 3 16 = RationalCertificate.rationalEvaluation 3 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_17 :
    constructionMatrixQ 3 17 = RationalCertificate.rationalEvaluation 3 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_18 :
    constructionMatrixQ 3 18 = RationalCertificate.rationalEvaluation 3 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_19 :
    constructionMatrixQ 3 19 = RationalCertificate.rationalEvaluation 3 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_20 :
    constructionMatrixQ 3 20 = RationalCertificate.rationalEvaluation 3 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_21 :
    constructionMatrixQ 3 21 = RationalCertificate.rationalEvaluation 3 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_22 :
    constructionMatrixQ 3 22 = RationalCertificate.rationalEvaluation 3 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_23 :
    constructionMatrixQ 3 23 = RationalCertificate.rationalEvaluation 3 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_24 :
    constructionMatrixQ 3 24 = RationalCertificate.rationalEvaluation 3 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_3_25 :
    constructionMatrixQ 3 25 = RationalCertificate.rationalEvaluation 3 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_3 :
    ∀ c, constructionMatrixQ 3 c = RationalCertificate.rationalEvaluation 3 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_3_25))))))

private theorem constructionMatrixQ_entry_4_0 :
    constructionMatrixQ 4 0 = RationalCertificate.rationalEvaluation 4 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_1 :
    constructionMatrixQ 4 1 = RationalCertificate.rationalEvaluation 4 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_2 :
    constructionMatrixQ 4 2 = RationalCertificate.rationalEvaluation 4 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_3 :
    constructionMatrixQ 4 3 = RationalCertificate.rationalEvaluation 4 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_4 :
    constructionMatrixQ 4 4 = RationalCertificate.rationalEvaluation 4 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_5 :
    constructionMatrixQ 4 5 = RationalCertificate.rationalEvaluation 4 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_6 :
    constructionMatrixQ 4 6 = RationalCertificate.rationalEvaluation 4 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_7 :
    constructionMatrixQ 4 7 = RationalCertificate.rationalEvaluation 4 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_8 :
    constructionMatrixQ 4 8 = RationalCertificate.rationalEvaluation 4 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_9 :
    constructionMatrixQ 4 9 = RationalCertificate.rationalEvaluation 4 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_10 :
    constructionMatrixQ 4 10 = RationalCertificate.rationalEvaluation 4 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_11 :
    constructionMatrixQ 4 11 = RationalCertificate.rationalEvaluation 4 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_12 :
    constructionMatrixQ 4 12 = RationalCertificate.rationalEvaluation 4 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_13 :
    constructionMatrixQ 4 13 = RationalCertificate.rationalEvaluation 4 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_14 :
    constructionMatrixQ 4 14 = RationalCertificate.rationalEvaluation 4 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_15 :
    constructionMatrixQ 4 15 = RationalCertificate.rationalEvaluation 4 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_16 :
    constructionMatrixQ 4 16 = RationalCertificate.rationalEvaluation 4 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_17 :
    constructionMatrixQ 4 17 = RationalCertificate.rationalEvaluation 4 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_18 :
    constructionMatrixQ 4 18 = RationalCertificate.rationalEvaluation 4 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_19 :
    constructionMatrixQ 4 19 = RationalCertificate.rationalEvaluation 4 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_20 :
    constructionMatrixQ 4 20 = RationalCertificate.rationalEvaluation 4 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_21 :
    constructionMatrixQ 4 21 = RationalCertificate.rationalEvaluation 4 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_22 :
    constructionMatrixQ 4 22 = RationalCertificate.rationalEvaluation 4 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_23 :
    constructionMatrixQ 4 23 = RationalCertificate.rationalEvaluation 4 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_24 :
    constructionMatrixQ 4 24 = RationalCertificate.rationalEvaluation 4 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_4_25 :
    constructionMatrixQ 4 25 = RationalCertificate.rationalEvaluation 4 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_4 :
    ∀ c, constructionMatrixQ 4 c = RationalCertificate.rationalEvaluation 4 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_4_25))))))

private theorem constructionMatrixQ_entry_5_0 :
    constructionMatrixQ 5 0 = RationalCertificate.rationalEvaluation 5 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_1 :
    constructionMatrixQ 5 1 = RationalCertificate.rationalEvaluation 5 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_2 :
    constructionMatrixQ 5 2 = RationalCertificate.rationalEvaluation 5 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_3 :
    constructionMatrixQ 5 3 = RationalCertificate.rationalEvaluation 5 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_4 :
    constructionMatrixQ 5 4 = RationalCertificate.rationalEvaluation 5 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_5 :
    constructionMatrixQ 5 5 = RationalCertificate.rationalEvaluation 5 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_6 :
    constructionMatrixQ 5 6 = RationalCertificate.rationalEvaluation 5 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_7 :
    constructionMatrixQ 5 7 = RationalCertificate.rationalEvaluation 5 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_8 :
    constructionMatrixQ 5 8 = RationalCertificate.rationalEvaluation 5 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_9 :
    constructionMatrixQ 5 9 = RationalCertificate.rationalEvaluation 5 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_10 :
    constructionMatrixQ 5 10 = RationalCertificate.rationalEvaluation 5 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_11 :
    constructionMatrixQ 5 11 = RationalCertificate.rationalEvaluation 5 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_12 :
    constructionMatrixQ 5 12 = RationalCertificate.rationalEvaluation 5 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_13 :
    constructionMatrixQ 5 13 = RationalCertificate.rationalEvaluation 5 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_14 :
    constructionMatrixQ 5 14 = RationalCertificate.rationalEvaluation 5 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_15 :
    constructionMatrixQ 5 15 = RationalCertificate.rationalEvaluation 5 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_16 :
    constructionMatrixQ 5 16 = RationalCertificate.rationalEvaluation 5 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_17 :
    constructionMatrixQ 5 17 = RationalCertificate.rationalEvaluation 5 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_18 :
    constructionMatrixQ 5 18 = RationalCertificate.rationalEvaluation 5 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_19 :
    constructionMatrixQ 5 19 = RationalCertificate.rationalEvaluation 5 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_20 :
    constructionMatrixQ 5 20 = RationalCertificate.rationalEvaluation 5 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_21 :
    constructionMatrixQ 5 21 = RationalCertificate.rationalEvaluation 5 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_22 :
    constructionMatrixQ 5 22 = RationalCertificate.rationalEvaluation 5 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_23 :
    constructionMatrixQ 5 23 = RationalCertificate.rationalEvaluation 5 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_24 :
    constructionMatrixQ 5 24 = RationalCertificate.rationalEvaluation 5 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_5_25 :
    constructionMatrixQ 5 25 = RationalCertificate.rationalEvaluation 5 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_5 :
    ∀ c, constructionMatrixQ 5 c = RationalCertificate.rationalEvaluation 5 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_5_25))))))

private theorem constructionMatrixQ_entry_6_0 :
    constructionMatrixQ 6 0 = RationalCertificate.rationalEvaluation 6 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_1 :
    constructionMatrixQ 6 1 = RationalCertificate.rationalEvaluation 6 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_2 :
    constructionMatrixQ 6 2 = RationalCertificate.rationalEvaluation 6 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_3 :
    constructionMatrixQ 6 3 = RationalCertificate.rationalEvaluation 6 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_4 :
    constructionMatrixQ 6 4 = RationalCertificate.rationalEvaluation 6 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_5 :
    constructionMatrixQ 6 5 = RationalCertificate.rationalEvaluation 6 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_6 :
    constructionMatrixQ 6 6 = RationalCertificate.rationalEvaluation 6 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_7 :
    constructionMatrixQ 6 7 = RationalCertificate.rationalEvaluation 6 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_8 :
    constructionMatrixQ 6 8 = RationalCertificate.rationalEvaluation 6 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_9 :
    constructionMatrixQ 6 9 = RationalCertificate.rationalEvaluation 6 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_10 :
    constructionMatrixQ 6 10 = RationalCertificate.rationalEvaluation 6 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_11 :
    constructionMatrixQ 6 11 = RationalCertificate.rationalEvaluation 6 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_12 :
    constructionMatrixQ 6 12 = RationalCertificate.rationalEvaluation 6 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_13 :
    constructionMatrixQ 6 13 = RationalCertificate.rationalEvaluation 6 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_14 :
    constructionMatrixQ 6 14 = RationalCertificate.rationalEvaluation 6 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_15 :
    constructionMatrixQ 6 15 = RationalCertificate.rationalEvaluation 6 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_16 :
    constructionMatrixQ 6 16 = RationalCertificate.rationalEvaluation 6 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_17 :
    constructionMatrixQ 6 17 = RationalCertificate.rationalEvaluation 6 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_18 :
    constructionMatrixQ 6 18 = RationalCertificate.rationalEvaluation 6 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_19 :
    constructionMatrixQ 6 19 = RationalCertificate.rationalEvaluation 6 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_20 :
    constructionMatrixQ 6 20 = RationalCertificate.rationalEvaluation 6 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_21 :
    constructionMatrixQ 6 21 = RationalCertificate.rationalEvaluation 6 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_22 :
    constructionMatrixQ 6 22 = RationalCertificate.rationalEvaluation 6 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_23 :
    constructionMatrixQ 6 23 = RationalCertificate.rationalEvaluation 6 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_24 :
    constructionMatrixQ 6 24 = RationalCertificate.rationalEvaluation 6 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_6_25 :
    constructionMatrixQ 6 25 = RationalCertificate.rationalEvaluation 6 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_6 :
    ∀ c, constructionMatrixQ 6 c = RationalCertificate.rationalEvaluation 6 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_6_25))))))

private theorem constructionMatrixQ_entry_7_0 :
    constructionMatrixQ 7 0 = RationalCertificate.rationalEvaluation 7 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_1 :
    constructionMatrixQ 7 1 = RationalCertificate.rationalEvaluation 7 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_2 :
    constructionMatrixQ 7 2 = RationalCertificate.rationalEvaluation 7 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_3 :
    constructionMatrixQ 7 3 = RationalCertificate.rationalEvaluation 7 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_4 :
    constructionMatrixQ 7 4 = RationalCertificate.rationalEvaluation 7 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_5 :
    constructionMatrixQ 7 5 = RationalCertificate.rationalEvaluation 7 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_6 :
    constructionMatrixQ 7 6 = RationalCertificate.rationalEvaluation 7 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_7 :
    constructionMatrixQ 7 7 = RationalCertificate.rationalEvaluation 7 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_8 :
    constructionMatrixQ 7 8 = RationalCertificate.rationalEvaluation 7 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_9 :
    constructionMatrixQ 7 9 = RationalCertificate.rationalEvaluation 7 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_10 :
    constructionMatrixQ 7 10 = RationalCertificate.rationalEvaluation 7 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_11 :
    constructionMatrixQ 7 11 = RationalCertificate.rationalEvaluation 7 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_12 :
    constructionMatrixQ 7 12 = RationalCertificate.rationalEvaluation 7 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_13 :
    constructionMatrixQ 7 13 = RationalCertificate.rationalEvaluation 7 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_14 :
    constructionMatrixQ 7 14 = RationalCertificate.rationalEvaluation 7 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_15 :
    constructionMatrixQ 7 15 = RationalCertificate.rationalEvaluation 7 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_16 :
    constructionMatrixQ 7 16 = RationalCertificate.rationalEvaluation 7 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_17 :
    constructionMatrixQ 7 17 = RationalCertificate.rationalEvaluation 7 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_18 :
    constructionMatrixQ 7 18 = RationalCertificate.rationalEvaluation 7 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_19 :
    constructionMatrixQ 7 19 = RationalCertificate.rationalEvaluation 7 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_20 :
    constructionMatrixQ 7 20 = RationalCertificate.rationalEvaluation 7 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_21 :
    constructionMatrixQ 7 21 = RationalCertificate.rationalEvaluation 7 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_22 :
    constructionMatrixQ 7 22 = RationalCertificate.rationalEvaluation 7 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_23 :
    constructionMatrixQ 7 23 = RationalCertificate.rationalEvaluation 7 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_24 :
    constructionMatrixQ 7 24 = RationalCertificate.rationalEvaluation 7 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_7_25 :
    constructionMatrixQ 7 25 = RationalCertificate.rationalEvaluation 7 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_7 :
    ∀ c, constructionMatrixQ 7 c = RationalCertificate.rationalEvaluation 7 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_7_25))))))

private theorem constructionMatrixQ_entry_8_0 :
    constructionMatrixQ 8 0 = RationalCertificate.rationalEvaluation 8 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_1 :
    constructionMatrixQ 8 1 = RationalCertificate.rationalEvaluation 8 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_2 :
    constructionMatrixQ 8 2 = RationalCertificate.rationalEvaluation 8 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_3 :
    constructionMatrixQ 8 3 = RationalCertificate.rationalEvaluation 8 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_4 :
    constructionMatrixQ 8 4 = RationalCertificate.rationalEvaluation 8 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_5 :
    constructionMatrixQ 8 5 = RationalCertificate.rationalEvaluation 8 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_6 :
    constructionMatrixQ 8 6 = RationalCertificate.rationalEvaluation 8 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_7 :
    constructionMatrixQ 8 7 = RationalCertificate.rationalEvaluation 8 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_8 :
    constructionMatrixQ 8 8 = RationalCertificate.rationalEvaluation 8 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_9 :
    constructionMatrixQ 8 9 = RationalCertificate.rationalEvaluation 8 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_10 :
    constructionMatrixQ 8 10 = RationalCertificate.rationalEvaluation 8 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_11 :
    constructionMatrixQ 8 11 = RationalCertificate.rationalEvaluation 8 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_12 :
    constructionMatrixQ 8 12 = RationalCertificate.rationalEvaluation 8 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_13 :
    constructionMatrixQ 8 13 = RationalCertificate.rationalEvaluation 8 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_14 :
    constructionMatrixQ 8 14 = RationalCertificate.rationalEvaluation 8 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_15 :
    constructionMatrixQ 8 15 = RationalCertificate.rationalEvaluation 8 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_16 :
    constructionMatrixQ 8 16 = RationalCertificate.rationalEvaluation 8 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_17 :
    constructionMatrixQ 8 17 = RationalCertificate.rationalEvaluation 8 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_18 :
    constructionMatrixQ 8 18 = RationalCertificate.rationalEvaluation 8 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_19 :
    constructionMatrixQ 8 19 = RationalCertificate.rationalEvaluation 8 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_20 :
    constructionMatrixQ 8 20 = RationalCertificate.rationalEvaluation 8 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_21 :
    constructionMatrixQ 8 21 = RationalCertificate.rationalEvaluation 8 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_22 :
    constructionMatrixQ 8 22 = RationalCertificate.rationalEvaluation 8 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_23 :
    constructionMatrixQ 8 23 = RationalCertificate.rationalEvaluation 8 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_24 :
    constructionMatrixQ 8 24 = RationalCertificate.rationalEvaluation 8 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_8_25 :
    constructionMatrixQ 8 25 = RationalCertificate.rationalEvaluation 8 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_8 :
    ∀ c, constructionMatrixQ 8 c = RationalCertificate.rationalEvaluation 8 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_8_25))))))

private theorem constructionMatrixQ_entry_9_0 :
    constructionMatrixQ 9 0 = RationalCertificate.rationalEvaluation 9 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_1 :
    constructionMatrixQ 9 1 = RationalCertificate.rationalEvaluation 9 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_2 :
    constructionMatrixQ 9 2 = RationalCertificate.rationalEvaluation 9 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_3 :
    constructionMatrixQ 9 3 = RationalCertificate.rationalEvaluation 9 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_4 :
    constructionMatrixQ 9 4 = RationalCertificate.rationalEvaluation 9 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_5 :
    constructionMatrixQ 9 5 = RationalCertificate.rationalEvaluation 9 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_6 :
    constructionMatrixQ 9 6 = RationalCertificate.rationalEvaluation 9 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_7 :
    constructionMatrixQ 9 7 = RationalCertificate.rationalEvaluation 9 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_8 :
    constructionMatrixQ 9 8 = RationalCertificate.rationalEvaluation 9 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_9 :
    constructionMatrixQ 9 9 = RationalCertificate.rationalEvaluation 9 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_10 :
    constructionMatrixQ 9 10 = RationalCertificate.rationalEvaluation 9 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_11 :
    constructionMatrixQ 9 11 = RationalCertificate.rationalEvaluation 9 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_12 :
    constructionMatrixQ 9 12 = RationalCertificate.rationalEvaluation 9 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_13 :
    constructionMatrixQ 9 13 = RationalCertificate.rationalEvaluation 9 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_14 :
    constructionMatrixQ 9 14 = RationalCertificate.rationalEvaluation 9 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_15 :
    constructionMatrixQ 9 15 = RationalCertificate.rationalEvaluation 9 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_16 :
    constructionMatrixQ 9 16 = RationalCertificate.rationalEvaluation 9 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_17 :
    constructionMatrixQ 9 17 = RationalCertificate.rationalEvaluation 9 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_18 :
    constructionMatrixQ 9 18 = RationalCertificate.rationalEvaluation 9 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_19 :
    constructionMatrixQ 9 19 = RationalCertificate.rationalEvaluation 9 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_20 :
    constructionMatrixQ 9 20 = RationalCertificate.rationalEvaluation 9 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_21 :
    constructionMatrixQ 9 21 = RationalCertificate.rationalEvaluation 9 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_22 :
    constructionMatrixQ 9 22 = RationalCertificate.rationalEvaluation 9 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_23 :
    constructionMatrixQ 9 23 = RationalCertificate.rationalEvaluation 9 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_24 :
    constructionMatrixQ 9 24 = RationalCertificate.rationalEvaluation 9 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_9_25 :
    constructionMatrixQ 9 25 = RationalCertificate.rationalEvaluation 9 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_9 :
    ∀ c, constructionMatrixQ 9 c = RationalCertificate.rationalEvaluation 9 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_9_25))))))

private theorem constructionMatrixQ_entry_10_0 :
    constructionMatrixQ 10 0 = RationalCertificate.rationalEvaluation 10 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_1 :
    constructionMatrixQ 10 1 = RationalCertificate.rationalEvaluation 10 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_2 :
    constructionMatrixQ 10 2 = RationalCertificate.rationalEvaluation 10 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_3 :
    constructionMatrixQ 10 3 = RationalCertificate.rationalEvaluation 10 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_4 :
    constructionMatrixQ 10 4 = RationalCertificate.rationalEvaluation 10 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_5 :
    constructionMatrixQ 10 5 = RationalCertificate.rationalEvaluation 10 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_6 :
    constructionMatrixQ 10 6 = RationalCertificate.rationalEvaluation 10 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_7 :
    constructionMatrixQ 10 7 = RationalCertificate.rationalEvaluation 10 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_8 :
    constructionMatrixQ 10 8 = RationalCertificate.rationalEvaluation 10 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_9 :
    constructionMatrixQ 10 9 = RationalCertificate.rationalEvaluation 10 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_10 :
    constructionMatrixQ 10 10 = RationalCertificate.rationalEvaluation 10 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_11 :
    constructionMatrixQ 10 11 = RationalCertificate.rationalEvaluation 10 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_12 :
    constructionMatrixQ 10 12 = RationalCertificate.rationalEvaluation 10 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_13 :
    constructionMatrixQ 10 13 = RationalCertificate.rationalEvaluation 10 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_14 :
    constructionMatrixQ 10 14 = RationalCertificate.rationalEvaluation 10 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_15 :
    constructionMatrixQ 10 15 = RationalCertificate.rationalEvaluation 10 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_16 :
    constructionMatrixQ 10 16 = RationalCertificate.rationalEvaluation 10 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_17 :
    constructionMatrixQ 10 17 = RationalCertificate.rationalEvaluation 10 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_18 :
    constructionMatrixQ 10 18 = RationalCertificate.rationalEvaluation 10 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_19 :
    constructionMatrixQ 10 19 = RationalCertificate.rationalEvaluation 10 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_20 :
    constructionMatrixQ 10 20 = RationalCertificate.rationalEvaluation 10 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_21 :
    constructionMatrixQ 10 21 = RationalCertificate.rationalEvaluation 10 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_22 :
    constructionMatrixQ 10 22 = RationalCertificate.rationalEvaluation 10 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_23 :
    constructionMatrixQ 10 23 = RationalCertificate.rationalEvaluation 10 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_24 :
    constructionMatrixQ 10 24 = RationalCertificate.rationalEvaluation 10 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_10_25 :
    constructionMatrixQ 10 25 = RationalCertificate.rationalEvaluation 10 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_10 :
    ∀ c, constructionMatrixQ 10 c = RationalCertificate.rationalEvaluation 10 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_10_25))))))

private theorem constructionMatrixQ_entry_11_0 :
    constructionMatrixQ 11 0 = RationalCertificate.rationalEvaluation 11 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_1 :
    constructionMatrixQ 11 1 = RationalCertificate.rationalEvaluation 11 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_2 :
    constructionMatrixQ 11 2 = RationalCertificate.rationalEvaluation 11 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_3 :
    constructionMatrixQ 11 3 = RationalCertificate.rationalEvaluation 11 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_4 :
    constructionMatrixQ 11 4 = RationalCertificate.rationalEvaluation 11 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_5 :
    constructionMatrixQ 11 5 = RationalCertificate.rationalEvaluation 11 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_6 :
    constructionMatrixQ 11 6 = RationalCertificate.rationalEvaluation 11 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_7 :
    constructionMatrixQ 11 7 = RationalCertificate.rationalEvaluation 11 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_8 :
    constructionMatrixQ 11 8 = RationalCertificate.rationalEvaluation 11 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_9 :
    constructionMatrixQ 11 9 = RationalCertificate.rationalEvaluation 11 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_10 :
    constructionMatrixQ 11 10 = RationalCertificate.rationalEvaluation 11 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_11 :
    constructionMatrixQ 11 11 = RationalCertificate.rationalEvaluation 11 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_12 :
    constructionMatrixQ 11 12 = RationalCertificate.rationalEvaluation 11 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_13 :
    constructionMatrixQ 11 13 = RationalCertificate.rationalEvaluation 11 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_14 :
    constructionMatrixQ 11 14 = RationalCertificate.rationalEvaluation 11 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_15 :
    constructionMatrixQ 11 15 = RationalCertificate.rationalEvaluation 11 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_16 :
    constructionMatrixQ 11 16 = RationalCertificate.rationalEvaluation 11 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_17 :
    constructionMatrixQ 11 17 = RationalCertificate.rationalEvaluation 11 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_18 :
    constructionMatrixQ 11 18 = RationalCertificate.rationalEvaluation 11 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_19 :
    constructionMatrixQ 11 19 = RationalCertificate.rationalEvaluation 11 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_20 :
    constructionMatrixQ 11 20 = RationalCertificate.rationalEvaluation 11 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_21 :
    constructionMatrixQ 11 21 = RationalCertificate.rationalEvaluation 11 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_22 :
    constructionMatrixQ 11 22 = RationalCertificate.rationalEvaluation 11 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_23 :
    constructionMatrixQ 11 23 = RationalCertificate.rationalEvaluation 11 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_24 :
    constructionMatrixQ 11 24 = RationalCertificate.rationalEvaluation 11 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_11_25 :
    constructionMatrixQ 11 25 = RationalCertificate.rationalEvaluation 11 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_11 :
    ∀ c, constructionMatrixQ 11 c = RationalCertificate.rationalEvaluation 11 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_11_25))))))

private theorem constructionMatrixQ_entry_12_0 :
    constructionMatrixQ 12 0 = RationalCertificate.rationalEvaluation 12 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_1 :
    constructionMatrixQ 12 1 = RationalCertificate.rationalEvaluation 12 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_2 :
    constructionMatrixQ 12 2 = RationalCertificate.rationalEvaluation 12 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_3 :
    constructionMatrixQ 12 3 = RationalCertificate.rationalEvaluation 12 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_4 :
    constructionMatrixQ 12 4 = RationalCertificate.rationalEvaluation 12 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_5 :
    constructionMatrixQ 12 5 = RationalCertificate.rationalEvaluation 12 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_6 :
    constructionMatrixQ 12 6 = RationalCertificate.rationalEvaluation 12 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_7 :
    constructionMatrixQ 12 7 = RationalCertificate.rationalEvaluation 12 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_8 :
    constructionMatrixQ 12 8 = RationalCertificate.rationalEvaluation 12 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_9 :
    constructionMatrixQ 12 9 = RationalCertificate.rationalEvaluation 12 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_10 :
    constructionMatrixQ 12 10 = RationalCertificate.rationalEvaluation 12 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_11 :
    constructionMatrixQ 12 11 = RationalCertificate.rationalEvaluation 12 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_12 :
    constructionMatrixQ 12 12 = RationalCertificate.rationalEvaluation 12 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_13 :
    constructionMatrixQ 12 13 = RationalCertificate.rationalEvaluation 12 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_14 :
    constructionMatrixQ 12 14 = RationalCertificate.rationalEvaluation 12 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_15 :
    constructionMatrixQ 12 15 = RationalCertificate.rationalEvaluation 12 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_16 :
    constructionMatrixQ 12 16 = RationalCertificate.rationalEvaluation 12 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_17 :
    constructionMatrixQ 12 17 = RationalCertificate.rationalEvaluation 12 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_18 :
    constructionMatrixQ 12 18 = RationalCertificate.rationalEvaluation 12 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_19 :
    constructionMatrixQ 12 19 = RationalCertificate.rationalEvaluation 12 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_20 :
    constructionMatrixQ 12 20 = RationalCertificate.rationalEvaluation 12 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_21 :
    constructionMatrixQ 12 21 = RationalCertificate.rationalEvaluation 12 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_22 :
    constructionMatrixQ 12 22 = RationalCertificate.rationalEvaluation 12 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_23 :
    constructionMatrixQ 12 23 = RationalCertificate.rationalEvaluation 12 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_24 :
    constructionMatrixQ 12 24 = RationalCertificate.rationalEvaluation 12 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_12_25 :
    constructionMatrixQ 12 25 = RationalCertificate.rationalEvaluation 12 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_12 :
    ∀ c, constructionMatrixQ 12 c = RationalCertificate.rationalEvaluation 12 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_12_25))))))

private theorem constructionMatrixQ_entry_13_0 :
    constructionMatrixQ 13 0 = RationalCertificate.rationalEvaluation 13 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_1 :
    constructionMatrixQ 13 1 = RationalCertificate.rationalEvaluation 13 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_2 :
    constructionMatrixQ 13 2 = RationalCertificate.rationalEvaluation 13 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_3 :
    constructionMatrixQ 13 3 = RationalCertificate.rationalEvaluation 13 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_4 :
    constructionMatrixQ 13 4 = RationalCertificate.rationalEvaluation 13 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_5 :
    constructionMatrixQ 13 5 = RationalCertificate.rationalEvaluation 13 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_6 :
    constructionMatrixQ 13 6 = RationalCertificate.rationalEvaluation 13 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_7 :
    constructionMatrixQ 13 7 = RationalCertificate.rationalEvaluation 13 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_8 :
    constructionMatrixQ 13 8 = RationalCertificate.rationalEvaluation 13 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_9 :
    constructionMatrixQ 13 9 = RationalCertificate.rationalEvaluation 13 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_10 :
    constructionMatrixQ 13 10 = RationalCertificate.rationalEvaluation 13 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_11 :
    constructionMatrixQ 13 11 = RationalCertificate.rationalEvaluation 13 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_12 :
    constructionMatrixQ 13 12 = RationalCertificate.rationalEvaluation 13 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_13 :
    constructionMatrixQ 13 13 = RationalCertificate.rationalEvaluation 13 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_14 :
    constructionMatrixQ 13 14 = RationalCertificate.rationalEvaluation 13 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_15 :
    constructionMatrixQ 13 15 = RationalCertificate.rationalEvaluation 13 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_16 :
    constructionMatrixQ 13 16 = RationalCertificate.rationalEvaluation 13 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_17 :
    constructionMatrixQ 13 17 = RationalCertificate.rationalEvaluation 13 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_18 :
    constructionMatrixQ 13 18 = RationalCertificate.rationalEvaluation 13 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_19 :
    constructionMatrixQ 13 19 = RationalCertificate.rationalEvaluation 13 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_20 :
    constructionMatrixQ 13 20 = RationalCertificate.rationalEvaluation 13 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_21 :
    constructionMatrixQ 13 21 = RationalCertificate.rationalEvaluation 13 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_22 :
    constructionMatrixQ 13 22 = RationalCertificate.rationalEvaluation 13 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_23 :
    constructionMatrixQ 13 23 = RationalCertificate.rationalEvaluation 13 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_24 :
    constructionMatrixQ 13 24 = RationalCertificate.rationalEvaluation 13 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_13_25 :
    constructionMatrixQ 13 25 = RationalCertificate.rationalEvaluation 13 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_13 :
    ∀ c, constructionMatrixQ 13 c = RationalCertificate.rationalEvaluation 13 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_13_25))))))

private theorem constructionMatrixQ_entry_14_0 :
    constructionMatrixQ 14 0 = RationalCertificate.rationalEvaluation 14 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_1 :
    constructionMatrixQ 14 1 = RationalCertificate.rationalEvaluation 14 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_2 :
    constructionMatrixQ 14 2 = RationalCertificate.rationalEvaluation 14 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_3 :
    constructionMatrixQ 14 3 = RationalCertificate.rationalEvaluation 14 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_4 :
    constructionMatrixQ 14 4 = RationalCertificate.rationalEvaluation 14 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_5 :
    constructionMatrixQ 14 5 = RationalCertificate.rationalEvaluation 14 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_6 :
    constructionMatrixQ 14 6 = RationalCertificate.rationalEvaluation 14 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_7 :
    constructionMatrixQ 14 7 = RationalCertificate.rationalEvaluation 14 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_8 :
    constructionMatrixQ 14 8 = RationalCertificate.rationalEvaluation 14 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_9 :
    constructionMatrixQ 14 9 = RationalCertificate.rationalEvaluation 14 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_10 :
    constructionMatrixQ 14 10 = RationalCertificate.rationalEvaluation 14 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_11 :
    constructionMatrixQ 14 11 = RationalCertificate.rationalEvaluation 14 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_12 :
    constructionMatrixQ 14 12 = RationalCertificate.rationalEvaluation 14 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_13 :
    constructionMatrixQ 14 13 = RationalCertificate.rationalEvaluation 14 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_14 :
    constructionMatrixQ 14 14 = RationalCertificate.rationalEvaluation 14 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_15 :
    constructionMatrixQ 14 15 = RationalCertificate.rationalEvaluation 14 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_16 :
    constructionMatrixQ 14 16 = RationalCertificate.rationalEvaluation 14 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_17 :
    constructionMatrixQ 14 17 = RationalCertificate.rationalEvaluation 14 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_18 :
    constructionMatrixQ 14 18 = RationalCertificate.rationalEvaluation 14 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_19 :
    constructionMatrixQ 14 19 = RationalCertificate.rationalEvaluation 14 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_20 :
    constructionMatrixQ 14 20 = RationalCertificate.rationalEvaluation 14 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_21 :
    constructionMatrixQ 14 21 = RationalCertificate.rationalEvaluation 14 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_22 :
    constructionMatrixQ 14 22 = RationalCertificate.rationalEvaluation 14 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_23 :
    constructionMatrixQ 14 23 = RationalCertificate.rationalEvaluation 14 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_24 :
    constructionMatrixQ 14 24 = RationalCertificate.rationalEvaluation 14 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_14_25 :
    constructionMatrixQ 14 25 = RationalCertificate.rationalEvaluation 14 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_14 :
    ∀ c, constructionMatrixQ 14 c = RationalCertificate.rationalEvaluation 14 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_14_25))))))

private theorem constructionMatrixQ_entry_15_0 :
    constructionMatrixQ 15 0 = RationalCertificate.rationalEvaluation 15 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_1 :
    constructionMatrixQ 15 1 = RationalCertificate.rationalEvaluation 15 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_2 :
    constructionMatrixQ 15 2 = RationalCertificate.rationalEvaluation 15 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_3 :
    constructionMatrixQ 15 3 = RationalCertificate.rationalEvaluation 15 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_4 :
    constructionMatrixQ 15 4 = RationalCertificate.rationalEvaluation 15 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_5 :
    constructionMatrixQ 15 5 = RationalCertificate.rationalEvaluation 15 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_6 :
    constructionMatrixQ 15 6 = RationalCertificate.rationalEvaluation 15 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_7 :
    constructionMatrixQ 15 7 = RationalCertificate.rationalEvaluation 15 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_8 :
    constructionMatrixQ 15 8 = RationalCertificate.rationalEvaluation 15 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_9 :
    constructionMatrixQ 15 9 = RationalCertificate.rationalEvaluation 15 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_10 :
    constructionMatrixQ 15 10 = RationalCertificate.rationalEvaluation 15 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_11 :
    constructionMatrixQ 15 11 = RationalCertificate.rationalEvaluation 15 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_12 :
    constructionMatrixQ 15 12 = RationalCertificate.rationalEvaluation 15 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_13 :
    constructionMatrixQ 15 13 = RationalCertificate.rationalEvaluation 15 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_14 :
    constructionMatrixQ 15 14 = RationalCertificate.rationalEvaluation 15 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_15 :
    constructionMatrixQ 15 15 = RationalCertificate.rationalEvaluation 15 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_16 :
    constructionMatrixQ 15 16 = RationalCertificate.rationalEvaluation 15 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_17 :
    constructionMatrixQ 15 17 = RationalCertificate.rationalEvaluation 15 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_18 :
    constructionMatrixQ 15 18 = RationalCertificate.rationalEvaluation 15 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_19 :
    constructionMatrixQ 15 19 = RationalCertificate.rationalEvaluation 15 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_20 :
    constructionMatrixQ 15 20 = RationalCertificate.rationalEvaluation 15 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_21 :
    constructionMatrixQ 15 21 = RationalCertificate.rationalEvaluation 15 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_22 :
    constructionMatrixQ 15 22 = RationalCertificate.rationalEvaluation 15 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_23 :
    constructionMatrixQ 15 23 = RationalCertificate.rationalEvaluation 15 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_24 :
    constructionMatrixQ 15 24 = RationalCertificate.rationalEvaluation 15 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_15_25 :
    constructionMatrixQ 15 25 = RationalCertificate.rationalEvaluation 15 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_15 :
    ∀ c, constructionMatrixQ 15 c = RationalCertificate.rationalEvaluation 15 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_15_25))))))

private theorem constructionMatrixQ_entry_16_0 :
    constructionMatrixQ 16 0 = RationalCertificate.rationalEvaluation 16 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_1 :
    constructionMatrixQ 16 1 = RationalCertificate.rationalEvaluation 16 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_2 :
    constructionMatrixQ 16 2 = RationalCertificate.rationalEvaluation 16 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_3 :
    constructionMatrixQ 16 3 = RationalCertificate.rationalEvaluation 16 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_4 :
    constructionMatrixQ 16 4 = RationalCertificate.rationalEvaluation 16 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_5 :
    constructionMatrixQ 16 5 = RationalCertificate.rationalEvaluation 16 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_6 :
    constructionMatrixQ 16 6 = RationalCertificate.rationalEvaluation 16 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_7 :
    constructionMatrixQ 16 7 = RationalCertificate.rationalEvaluation 16 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_8 :
    constructionMatrixQ 16 8 = RationalCertificate.rationalEvaluation 16 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_9 :
    constructionMatrixQ 16 9 = RationalCertificate.rationalEvaluation 16 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_10 :
    constructionMatrixQ 16 10 = RationalCertificate.rationalEvaluation 16 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_11 :
    constructionMatrixQ 16 11 = RationalCertificate.rationalEvaluation 16 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_12 :
    constructionMatrixQ 16 12 = RationalCertificate.rationalEvaluation 16 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_13 :
    constructionMatrixQ 16 13 = RationalCertificate.rationalEvaluation 16 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_14 :
    constructionMatrixQ 16 14 = RationalCertificate.rationalEvaluation 16 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_15 :
    constructionMatrixQ 16 15 = RationalCertificate.rationalEvaluation 16 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_16 :
    constructionMatrixQ 16 16 = RationalCertificate.rationalEvaluation 16 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_17 :
    constructionMatrixQ 16 17 = RationalCertificate.rationalEvaluation 16 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_18 :
    constructionMatrixQ 16 18 = RationalCertificate.rationalEvaluation 16 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_19 :
    constructionMatrixQ 16 19 = RationalCertificate.rationalEvaluation 16 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_20 :
    constructionMatrixQ 16 20 = RationalCertificate.rationalEvaluation 16 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_21 :
    constructionMatrixQ 16 21 = RationalCertificate.rationalEvaluation 16 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_22 :
    constructionMatrixQ 16 22 = RationalCertificate.rationalEvaluation 16 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_23 :
    constructionMatrixQ 16 23 = RationalCertificate.rationalEvaluation 16 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_24 :
    constructionMatrixQ 16 24 = RationalCertificate.rationalEvaluation 16 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_16_25 :
    constructionMatrixQ 16 25 = RationalCertificate.rationalEvaluation 16 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_16 :
    ∀ c, constructionMatrixQ 16 c = RationalCertificate.rationalEvaluation 16 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_16_25))))))

private theorem constructionMatrixQ_entry_17_0 :
    constructionMatrixQ 17 0 = RationalCertificate.rationalEvaluation 17 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_1 :
    constructionMatrixQ 17 1 = RationalCertificate.rationalEvaluation 17 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_2 :
    constructionMatrixQ 17 2 = RationalCertificate.rationalEvaluation 17 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_3 :
    constructionMatrixQ 17 3 = RationalCertificate.rationalEvaluation 17 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_4 :
    constructionMatrixQ 17 4 = RationalCertificate.rationalEvaluation 17 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_5 :
    constructionMatrixQ 17 5 = RationalCertificate.rationalEvaluation 17 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_6 :
    constructionMatrixQ 17 6 = RationalCertificate.rationalEvaluation 17 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_7 :
    constructionMatrixQ 17 7 = RationalCertificate.rationalEvaluation 17 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_8 :
    constructionMatrixQ 17 8 = RationalCertificate.rationalEvaluation 17 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_9 :
    constructionMatrixQ 17 9 = RationalCertificate.rationalEvaluation 17 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_10 :
    constructionMatrixQ 17 10 = RationalCertificate.rationalEvaluation 17 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_11 :
    constructionMatrixQ 17 11 = RationalCertificate.rationalEvaluation 17 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_12 :
    constructionMatrixQ 17 12 = RationalCertificate.rationalEvaluation 17 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_13 :
    constructionMatrixQ 17 13 = RationalCertificate.rationalEvaluation 17 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_14 :
    constructionMatrixQ 17 14 = RationalCertificate.rationalEvaluation 17 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_15 :
    constructionMatrixQ 17 15 = RationalCertificate.rationalEvaluation 17 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_16 :
    constructionMatrixQ 17 16 = RationalCertificate.rationalEvaluation 17 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_17 :
    constructionMatrixQ 17 17 = RationalCertificate.rationalEvaluation 17 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_18 :
    constructionMatrixQ 17 18 = RationalCertificate.rationalEvaluation 17 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_19 :
    constructionMatrixQ 17 19 = RationalCertificate.rationalEvaluation 17 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_20 :
    constructionMatrixQ 17 20 = RationalCertificate.rationalEvaluation 17 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_21 :
    constructionMatrixQ 17 21 = RationalCertificate.rationalEvaluation 17 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_22 :
    constructionMatrixQ 17 22 = RationalCertificate.rationalEvaluation 17 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_23 :
    constructionMatrixQ 17 23 = RationalCertificate.rationalEvaluation 17 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_24 :
    constructionMatrixQ 17 24 = RationalCertificate.rationalEvaluation 17 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_17_25 :
    constructionMatrixQ 17 25 = RationalCertificate.rationalEvaluation 17 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_17 :
    ∀ c, constructionMatrixQ 17 c = RationalCertificate.rationalEvaluation 17 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_17_25))))))

private theorem constructionMatrixQ_entry_18_0 :
    constructionMatrixQ 18 0 = RationalCertificate.rationalEvaluation 18 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_1 :
    constructionMatrixQ 18 1 = RationalCertificate.rationalEvaluation 18 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_2 :
    constructionMatrixQ 18 2 = RationalCertificate.rationalEvaluation 18 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_3 :
    constructionMatrixQ 18 3 = RationalCertificate.rationalEvaluation 18 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_4 :
    constructionMatrixQ 18 4 = RationalCertificate.rationalEvaluation 18 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_5 :
    constructionMatrixQ 18 5 = RationalCertificate.rationalEvaluation 18 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_6 :
    constructionMatrixQ 18 6 = RationalCertificate.rationalEvaluation 18 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_7 :
    constructionMatrixQ 18 7 = RationalCertificate.rationalEvaluation 18 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_8 :
    constructionMatrixQ 18 8 = RationalCertificate.rationalEvaluation 18 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_9 :
    constructionMatrixQ 18 9 = RationalCertificate.rationalEvaluation 18 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_10 :
    constructionMatrixQ 18 10 = RationalCertificate.rationalEvaluation 18 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_11 :
    constructionMatrixQ 18 11 = RationalCertificate.rationalEvaluation 18 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_12 :
    constructionMatrixQ 18 12 = RationalCertificate.rationalEvaluation 18 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_13 :
    constructionMatrixQ 18 13 = RationalCertificate.rationalEvaluation 18 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_14 :
    constructionMatrixQ 18 14 = RationalCertificate.rationalEvaluation 18 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_15 :
    constructionMatrixQ 18 15 = RationalCertificate.rationalEvaluation 18 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_16 :
    constructionMatrixQ 18 16 = RationalCertificate.rationalEvaluation 18 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_17 :
    constructionMatrixQ 18 17 = RationalCertificate.rationalEvaluation 18 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_18 :
    constructionMatrixQ 18 18 = RationalCertificate.rationalEvaluation 18 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_19 :
    constructionMatrixQ 18 19 = RationalCertificate.rationalEvaluation 18 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_20 :
    constructionMatrixQ 18 20 = RationalCertificate.rationalEvaluation 18 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_21 :
    constructionMatrixQ 18 21 = RationalCertificate.rationalEvaluation 18 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_22 :
    constructionMatrixQ 18 22 = RationalCertificate.rationalEvaluation 18 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_23 :
    constructionMatrixQ 18 23 = RationalCertificate.rationalEvaluation 18 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_24 :
    constructionMatrixQ 18 24 = RationalCertificate.rationalEvaluation 18 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_18_25 :
    constructionMatrixQ 18 25 = RationalCertificate.rationalEvaluation 18 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_18 :
    ∀ c, constructionMatrixQ 18 c = RationalCertificate.rationalEvaluation 18 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_18_25))))))

private theorem constructionMatrixQ_entry_19_0 :
    constructionMatrixQ 19 0 = RationalCertificate.rationalEvaluation 19 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_1 :
    constructionMatrixQ 19 1 = RationalCertificate.rationalEvaluation 19 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_2 :
    constructionMatrixQ 19 2 = RationalCertificate.rationalEvaluation 19 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_3 :
    constructionMatrixQ 19 3 = RationalCertificate.rationalEvaluation 19 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_4 :
    constructionMatrixQ 19 4 = RationalCertificate.rationalEvaluation 19 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_5 :
    constructionMatrixQ 19 5 = RationalCertificate.rationalEvaluation 19 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_6 :
    constructionMatrixQ 19 6 = RationalCertificate.rationalEvaluation 19 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_7 :
    constructionMatrixQ 19 7 = RationalCertificate.rationalEvaluation 19 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_8 :
    constructionMatrixQ 19 8 = RationalCertificate.rationalEvaluation 19 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_9 :
    constructionMatrixQ 19 9 = RationalCertificate.rationalEvaluation 19 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_10 :
    constructionMatrixQ 19 10 = RationalCertificate.rationalEvaluation 19 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_11 :
    constructionMatrixQ 19 11 = RationalCertificate.rationalEvaluation 19 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_12 :
    constructionMatrixQ 19 12 = RationalCertificate.rationalEvaluation 19 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_13 :
    constructionMatrixQ 19 13 = RationalCertificate.rationalEvaluation 19 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_14 :
    constructionMatrixQ 19 14 = RationalCertificate.rationalEvaluation 19 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_15 :
    constructionMatrixQ 19 15 = RationalCertificate.rationalEvaluation 19 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_16 :
    constructionMatrixQ 19 16 = RationalCertificate.rationalEvaluation 19 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_17 :
    constructionMatrixQ 19 17 = RationalCertificate.rationalEvaluation 19 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_18 :
    constructionMatrixQ 19 18 = RationalCertificate.rationalEvaluation 19 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_19 :
    constructionMatrixQ 19 19 = RationalCertificate.rationalEvaluation 19 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_20 :
    constructionMatrixQ 19 20 = RationalCertificate.rationalEvaluation 19 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_21 :
    constructionMatrixQ 19 21 = RationalCertificate.rationalEvaluation 19 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_22 :
    constructionMatrixQ 19 22 = RationalCertificate.rationalEvaluation 19 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_23 :
    constructionMatrixQ 19 23 = RationalCertificate.rationalEvaluation 19 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_24 :
    constructionMatrixQ 19 24 = RationalCertificate.rationalEvaluation 19 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_19_25 :
    constructionMatrixQ 19 25 = RationalCertificate.rationalEvaluation 19 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_19 :
    ∀ c, constructionMatrixQ 19 c = RationalCertificate.rationalEvaluation 19 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_19_25))))))

private theorem constructionMatrixQ_entry_20_0 :
    constructionMatrixQ 20 0 = RationalCertificate.rationalEvaluation 20 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_1 :
    constructionMatrixQ 20 1 = RationalCertificate.rationalEvaluation 20 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_2 :
    constructionMatrixQ 20 2 = RationalCertificate.rationalEvaluation 20 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_3 :
    constructionMatrixQ 20 3 = RationalCertificate.rationalEvaluation 20 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_4 :
    constructionMatrixQ 20 4 = RationalCertificate.rationalEvaluation 20 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_5 :
    constructionMatrixQ 20 5 = RationalCertificate.rationalEvaluation 20 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_6 :
    constructionMatrixQ 20 6 = RationalCertificate.rationalEvaluation 20 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_7 :
    constructionMatrixQ 20 7 = RationalCertificate.rationalEvaluation 20 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_8 :
    constructionMatrixQ 20 8 = RationalCertificate.rationalEvaluation 20 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_9 :
    constructionMatrixQ 20 9 = RationalCertificate.rationalEvaluation 20 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_10 :
    constructionMatrixQ 20 10 = RationalCertificate.rationalEvaluation 20 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_11 :
    constructionMatrixQ 20 11 = RationalCertificate.rationalEvaluation 20 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_12 :
    constructionMatrixQ 20 12 = RationalCertificate.rationalEvaluation 20 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_13 :
    constructionMatrixQ 20 13 = RationalCertificate.rationalEvaluation 20 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_14 :
    constructionMatrixQ 20 14 = RationalCertificate.rationalEvaluation 20 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_15 :
    constructionMatrixQ 20 15 = RationalCertificate.rationalEvaluation 20 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_16 :
    constructionMatrixQ 20 16 = RationalCertificate.rationalEvaluation 20 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_17 :
    constructionMatrixQ 20 17 = RationalCertificate.rationalEvaluation 20 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_18 :
    constructionMatrixQ 20 18 = RationalCertificate.rationalEvaluation 20 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_19 :
    constructionMatrixQ 20 19 = RationalCertificate.rationalEvaluation 20 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_20 :
    constructionMatrixQ 20 20 = RationalCertificate.rationalEvaluation 20 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_21 :
    constructionMatrixQ 20 21 = RationalCertificate.rationalEvaluation 20 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_22 :
    constructionMatrixQ 20 22 = RationalCertificate.rationalEvaluation 20 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_23 :
    constructionMatrixQ 20 23 = RationalCertificate.rationalEvaluation 20 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_24 :
    constructionMatrixQ 20 24 = RationalCertificate.rationalEvaluation 20 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_20_25 :
    constructionMatrixQ 20 25 = RationalCertificate.rationalEvaluation 20 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_20 :
    ∀ c, constructionMatrixQ 20 c = RationalCertificate.rationalEvaluation 20 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_20_25))))))

private theorem constructionMatrixQ_entry_21_0 :
    constructionMatrixQ 21 0 = RationalCertificate.rationalEvaluation 21 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_1 :
    constructionMatrixQ 21 1 = RationalCertificate.rationalEvaluation 21 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_2 :
    constructionMatrixQ 21 2 = RationalCertificate.rationalEvaluation 21 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_3 :
    constructionMatrixQ 21 3 = RationalCertificate.rationalEvaluation 21 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_4 :
    constructionMatrixQ 21 4 = RationalCertificate.rationalEvaluation 21 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_5 :
    constructionMatrixQ 21 5 = RationalCertificate.rationalEvaluation 21 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_6 :
    constructionMatrixQ 21 6 = RationalCertificate.rationalEvaluation 21 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_7 :
    constructionMatrixQ 21 7 = RationalCertificate.rationalEvaluation 21 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_8 :
    constructionMatrixQ 21 8 = RationalCertificate.rationalEvaluation 21 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_9 :
    constructionMatrixQ 21 9 = RationalCertificate.rationalEvaluation 21 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_10 :
    constructionMatrixQ 21 10 = RationalCertificate.rationalEvaluation 21 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_11 :
    constructionMatrixQ 21 11 = RationalCertificate.rationalEvaluation 21 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_12 :
    constructionMatrixQ 21 12 = RationalCertificate.rationalEvaluation 21 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_13 :
    constructionMatrixQ 21 13 = RationalCertificate.rationalEvaluation 21 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_14 :
    constructionMatrixQ 21 14 = RationalCertificate.rationalEvaluation 21 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_15 :
    constructionMatrixQ 21 15 = RationalCertificate.rationalEvaluation 21 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_16 :
    constructionMatrixQ 21 16 = RationalCertificate.rationalEvaluation 21 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_17 :
    constructionMatrixQ 21 17 = RationalCertificate.rationalEvaluation 21 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_18 :
    constructionMatrixQ 21 18 = RationalCertificate.rationalEvaluation 21 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_19 :
    constructionMatrixQ 21 19 = RationalCertificate.rationalEvaluation 21 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_20 :
    constructionMatrixQ 21 20 = RationalCertificate.rationalEvaluation 21 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_21 :
    constructionMatrixQ 21 21 = RationalCertificate.rationalEvaluation 21 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_22 :
    constructionMatrixQ 21 22 = RationalCertificate.rationalEvaluation 21 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_23 :
    constructionMatrixQ 21 23 = RationalCertificate.rationalEvaluation 21 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_24 :
    constructionMatrixQ 21 24 = RationalCertificate.rationalEvaluation 21 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_21_25 :
    constructionMatrixQ 21 25 = RationalCertificate.rationalEvaluation 21 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_21 :
    ∀ c, constructionMatrixQ 21 c = RationalCertificate.rationalEvaluation 21 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_21_25))))))

private theorem constructionMatrixQ_entry_22_0 :
    constructionMatrixQ 22 0 = RationalCertificate.rationalEvaluation 22 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_1 :
    constructionMatrixQ 22 1 = RationalCertificate.rationalEvaluation 22 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_2 :
    constructionMatrixQ 22 2 = RationalCertificate.rationalEvaluation 22 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_3 :
    constructionMatrixQ 22 3 = RationalCertificate.rationalEvaluation 22 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_4 :
    constructionMatrixQ 22 4 = RationalCertificate.rationalEvaluation 22 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_5 :
    constructionMatrixQ 22 5 = RationalCertificate.rationalEvaluation 22 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_6 :
    constructionMatrixQ 22 6 = RationalCertificate.rationalEvaluation 22 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_7 :
    constructionMatrixQ 22 7 = RationalCertificate.rationalEvaluation 22 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_8 :
    constructionMatrixQ 22 8 = RationalCertificate.rationalEvaluation 22 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_9 :
    constructionMatrixQ 22 9 = RationalCertificate.rationalEvaluation 22 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_10 :
    constructionMatrixQ 22 10 = RationalCertificate.rationalEvaluation 22 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_11 :
    constructionMatrixQ 22 11 = RationalCertificate.rationalEvaluation 22 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_12 :
    constructionMatrixQ 22 12 = RationalCertificate.rationalEvaluation 22 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_13 :
    constructionMatrixQ 22 13 = RationalCertificate.rationalEvaluation 22 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_14 :
    constructionMatrixQ 22 14 = RationalCertificate.rationalEvaluation 22 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_15 :
    constructionMatrixQ 22 15 = RationalCertificate.rationalEvaluation 22 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_16 :
    constructionMatrixQ 22 16 = RationalCertificate.rationalEvaluation 22 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_17 :
    constructionMatrixQ 22 17 = RationalCertificate.rationalEvaluation 22 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_18 :
    constructionMatrixQ 22 18 = RationalCertificate.rationalEvaluation 22 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_19 :
    constructionMatrixQ 22 19 = RationalCertificate.rationalEvaluation 22 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_20 :
    constructionMatrixQ 22 20 = RationalCertificate.rationalEvaluation 22 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_21 :
    constructionMatrixQ 22 21 = RationalCertificate.rationalEvaluation 22 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_22 :
    constructionMatrixQ 22 22 = RationalCertificate.rationalEvaluation 22 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_23 :
    constructionMatrixQ 22 23 = RationalCertificate.rationalEvaluation 22 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_24 :
    constructionMatrixQ 22 24 = RationalCertificate.rationalEvaluation 22 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_22_25 :
    constructionMatrixQ 22 25 = RationalCertificate.rationalEvaluation 22 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_22 :
    ∀ c, constructionMatrixQ 22 c = RationalCertificate.rationalEvaluation 22 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_22_25))))))

private theorem constructionMatrixQ_entry_23_0 :
    constructionMatrixQ 23 0 = RationalCertificate.rationalEvaluation 23 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_1 :
    constructionMatrixQ 23 1 = RationalCertificate.rationalEvaluation 23 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_2 :
    constructionMatrixQ 23 2 = RationalCertificate.rationalEvaluation 23 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_3 :
    constructionMatrixQ 23 3 = RationalCertificate.rationalEvaluation 23 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_4 :
    constructionMatrixQ 23 4 = RationalCertificate.rationalEvaluation 23 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_5 :
    constructionMatrixQ 23 5 = RationalCertificate.rationalEvaluation 23 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_6 :
    constructionMatrixQ 23 6 = RationalCertificate.rationalEvaluation 23 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_7 :
    constructionMatrixQ 23 7 = RationalCertificate.rationalEvaluation 23 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_8 :
    constructionMatrixQ 23 8 = RationalCertificate.rationalEvaluation 23 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_9 :
    constructionMatrixQ 23 9 = RationalCertificate.rationalEvaluation 23 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_10 :
    constructionMatrixQ 23 10 = RationalCertificate.rationalEvaluation 23 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_11 :
    constructionMatrixQ 23 11 = RationalCertificate.rationalEvaluation 23 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_12 :
    constructionMatrixQ 23 12 = RationalCertificate.rationalEvaluation 23 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_13 :
    constructionMatrixQ 23 13 = RationalCertificate.rationalEvaluation 23 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_14 :
    constructionMatrixQ 23 14 = RationalCertificate.rationalEvaluation 23 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_15 :
    constructionMatrixQ 23 15 = RationalCertificate.rationalEvaluation 23 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_16 :
    constructionMatrixQ 23 16 = RationalCertificate.rationalEvaluation 23 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_17 :
    constructionMatrixQ 23 17 = RationalCertificate.rationalEvaluation 23 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_18 :
    constructionMatrixQ 23 18 = RationalCertificate.rationalEvaluation 23 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_19 :
    constructionMatrixQ 23 19 = RationalCertificate.rationalEvaluation 23 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_20 :
    constructionMatrixQ 23 20 = RationalCertificate.rationalEvaluation 23 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_21 :
    constructionMatrixQ 23 21 = RationalCertificate.rationalEvaluation 23 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_22 :
    constructionMatrixQ 23 22 = RationalCertificate.rationalEvaluation 23 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_23 :
    constructionMatrixQ 23 23 = RationalCertificate.rationalEvaluation 23 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_24 :
    constructionMatrixQ 23 24 = RationalCertificate.rationalEvaluation 23 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_23_25 :
    constructionMatrixQ 23 25 = RationalCertificate.rationalEvaluation 23 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_23 :
    ∀ c, constructionMatrixQ 23 c = RationalCertificate.rationalEvaluation 23 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_23_25))))))

private theorem constructionMatrixQ_entry_24_0 :
    constructionMatrixQ 24 0 = RationalCertificate.rationalEvaluation 24 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_1 :
    constructionMatrixQ 24 1 = RationalCertificate.rationalEvaluation 24 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_2 :
    constructionMatrixQ 24 2 = RationalCertificate.rationalEvaluation 24 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_3 :
    constructionMatrixQ 24 3 = RationalCertificate.rationalEvaluation 24 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_4 :
    constructionMatrixQ 24 4 = RationalCertificate.rationalEvaluation 24 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_5 :
    constructionMatrixQ 24 5 = RationalCertificate.rationalEvaluation 24 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_6 :
    constructionMatrixQ 24 6 = RationalCertificate.rationalEvaluation 24 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_7 :
    constructionMatrixQ 24 7 = RationalCertificate.rationalEvaluation 24 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_8 :
    constructionMatrixQ 24 8 = RationalCertificate.rationalEvaluation 24 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_9 :
    constructionMatrixQ 24 9 = RationalCertificate.rationalEvaluation 24 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_10 :
    constructionMatrixQ 24 10 = RationalCertificate.rationalEvaluation 24 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_11 :
    constructionMatrixQ 24 11 = RationalCertificate.rationalEvaluation 24 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_12 :
    constructionMatrixQ 24 12 = RationalCertificate.rationalEvaluation 24 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_13 :
    constructionMatrixQ 24 13 = RationalCertificate.rationalEvaluation 24 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_14 :
    constructionMatrixQ 24 14 = RationalCertificate.rationalEvaluation 24 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_15 :
    constructionMatrixQ 24 15 = RationalCertificate.rationalEvaluation 24 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_16 :
    constructionMatrixQ 24 16 = RationalCertificate.rationalEvaluation 24 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_17 :
    constructionMatrixQ 24 17 = RationalCertificate.rationalEvaluation 24 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_18 :
    constructionMatrixQ 24 18 = RationalCertificate.rationalEvaluation 24 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_19 :
    constructionMatrixQ 24 19 = RationalCertificate.rationalEvaluation 24 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_20 :
    constructionMatrixQ 24 20 = RationalCertificate.rationalEvaluation 24 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_21 :
    constructionMatrixQ 24 21 = RationalCertificate.rationalEvaluation 24 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_22 :
    constructionMatrixQ 24 22 = RationalCertificate.rationalEvaluation 24 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_23 :
    constructionMatrixQ 24 23 = RationalCertificate.rationalEvaluation 24 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_24 :
    constructionMatrixQ 24 24 = RationalCertificate.rationalEvaluation 24 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_24_25 :
    constructionMatrixQ 24 25 = RationalCertificate.rationalEvaluation 24 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_24 :
    ∀ c, constructionMatrixQ 24 c = RationalCertificate.rationalEvaluation 24 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_24_25))))))

private theorem constructionMatrixQ_entry_25_0 :
    constructionMatrixQ 25 0 = RationalCertificate.rationalEvaluation 25 0 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_1 :
    constructionMatrixQ 25 1 = RationalCertificate.rationalEvaluation 25 1 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_2 :
    constructionMatrixQ 25 2 = RationalCertificate.rationalEvaluation 25 2 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_3 :
    constructionMatrixQ 25 3 = RationalCertificate.rationalEvaluation 25 3 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_4 :
    constructionMatrixQ 25 4 = RationalCertificate.rationalEvaluation 25 4 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_5 :
    constructionMatrixQ 25 5 = RationalCertificate.rationalEvaluation 25 5 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_6 :
    constructionMatrixQ 25 6 = RationalCertificate.rationalEvaluation 25 6 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_7 :
    constructionMatrixQ 25 7 = RationalCertificate.rationalEvaluation 25 7 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_8 :
    constructionMatrixQ 25 8 = RationalCertificate.rationalEvaluation 25 8 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_9 :
    constructionMatrixQ 25 9 = RationalCertificate.rationalEvaluation 25 9 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_10 :
    constructionMatrixQ 25 10 = RationalCertificate.rationalEvaluation 25 10 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_11 :
    constructionMatrixQ 25 11 = RationalCertificate.rationalEvaluation 25 11 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_12 :
    constructionMatrixQ 25 12 = RationalCertificate.rationalEvaluation 25 12 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_13 :
    constructionMatrixQ 25 13 = RationalCertificate.rationalEvaluation 25 13 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_14 :
    constructionMatrixQ 25 14 = RationalCertificate.rationalEvaluation 25 14 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_15 :
    constructionMatrixQ 25 15 = RationalCertificate.rationalEvaluation 25 15 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_16 :
    constructionMatrixQ 25 16 = RationalCertificate.rationalEvaluation 25 16 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_17 :
    constructionMatrixQ 25 17 = RationalCertificate.rationalEvaluation 25 17 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_18 :
    constructionMatrixQ 25 18 = RationalCertificate.rationalEvaluation 25 18 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_19 :
    constructionMatrixQ 25 19 = RationalCertificate.rationalEvaluation 25 19 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_20 :
    constructionMatrixQ 25 20 = RationalCertificate.rationalEvaluation 25 20 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_21 :
    constructionMatrixQ 25 21 = RationalCertificate.rationalEvaluation 25 21 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_22 :
    constructionMatrixQ 25 22 = RationalCertificate.rationalEvaluation 25 22 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_23 :
    constructionMatrixQ 25 23 = RationalCertificate.rationalEvaluation 25 23 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_24 :
    constructionMatrixQ 25 24 = RationalCertificate.rationalEvaluation 25 24 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_entry_25_25 :
    constructionMatrixQ 25 25 = RationalCertificate.rationalEvaluation 25 25 := by
  check_rational_matrix_entry

private theorem constructionMatrixQ_row_25 :
    ∀ c, constructionMatrixQ 25 c = RationalCertificate.rationalEvaluation 25 c :=
  (CertifiedRank.forall_fin_add (a := 13) (b := 13)
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_0)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_2)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_3)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_4)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_5))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_6)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_7)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_8)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_9)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_10))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_11)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_12)))))
    (CertifiedRank.forall_fin_add (a := 6) (b := 7)
      (CertifiedRank.forall_fin_add (a := 3) (b := 3)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_13)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_14)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_15)))
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_16)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_17)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_18))))
      (CertifiedRank.forall_fin_add (a := 3) (b := 4)
        (CertifiedRank.forall_fin_add (a := 1) (b := 2)
          (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_19)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_20)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_21)))
        (CertifiedRank.forall_fin_add (a := 2) (b := 2)
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_22)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_23))
          (CertifiedRank.forall_fin_add (a := 1) (b := 1)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_24)
            (CertifiedRank.forall_fin_one constructionMatrixQ_entry_25_25))))))

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
