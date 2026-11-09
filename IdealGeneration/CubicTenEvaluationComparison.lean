module

public import IdealGeneration.CubicTenGeometry
public import IdealGeneration.CubicTenNormalKernelCertificate
public import IdealGeneration.CubicTenTraceKernelCertificate
public import IdealGeneration.CubicTenNormalPivotCertificate
public import IdealGeneration.CubicTenTracePivotCertificate

public import IdealGeneration.CubicTenEvaluationCoordinates

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Entrywise agreement of the numerical rank certificates and the marked cone. -/

noncomputable section
namespace IdealGeneration.CubicTen
open MvPolynomial Matrix ConeMonomialChart CertifiedRank CubicTenPackedData
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

private def actualNormalRow (i : Fin 75) : List ℕ :=
  List.ofFn fun j : Fin 100 => evalTriple (pointFast i) (tableGet 7 normalTriples j.val)

private def actualTraceRow (i : Fin 90) : List ℕ :=
  List.ofFn fun j : Fin 120 => evalTriple (tracePointFast i) (tableGet 7 traceTriples j.val)

private def certifiedNormalRow (i : Fin 75) : List ℕ :=
  List.ofFn fun j : Fin 100 => rowValue (EPRow i) j % modulus

private def certifiedTraceRow (i : Fin 90) : List ℕ :=
  List.ofFn fun j : Fin 120 => rowValue (ETRow i) j % modulus

private theorem normalEntry_of_row (i : Fin 75) (j : Fin 100)
    (hr : actualNormalRow i = certifiedNormalRow i) :
    normalEvaluationMatrix (ZMod modulus) i j = EP i j := by
  have h := congrFun (List.ofFn_injective hr) j
  have hc := congrArg (fun x : ℕ => (x : ZMod modulus)) h
  simpa only [cast_evalTriple, pointFast_eq, normalTriple_exp, ZMod.natCast_mod, EP_apply,
    normalEvaluationMatrix, evaluationMatrix] using hc

private theorem traceEntry_of_row (i : Fin 90) (j : Fin 120)
    (hr : actualTraceRow i = certifiedTraceRow i) :
    traceEvaluationMatrix (ZMod modulus) i j = ET i j := by
  have h := congrFun (List.ofFn_injective hr) j
  have hc := congrArg (fun x : ℕ => (x : ZMod modulus)) h
  simpa only [cast_evalTriple, tracePointFast_eq, traceTriple_exp, ZMod.natCast_mod, ET_apply,
    traceEvaluationMatrix, evaluationMatrix] using hc


private def normalEvaluationAgreementAt (i : Fin 75) : Prop :=
  actualNormalRow i = certifiedNormalRow i

private theorem normalEvaluationAgreement000 : normalEvaluationAgreementAt (0 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement001 : normalEvaluationAgreementAt (1 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement002 : normalEvaluationAgreementAt (2 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement003 : normalEvaluationAgreementAt (3 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement004 : normalEvaluationAgreementAt (4 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement005 : normalEvaluationAgreementAt (5 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement006 : normalEvaluationAgreementAt (6 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement007 : normalEvaluationAgreementAt (7 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement008 : normalEvaluationAgreementAt (8 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement009 : normalEvaluationAgreementAt (9 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement010 : normalEvaluationAgreementAt (10 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement011 : normalEvaluationAgreementAt (11 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement012 : normalEvaluationAgreementAt (12 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement013 : normalEvaluationAgreementAt (13 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement014 : normalEvaluationAgreementAt (14 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement015 : normalEvaluationAgreementAt (15 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement016 : normalEvaluationAgreementAt (16 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement017 : normalEvaluationAgreementAt (17 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement018 : normalEvaluationAgreementAt (18 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement019 : normalEvaluationAgreementAt (19 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement020 : normalEvaluationAgreementAt (20 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement021 : normalEvaluationAgreementAt (21 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement022 : normalEvaluationAgreementAt (22 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement023 : normalEvaluationAgreementAt (23 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement024 : normalEvaluationAgreementAt (24 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement025 : normalEvaluationAgreementAt (25 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement026 : normalEvaluationAgreementAt (26 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement027 : normalEvaluationAgreementAt (27 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement028 : normalEvaluationAgreementAt (28 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement029 : normalEvaluationAgreementAt (29 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement030 : normalEvaluationAgreementAt (30 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement031 : normalEvaluationAgreementAt (31 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement032 : normalEvaluationAgreementAt (32 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement033 : normalEvaluationAgreementAt (33 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement034 : normalEvaluationAgreementAt (34 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement035 : normalEvaluationAgreementAt (35 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement036 : normalEvaluationAgreementAt (36 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement037 : normalEvaluationAgreementAt (37 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement038 : normalEvaluationAgreementAt (38 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement039 : normalEvaluationAgreementAt (39 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement040 : normalEvaluationAgreementAt (40 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement041 : normalEvaluationAgreementAt (41 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement042 : normalEvaluationAgreementAt (42 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement043 : normalEvaluationAgreementAt (43 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement044 : normalEvaluationAgreementAt (44 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement045 : normalEvaluationAgreementAt (45 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement046 : normalEvaluationAgreementAt (46 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement047 : normalEvaluationAgreementAt (47 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement048 : normalEvaluationAgreementAt (48 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement049 : normalEvaluationAgreementAt (49 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement050 : normalEvaluationAgreementAt (50 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement051 : normalEvaluationAgreementAt (51 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement052 : normalEvaluationAgreementAt (52 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement053 : normalEvaluationAgreementAt (53 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement054 : normalEvaluationAgreementAt (54 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement055 : normalEvaluationAgreementAt (55 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement056 : normalEvaluationAgreementAt (56 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement057 : normalEvaluationAgreementAt (57 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement058 : normalEvaluationAgreementAt (58 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement059 : normalEvaluationAgreementAt (59 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement060 : normalEvaluationAgreementAt (60 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement061 : normalEvaluationAgreementAt (61 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement062 : normalEvaluationAgreementAt (62 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement063 : normalEvaluationAgreementAt (63 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement064 : normalEvaluationAgreementAt (64 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement065 : normalEvaluationAgreementAt (65 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement066 : normalEvaluationAgreementAt (66 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement067 : normalEvaluationAgreementAt (67 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement068 : normalEvaluationAgreementAt (68 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement069 : normalEvaluationAgreementAt (69 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement070 : normalEvaluationAgreementAt (70 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement071 : normalEvaluationAgreementAt (71 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement072 : normalEvaluationAgreementAt (72 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement073 : normalEvaluationAgreementAt (73 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel
private theorem normalEvaluationAgreement074 : normalEvaluationAgreementAt (74 : Fin 75) := by unfold normalEvaluationAgreementAt; decide +kernel

private theorem normalEvaluationAgreement : ∀ i : Fin 75, normalEvaluationAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement000) (finOne normalEvaluationAgreement001)) (finSplit (finOne normalEvaluationAgreement002) (finOne normalEvaluationAgreement003))) (finSplit (finSplit (finOne normalEvaluationAgreement004) (finOne normalEvaluationAgreement005)) (finSplit (finOne normalEvaluationAgreement006) (finSplit (finOne normalEvaluationAgreement007) (finOne normalEvaluationAgreement008))))) (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement009) (finOne normalEvaluationAgreement010)) (finSplit (finOne normalEvaluationAgreement011) (finOne normalEvaluationAgreement012))) (finSplit (finSplit (finOne normalEvaluationAgreement013) (finOne normalEvaluationAgreement014)) (finSplit (finOne normalEvaluationAgreement015) (finSplit (finOne normalEvaluationAgreement016) (finOne normalEvaluationAgreement017)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement018) (finOne normalEvaluationAgreement019)) (finSplit (finOne normalEvaluationAgreement020) (finOne normalEvaluationAgreement021))) (finSplit (finSplit (finOne normalEvaluationAgreement022) (finOne normalEvaluationAgreement023)) (finSplit (finOne normalEvaluationAgreement024) (finSplit (finOne normalEvaluationAgreement025) (finOne normalEvaluationAgreement026))))) (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement027) (finOne normalEvaluationAgreement028)) (finSplit (finOne normalEvaluationAgreement029) (finSplit (finOne normalEvaluationAgreement030) (finOne normalEvaluationAgreement031)))) (finSplit (finSplit (finOne normalEvaluationAgreement032) (finOne normalEvaluationAgreement033)) (finSplit (finOne normalEvaluationAgreement034) (finSplit (finOne normalEvaluationAgreement035) (finOne normalEvaluationAgreement036))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement037) (finOne normalEvaluationAgreement038)) (finSplit (finOne normalEvaluationAgreement039) (finOne normalEvaluationAgreement040))) (finSplit (finSplit (finOne normalEvaluationAgreement041) (finOne normalEvaluationAgreement042)) (finSplit (finOne normalEvaluationAgreement043) (finSplit (finOne normalEvaluationAgreement044) (finOne normalEvaluationAgreement045))))) (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement046) (finOne normalEvaluationAgreement047)) (finSplit (finOne normalEvaluationAgreement048) (finSplit (finOne normalEvaluationAgreement049) (finOne normalEvaluationAgreement050)))) (finSplit (finSplit (finOne normalEvaluationAgreement051) (finOne normalEvaluationAgreement052)) (finSplit (finOne normalEvaluationAgreement053) (finSplit (finOne normalEvaluationAgreement054) (finOne normalEvaluationAgreement055)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement056) (finOne normalEvaluationAgreement057)) (finSplit (finOne normalEvaluationAgreement058) (finOne normalEvaluationAgreement059))) (finSplit (finSplit (finOne normalEvaluationAgreement060) (finOne normalEvaluationAgreement061)) (finSplit (finOne normalEvaluationAgreement062) (finSplit (finOne normalEvaluationAgreement063) (finOne normalEvaluationAgreement064))))) (finSplit (finSplit (finSplit (finOne normalEvaluationAgreement065) (finOne normalEvaluationAgreement066)) (finSplit (finOne normalEvaluationAgreement067) (finSplit (finOne normalEvaluationAgreement068) (finOne normalEvaluationAgreement069)))) (finSplit (finSplit (finOne normalEvaluationAgreement070) (finOne normalEvaluationAgreement071)) (finSplit (finOne normalEvaluationAgreement072) (finSplit (finOne normalEvaluationAgreement073) (finOne normalEvaluationAgreement074))))))))

private def traceEvaluationAgreementAt (i : Fin 90) : Prop :=
  actualTraceRow i = certifiedTraceRow i

private theorem traceEvaluationAgreement000 : traceEvaluationAgreementAt (0 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement001 : traceEvaluationAgreementAt (1 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement002 : traceEvaluationAgreementAt (2 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement003 : traceEvaluationAgreementAt (3 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement004 : traceEvaluationAgreementAt (4 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement005 : traceEvaluationAgreementAt (5 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement006 : traceEvaluationAgreementAt (6 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement007 : traceEvaluationAgreementAt (7 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement008 : traceEvaluationAgreementAt (8 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement009 : traceEvaluationAgreementAt (9 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement010 : traceEvaluationAgreementAt (10 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement011 : traceEvaluationAgreementAt (11 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement012 : traceEvaluationAgreementAt (12 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement013 : traceEvaluationAgreementAt (13 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement014 : traceEvaluationAgreementAt (14 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement015 : traceEvaluationAgreementAt (15 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement016 : traceEvaluationAgreementAt (16 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement017 : traceEvaluationAgreementAt (17 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement018 : traceEvaluationAgreementAt (18 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement019 : traceEvaluationAgreementAt (19 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement020 : traceEvaluationAgreementAt (20 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement021 : traceEvaluationAgreementAt (21 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement022 : traceEvaluationAgreementAt (22 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement023 : traceEvaluationAgreementAt (23 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement024 : traceEvaluationAgreementAt (24 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement025 : traceEvaluationAgreementAt (25 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement026 : traceEvaluationAgreementAt (26 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement027 : traceEvaluationAgreementAt (27 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement028 : traceEvaluationAgreementAt (28 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement029 : traceEvaluationAgreementAt (29 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement030 : traceEvaluationAgreementAt (30 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement031 : traceEvaluationAgreementAt (31 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement032 : traceEvaluationAgreementAt (32 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement033 : traceEvaluationAgreementAt (33 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement034 : traceEvaluationAgreementAt (34 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement035 : traceEvaluationAgreementAt (35 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement036 : traceEvaluationAgreementAt (36 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement037 : traceEvaluationAgreementAt (37 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement038 : traceEvaluationAgreementAt (38 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement039 : traceEvaluationAgreementAt (39 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement040 : traceEvaluationAgreementAt (40 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement041 : traceEvaluationAgreementAt (41 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement042 : traceEvaluationAgreementAt (42 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement043 : traceEvaluationAgreementAt (43 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement044 : traceEvaluationAgreementAt (44 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement045 : traceEvaluationAgreementAt (45 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement046 : traceEvaluationAgreementAt (46 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement047 : traceEvaluationAgreementAt (47 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement048 : traceEvaluationAgreementAt (48 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement049 : traceEvaluationAgreementAt (49 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement050 : traceEvaluationAgreementAt (50 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement051 : traceEvaluationAgreementAt (51 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement052 : traceEvaluationAgreementAt (52 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement053 : traceEvaluationAgreementAt (53 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement054 : traceEvaluationAgreementAt (54 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement055 : traceEvaluationAgreementAt (55 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement056 : traceEvaluationAgreementAt (56 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement057 : traceEvaluationAgreementAt (57 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement058 : traceEvaluationAgreementAt (58 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement059 : traceEvaluationAgreementAt (59 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement060 : traceEvaluationAgreementAt (60 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement061 : traceEvaluationAgreementAt (61 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement062 : traceEvaluationAgreementAt (62 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement063 : traceEvaluationAgreementAt (63 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement064 : traceEvaluationAgreementAt (64 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement065 : traceEvaluationAgreementAt (65 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement066 : traceEvaluationAgreementAt (66 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement067 : traceEvaluationAgreementAt (67 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement068 : traceEvaluationAgreementAt (68 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement069 : traceEvaluationAgreementAt (69 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement070 : traceEvaluationAgreementAt (70 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement071 : traceEvaluationAgreementAt (71 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement072 : traceEvaluationAgreementAt (72 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement073 : traceEvaluationAgreementAt (73 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement074 : traceEvaluationAgreementAt (74 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement075 : traceEvaluationAgreementAt (75 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement076 : traceEvaluationAgreementAt (76 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement077 : traceEvaluationAgreementAt (77 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement078 : traceEvaluationAgreementAt (78 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement079 : traceEvaluationAgreementAt (79 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement080 : traceEvaluationAgreementAt (80 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement081 : traceEvaluationAgreementAt (81 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement082 : traceEvaluationAgreementAt (82 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement083 : traceEvaluationAgreementAt (83 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement084 : traceEvaluationAgreementAt (84 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement085 : traceEvaluationAgreementAt (85 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement086 : traceEvaluationAgreementAt (86 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement087 : traceEvaluationAgreementAt (87 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement088 : traceEvaluationAgreementAt (88 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel
private theorem traceEvaluationAgreement089 : traceEvaluationAgreementAt (89 : Fin 90) := by unfold traceEvaluationAgreementAt; decide +kernel

private theorem traceEvaluationAgreement : ∀ i : Fin 90, traceEvaluationAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement000) (finOne traceEvaluationAgreement001)) (finSplit (finOne traceEvaluationAgreement002) (finSplit (finOne traceEvaluationAgreement003) (finOne traceEvaluationAgreement004)))) (finSplit (finSplit (finOne traceEvaluationAgreement005) (finSplit (finOne traceEvaluationAgreement006) (finOne traceEvaluationAgreement007))) (finSplit (finOne traceEvaluationAgreement008) (finSplit (finOne traceEvaluationAgreement009) (finOne traceEvaluationAgreement010))))) (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement011) (finOne traceEvaluationAgreement012)) (finSplit (finOne traceEvaluationAgreement013) (finSplit (finOne traceEvaluationAgreement014) (finOne traceEvaluationAgreement015)))) (finSplit (finSplit (finOne traceEvaluationAgreement016) (finSplit (finOne traceEvaluationAgreement017) (finOne traceEvaluationAgreement018))) (finSplit (finOne traceEvaluationAgreement019) (finSplit (finOne traceEvaluationAgreement020) (finOne traceEvaluationAgreement021)))))) (finSplit (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement022) (finOne traceEvaluationAgreement023)) (finSplit (finOne traceEvaluationAgreement024) (finSplit (finOne traceEvaluationAgreement025) (finOne traceEvaluationAgreement026)))) (finSplit (finSplit (finOne traceEvaluationAgreement027) (finSplit (finOne traceEvaluationAgreement028) (finOne traceEvaluationAgreement029))) (finSplit (finOne traceEvaluationAgreement030) (finSplit (finOne traceEvaluationAgreement031) (finOne traceEvaluationAgreement032))))) (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement033) (finSplit (finOne traceEvaluationAgreement034) (finOne traceEvaluationAgreement035))) (finSplit (finOne traceEvaluationAgreement036) (finSplit (finOne traceEvaluationAgreement037) (finOne traceEvaluationAgreement038)))) (finSplit (finSplit (finOne traceEvaluationAgreement039) (finSplit (finOne traceEvaluationAgreement040) (finOne traceEvaluationAgreement041))) (finSplit (finOne traceEvaluationAgreement042) (finSplit (finOne traceEvaluationAgreement043) (finOne traceEvaluationAgreement044))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement045) (finOne traceEvaluationAgreement046)) (finSplit (finOne traceEvaluationAgreement047) (finSplit (finOne traceEvaluationAgreement048) (finOne traceEvaluationAgreement049)))) (finSplit (finSplit (finOne traceEvaluationAgreement050) (finSplit (finOne traceEvaluationAgreement051) (finOne traceEvaluationAgreement052))) (finSplit (finOne traceEvaluationAgreement053) (finSplit (finOne traceEvaluationAgreement054) (finOne traceEvaluationAgreement055))))) (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement056) (finOne traceEvaluationAgreement057)) (finSplit (finOne traceEvaluationAgreement058) (finSplit (finOne traceEvaluationAgreement059) (finOne traceEvaluationAgreement060)))) (finSplit (finSplit (finOne traceEvaluationAgreement061) (finSplit (finOne traceEvaluationAgreement062) (finOne traceEvaluationAgreement063))) (finSplit (finOne traceEvaluationAgreement064) (finSplit (finOne traceEvaluationAgreement065) (finOne traceEvaluationAgreement066)))))) (finSplit (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement067) (finOne traceEvaluationAgreement068)) (finSplit (finOne traceEvaluationAgreement069) (finSplit (finOne traceEvaluationAgreement070) (finOne traceEvaluationAgreement071)))) (finSplit (finSplit (finOne traceEvaluationAgreement072) (finSplit (finOne traceEvaluationAgreement073) (finOne traceEvaluationAgreement074))) (finSplit (finOne traceEvaluationAgreement075) (finSplit (finOne traceEvaluationAgreement076) (finOne traceEvaluationAgreement077))))) (finSplit (finSplit (finSplit (finOne traceEvaluationAgreement078) (finSplit (finOne traceEvaluationAgreement079) (finOne traceEvaluationAgreement080))) (finSplit (finOne traceEvaluationAgreement081) (finSplit (finOne traceEvaluationAgreement082) (finOne traceEvaluationAgreement083)))) (finSplit (finSplit (finOne traceEvaluationAgreement084) (finSplit (finOne traceEvaluationAgreement085) (finOne traceEvaluationAgreement086))) (finSplit (finOne traceEvaluationAgreement087) (finSplit (finOne traceEvaluationAgreement088) (finOne traceEvaluationAgreement089))))))))


theorem normalEvaluationMatrix_eq_EP : normalEvaluationMatrix (ZMod modulus) = EP := by
  ext i j
  exact normalEntry_of_row i j (normalEvaluationAgreement i)

theorem traceEvaluationMatrix_eq_ET : traceEvaluationMatrix (ZMod modulus) = ET := by
  ext i j
  exact traceEntry_of_row i j (traceEvaluationAgreement i)

def normalPivotColumn (j : Fin 75) : Fin 100 :=
  Fin.ofNat 100 normalPivotIndices[j.val]!

def tracePivotColumn (j : Fin 90) : Fin 120 :=
  Fin.ofNat 120 tracePivotIndices[j.val]!

private def actualNormalPivotRow (i : Fin 75) : List ℕ :=
  List.ofFn fun j : Fin 75 => rowValue (EPRow i) (normalPivotColumn j)

private def actualTracePivotRow (i : Fin 90) : List ℕ :=
  List.ofFn fun j : Fin 90 => rowValue (ETRow i) (tracePivotColumn j)

private def certifiedNormalPivotRow (i : Fin 75) : List ℕ :=
  List.ofFn fun j : Fin 75 => rowValue (normalPivotRow i) j

private def certifiedTracePivotRow (i : Fin 90) : List ℕ :=
  List.ofFn fun j : Fin 90 => rowValue (tracePivotRow i) j

private def normalPivotAgreementAt (i : Fin 75) : Prop :=
  actualNormalPivotRow i = certifiedNormalPivotRow i

private theorem normalPivotAgreement000 : normalPivotAgreementAt (0 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement001 : normalPivotAgreementAt (1 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement002 : normalPivotAgreementAt (2 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement003 : normalPivotAgreementAt (3 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement004 : normalPivotAgreementAt (4 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement005 : normalPivotAgreementAt (5 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement006 : normalPivotAgreementAt (6 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement007 : normalPivotAgreementAt (7 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement008 : normalPivotAgreementAt (8 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement009 : normalPivotAgreementAt (9 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement010 : normalPivotAgreementAt (10 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement011 : normalPivotAgreementAt (11 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement012 : normalPivotAgreementAt (12 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement013 : normalPivotAgreementAt (13 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement014 : normalPivotAgreementAt (14 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement015 : normalPivotAgreementAt (15 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement016 : normalPivotAgreementAt (16 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement017 : normalPivotAgreementAt (17 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement018 : normalPivotAgreementAt (18 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement019 : normalPivotAgreementAt (19 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement020 : normalPivotAgreementAt (20 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement021 : normalPivotAgreementAt (21 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement022 : normalPivotAgreementAt (22 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement023 : normalPivotAgreementAt (23 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement024 : normalPivotAgreementAt (24 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement025 : normalPivotAgreementAt (25 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement026 : normalPivotAgreementAt (26 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement027 : normalPivotAgreementAt (27 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement028 : normalPivotAgreementAt (28 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement029 : normalPivotAgreementAt (29 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement030 : normalPivotAgreementAt (30 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement031 : normalPivotAgreementAt (31 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement032 : normalPivotAgreementAt (32 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement033 : normalPivotAgreementAt (33 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement034 : normalPivotAgreementAt (34 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement035 : normalPivotAgreementAt (35 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement036 : normalPivotAgreementAt (36 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement037 : normalPivotAgreementAt (37 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement038 : normalPivotAgreementAt (38 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement039 : normalPivotAgreementAt (39 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement040 : normalPivotAgreementAt (40 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement041 : normalPivotAgreementAt (41 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement042 : normalPivotAgreementAt (42 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement043 : normalPivotAgreementAt (43 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement044 : normalPivotAgreementAt (44 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement045 : normalPivotAgreementAt (45 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement046 : normalPivotAgreementAt (46 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement047 : normalPivotAgreementAt (47 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement048 : normalPivotAgreementAt (48 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement049 : normalPivotAgreementAt (49 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement050 : normalPivotAgreementAt (50 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement051 : normalPivotAgreementAt (51 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement052 : normalPivotAgreementAt (52 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement053 : normalPivotAgreementAt (53 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement054 : normalPivotAgreementAt (54 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement055 : normalPivotAgreementAt (55 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement056 : normalPivotAgreementAt (56 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement057 : normalPivotAgreementAt (57 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement058 : normalPivotAgreementAt (58 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement059 : normalPivotAgreementAt (59 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement060 : normalPivotAgreementAt (60 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement061 : normalPivotAgreementAt (61 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement062 : normalPivotAgreementAt (62 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement063 : normalPivotAgreementAt (63 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement064 : normalPivotAgreementAt (64 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement065 : normalPivotAgreementAt (65 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement066 : normalPivotAgreementAt (66 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement067 : normalPivotAgreementAt (67 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement068 : normalPivotAgreementAt (68 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement069 : normalPivotAgreementAt (69 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement070 : normalPivotAgreementAt (70 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement071 : normalPivotAgreementAt (71 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement072 : normalPivotAgreementAt (72 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement073 : normalPivotAgreementAt (73 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel
private theorem normalPivotAgreement074 : normalPivotAgreementAt (74 : Fin 75) := by unfold normalPivotAgreementAt; decide +kernel

private theorem normalPivotAgreement : ∀ i : Fin 75, normalPivotAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalPivotAgreement000) (finOne normalPivotAgreement001)) (finSplit (finOne normalPivotAgreement002) (finOne normalPivotAgreement003))) (finSplit (finSplit (finOne normalPivotAgreement004) (finOne normalPivotAgreement005)) (finSplit (finOne normalPivotAgreement006) (finSplit (finOne normalPivotAgreement007) (finOne normalPivotAgreement008))))) (finSplit (finSplit (finSplit (finOne normalPivotAgreement009) (finOne normalPivotAgreement010)) (finSplit (finOne normalPivotAgreement011) (finOne normalPivotAgreement012))) (finSplit (finSplit (finOne normalPivotAgreement013) (finOne normalPivotAgreement014)) (finSplit (finOne normalPivotAgreement015) (finSplit (finOne normalPivotAgreement016) (finOne normalPivotAgreement017)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalPivotAgreement018) (finOne normalPivotAgreement019)) (finSplit (finOne normalPivotAgreement020) (finOne normalPivotAgreement021))) (finSplit (finSplit (finOne normalPivotAgreement022) (finOne normalPivotAgreement023)) (finSplit (finOne normalPivotAgreement024) (finSplit (finOne normalPivotAgreement025) (finOne normalPivotAgreement026))))) (finSplit (finSplit (finSplit (finOne normalPivotAgreement027) (finOne normalPivotAgreement028)) (finSplit (finOne normalPivotAgreement029) (finSplit (finOne normalPivotAgreement030) (finOne normalPivotAgreement031)))) (finSplit (finSplit (finOne normalPivotAgreement032) (finOne normalPivotAgreement033)) (finSplit (finOne normalPivotAgreement034) (finSplit (finOne normalPivotAgreement035) (finOne normalPivotAgreement036))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalPivotAgreement037) (finOne normalPivotAgreement038)) (finSplit (finOne normalPivotAgreement039) (finOne normalPivotAgreement040))) (finSplit (finSplit (finOne normalPivotAgreement041) (finOne normalPivotAgreement042)) (finSplit (finOne normalPivotAgreement043) (finSplit (finOne normalPivotAgreement044) (finOne normalPivotAgreement045))))) (finSplit (finSplit (finSplit (finOne normalPivotAgreement046) (finOne normalPivotAgreement047)) (finSplit (finOne normalPivotAgreement048) (finSplit (finOne normalPivotAgreement049) (finOne normalPivotAgreement050)))) (finSplit (finSplit (finOne normalPivotAgreement051) (finOne normalPivotAgreement052)) (finSplit (finOne normalPivotAgreement053) (finSplit (finOne normalPivotAgreement054) (finOne normalPivotAgreement055)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalPivotAgreement056) (finOne normalPivotAgreement057)) (finSplit (finOne normalPivotAgreement058) (finOne normalPivotAgreement059))) (finSplit (finSplit (finOne normalPivotAgreement060) (finOne normalPivotAgreement061)) (finSplit (finOne normalPivotAgreement062) (finSplit (finOne normalPivotAgreement063) (finOne normalPivotAgreement064))))) (finSplit (finSplit (finSplit (finOne normalPivotAgreement065) (finOne normalPivotAgreement066)) (finSplit (finOne normalPivotAgreement067) (finSplit (finOne normalPivotAgreement068) (finOne normalPivotAgreement069)))) (finSplit (finSplit (finOne normalPivotAgreement070) (finOne normalPivotAgreement071)) (finSplit (finOne normalPivotAgreement072) (finSplit (finOne normalPivotAgreement073) (finOne normalPivotAgreement074))))))))

private def tracePivotAgreementAt (i : Fin 90) : Prop :=
  actualTracePivotRow i = certifiedTracePivotRow i

private theorem tracePivotAgreement000 : tracePivotAgreementAt (0 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement001 : tracePivotAgreementAt (1 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement002 : tracePivotAgreementAt (2 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement003 : tracePivotAgreementAt (3 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement004 : tracePivotAgreementAt (4 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement005 : tracePivotAgreementAt (5 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement006 : tracePivotAgreementAt (6 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement007 : tracePivotAgreementAt (7 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement008 : tracePivotAgreementAt (8 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement009 : tracePivotAgreementAt (9 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement010 : tracePivotAgreementAt (10 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement011 : tracePivotAgreementAt (11 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement012 : tracePivotAgreementAt (12 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement013 : tracePivotAgreementAt (13 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement014 : tracePivotAgreementAt (14 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement015 : tracePivotAgreementAt (15 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement016 : tracePivotAgreementAt (16 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement017 : tracePivotAgreementAt (17 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement018 : tracePivotAgreementAt (18 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement019 : tracePivotAgreementAt (19 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement020 : tracePivotAgreementAt (20 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement021 : tracePivotAgreementAt (21 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement022 : tracePivotAgreementAt (22 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement023 : tracePivotAgreementAt (23 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement024 : tracePivotAgreementAt (24 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement025 : tracePivotAgreementAt (25 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement026 : tracePivotAgreementAt (26 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement027 : tracePivotAgreementAt (27 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement028 : tracePivotAgreementAt (28 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement029 : tracePivotAgreementAt (29 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement030 : tracePivotAgreementAt (30 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement031 : tracePivotAgreementAt (31 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement032 : tracePivotAgreementAt (32 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement033 : tracePivotAgreementAt (33 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement034 : tracePivotAgreementAt (34 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement035 : tracePivotAgreementAt (35 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement036 : tracePivotAgreementAt (36 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement037 : tracePivotAgreementAt (37 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement038 : tracePivotAgreementAt (38 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement039 : tracePivotAgreementAt (39 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement040 : tracePivotAgreementAt (40 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement041 : tracePivotAgreementAt (41 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement042 : tracePivotAgreementAt (42 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement043 : tracePivotAgreementAt (43 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement044 : tracePivotAgreementAt (44 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement045 : tracePivotAgreementAt (45 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement046 : tracePivotAgreementAt (46 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement047 : tracePivotAgreementAt (47 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement048 : tracePivotAgreementAt (48 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement049 : tracePivotAgreementAt (49 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement050 : tracePivotAgreementAt (50 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement051 : tracePivotAgreementAt (51 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement052 : tracePivotAgreementAt (52 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement053 : tracePivotAgreementAt (53 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement054 : tracePivotAgreementAt (54 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement055 : tracePivotAgreementAt (55 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement056 : tracePivotAgreementAt (56 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement057 : tracePivotAgreementAt (57 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement058 : tracePivotAgreementAt (58 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement059 : tracePivotAgreementAt (59 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement060 : tracePivotAgreementAt (60 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement061 : tracePivotAgreementAt (61 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement062 : tracePivotAgreementAt (62 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement063 : tracePivotAgreementAt (63 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement064 : tracePivotAgreementAt (64 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement065 : tracePivotAgreementAt (65 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement066 : tracePivotAgreementAt (66 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement067 : tracePivotAgreementAt (67 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement068 : tracePivotAgreementAt (68 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement069 : tracePivotAgreementAt (69 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement070 : tracePivotAgreementAt (70 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement071 : tracePivotAgreementAt (71 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement072 : tracePivotAgreementAt (72 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement073 : tracePivotAgreementAt (73 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement074 : tracePivotAgreementAt (74 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement075 : tracePivotAgreementAt (75 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement076 : tracePivotAgreementAt (76 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement077 : tracePivotAgreementAt (77 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement078 : tracePivotAgreementAt (78 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement079 : tracePivotAgreementAt (79 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement080 : tracePivotAgreementAt (80 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement081 : tracePivotAgreementAt (81 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement082 : tracePivotAgreementAt (82 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement083 : tracePivotAgreementAt (83 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement084 : tracePivotAgreementAt (84 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement085 : tracePivotAgreementAt (85 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement086 : tracePivotAgreementAt (86 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement087 : tracePivotAgreementAt (87 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement088 : tracePivotAgreementAt (88 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel
private theorem tracePivotAgreement089 : tracePivotAgreementAt (89 : Fin 90) := by unfold tracePivotAgreementAt; decide +kernel

private theorem tracePivotAgreement : ∀ i : Fin 90, tracePivotAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne tracePivotAgreement000) (finOne tracePivotAgreement001)) (finSplit (finOne tracePivotAgreement002) (finSplit (finOne tracePivotAgreement003) (finOne tracePivotAgreement004)))) (finSplit (finSplit (finOne tracePivotAgreement005) (finSplit (finOne tracePivotAgreement006) (finOne tracePivotAgreement007))) (finSplit (finOne tracePivotAgreement008) (finSplit (finOne tracePivotAgreement009) (finOne tracePivotAgreement010))))) (finSplit (finSplit (finSplit (finOne tracePivotAgreement011) (finOne tracePivotAgreement012)) (finSplit (finOne tracePivotAgreement013) (finSplit (finOne tracePivotAgreement014) (finOne tracePivotAgreement015)))) (finSplit (finSplit (finOne tracePivotAgreement016) (finSplit (finOne tracePivotAgreement017) (finOne tracePivotAgreement018))) (finSplit (finOne tracePivotAgreement019) (finSplit (finOne tracePivotAgreement020) (finOne tracePivotAgreement021)))))) (finSplit (finSplit (finSplit (finSplit (finOne tracePivotAgreement022) (finOne tracePivotAgreement023)) (finSplit (finOne tracePivotAgreement024) (finSplit (finOne tracePivotAgreement025) (finOne tracePivotAgreement026)))) (finSplit (finSplit (finOne tracePivotAgreement027) (finSplit (finOne tracePivotAgreement028) (finOne tracePivotAgreement029))) (finSplit (finOne tracePivotAgreement030) (finSplit (finOne tracePivotAgreement031) (finOne tracePivotAgreement032))))) (finSplit (finSplit (finSplit (finOne tracePivotAgreement033) (finSplit (finOne tracePivotAgreement034) (finOne tracePivotAgreement035))) (finSplit (finOne tracePivotAgreement036) (finSplit (finOne tracePivotAgreement037) (finOne tracePivotAgreement038)))) (finSplit (finSplit (finOne tracePivotAgreement039) (finSplit (finOne tracePivotAgreement040) (finOne tracePivotAgreement041))) (finSplit (finOne tracePivotAgreement042) (finSplit (finOne tracePivotAgreement043) (finOne tracePivotAgreement044))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne tracePivotAgreement045) (finOne tracePivotAgreement046)) (finSplit (finOne tracePivotAgreement047) (finSplit (finOne tracePivotAgreement048) (finOne tracePivotAgreement049)))) (finSplit (finSplit (finOne tracePivotAgreement050) (finSplit (finOne tracePivotAgreement051) (finOne tracePivotAgreement052))) (finSplit (finOne tracePivotAgreement053) (finSplit (finOne tracePivotAgreement054) (finOne tracePivotAgreement055))))) (finSplit (finSplit (finSplit (finOne tracePivotAgreement056) (finOne tracePivotAgreement057)) (finSplit (finOne tracePivotAgreement058) (finSplit (finOne tracePivotAgreement059) (finOne tracePivotAgreement060)))) (finSplit (finSplit (finOne tracePivotAgreement061) (finSplit (finOne tracePivotAgreement062) (finOne tracePivotAgreement063))) (finSplit (finOne tracePivotAgreement064) (finSplit (finOne tracePivotAgreement065) (finOne tracePivotAgreement066)))))) (finSplit (finSplit (finSplit (finSplit (finOne tracePivotAgreement067) (finOne tracePivotAgreement068)) (finSplit (finOne tracePivotAgreement069) (finSplit (finOne tracePivotAgreement070) (finOne tracePivotAgreement071)))) (finSplit (finSplit (finOne tracePivotAgreement072) (finSplit (finOne tracePivotAgreement073) (finOne tracePivotAgreement074))) (finSplit (finOne tracePivotAgreement075) (finSplit (finOne tracePivotAgreement076) (finOne tracePivotAgreement077))))) (finSplit (finSplit (finSplit (finOne tracePivotAgreement078) (finSplit (finOne tracePivotAgreement079) (finOne tracePivotAgreement080))) (finSplit (finOne tracePivotAgreement081) (finSplit (finOne tracePivotAgreement082) (finOne tracePivotAgreement083)))) (finSplit (finSplit (finOne tracePivotAgreement084) (finSplit (finOne tracePivotAgreement085) (finOne tracePivotAgreement086))) (finSplit (finOne tracePivotAgreement087) (finSplit (finOne tracePivotAgreement088) (finOne tracePivotAgreement089))))))))

theorem normalPivot_eq_submatrix :
    EP.submatrix id normalPivotColumn = normalPivot := by
  ext i j
  have hr : actualNormalPivotRow i = certifiedNormalPivotRow i := normalPivotAgreement i
  have h := congrFun (List.ofFn_injective hr) j
  have hc := congrArg (fun x : ℕ => (x : ZMod modulus)) h
  simpa only [Matrix.submatrix_apply, id_eq, EP_apply, normalPivot_apply] using hc

theorem tracePivot_eq_submatrix :
    ET.submatrix id tracePivotColumn = tracePivot := by
  ext i j
  have hr : actualTracePivotRow i = certifiedTracePivotRow i := tracePivotAgreement i
  have h := congrFun (List.ofFn_injective hr) j
  have hc := congrArg (fun x : ℕ => (x : ZMod modulus)) h
  simpa only [Matrix.submatrix_apply, id_eq, ET_apply, tracePivot_apply] using hc

end IdealGeneration.CubicTen
