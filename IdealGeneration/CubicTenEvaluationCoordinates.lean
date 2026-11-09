module

public import IdealGeneration.CubicTenGeometry

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Packed coordinates and three-variable evaluation of the cubic monomials. -/

noncomputable section
namespace IdealGeneration.CubicTen
open MvPolynomial Matrix ConeMonomialChart CertifiedRank CubicTenPackedData
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

private def tripleExponent (n : ℕ) [NeZero n] (code : ℕ) : Fin n →₀ ℕ :=
  Finsupp.single (Fin.ofNat n code) 1 +
    Finsupp.single (Fin.ofNat n (code / n)) 1 +
    Finsupp.single (Fin.ofNat n (code / n / n)) 1

private def tripleExponentDigit (n : ℕ) [NeZero n] (code : ℕ) (j : Fin n) : ℕ :=
  (if Fin.ofNat n code = j then 1 else 0) +
    (if Fin.ofNat n (code / n) = j then 1 else 0) +
    (if Fin.ofNat n (code / n / n) = j then 1 else 0)

private theorem tripleExponent_apply (n : ℕ) [NeZero n] (code : ℕ) (j : Fin n) :
    tripleExponent n code j = tripleExponentDigit n code j := by
  simp [tripleExponent, tripleExponentDigit, Finsupp.single_apply]

def evalTriple {n : ℕ} [NeZero n] (z : Fin n → ℕ) (code : ℕ) : ℕ :=
  z (Fin.ofNat n code) * z (Fin.ofNat n (code / n)) * z (Fin.ofNat n (code / n / n)) % modulus

theorem cast_evalTriple {n : ℕ} [NeZero n] (z : Fin n → ℕ) (code : ℕ) :
    (evalTriple z code : ZMod modulus) =
      ∏ k, (z k : ZMod modulus) ^ tripleExponent n code k := by
  let a := Fin.ofNat n code
  let b := Fin.ofNat n (code / n)
  let c := Fin.ofNat n (code / n / n)
  have hmono : monomial (tripleExponent n code) (1 : ZMod modulus) = X a * X b * X c := by
    change _ = monomial (Finsupp.single a 1) 1 * monomial (Finsupp.single b 1) 1 *
      monomial (Finsupp.single c 1) 1
    simp [tripleExponent, a, b, c, monomial_mul_monomial]
  have hval := congrArg (eval (fun k => (z k : ZMod modulus))) hmono
  rw [evalTriple, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul]
  simpa [a, b, c, eval_monomial, Finsupp.prod_fintype] using hval.symm

private def pointFastData : Table ℕ 7 :=
  (((((((396924593111041, 75858529272861498488869771415523011260545063447056488595457), (679055073530258548371366461149544449, 0)), ((1039524758191551784419329, 0), (119122613953929904154027739985407125559431342703247361, 0))), (((681893961837661842799653021924704911361, 162032044052416968911053464130093829849089), (462637416354298858005509592291271087897145429505505359822849, 0)), ((499931136877784968767216002324271360464405921793, 0), (525184767368310640045851929835250988484697555978944513, 0)))), ((((93087288110326446758559745, 361022234526104695804130929196870820856362238529624426414081), (365599810581285943946282911730417983095520100353, 0)), ((2438959754839113368493951487574017, 0), (58248100105970497085004310709778662817793, 0))), (((147611665370421194738572168104344584985249892532225, 0), (1077238269255995873934792006493700521721857, 0)), ((286363649261740857961699083840333924360181211766758622363649, 0), (579745504851188790111869879215379473629971480577, 0))))), (((((289383297656355291137, 91297084415985111260439686925681059699797486735458305), (75618451452208079093773406726382930624513, 0)), ((569186454390960334757228969985, 0), (165368528823756334927732511005736178729173085042838991798273, 0))), (((1181939495522123026501393068450363160195497985, 214267841490174606609724726395245686962209765844844545), (12405229337192884863463933401366529, 0)), ((508374575535730594679642546951362750689739159538499585, 0), (983531118199073615072653389392948364865263414278087730266113, 0)))), ((((1263847648427544713292213825568769, 260161040873775804506206504675650200615887613572206336933889), (12508992513915198076905338483218697494115751349452801, 0)), ((902939260624710212800064521840544722190337, 0), (607764996488705858556874796644762022146575695873, 0))), (((12259964326927110866866776217202473468949912978315018241, 0), (319486050900449339782185289318246576146891145217, 0)), ((168708016204833345492383432705, 0), (176464630694608979421301828197256335807735459267739649, 0)))))), ((((((235295954960385, 701116709946144152700160008537409649529280131859154945966081), (285454632761793871259815161364480001, 0)), ((669985745460818610225153, 0), (322826712165111152893257332525508529861804640362823681, 0))), (((277808651119047417436895675599599697921, 557960859174987372462746831678434799661155860258909120888833), (646897017710309004890225447100688512589704783950390409297921, 0)), ((685672649839771620749120653834767743926497443841, 0), (189919214767876172415105125918282645282289153790181377, 0)))), ((((475107847108549265668964353, 420430956663311797645317031469773614161839568920574343249921), (222633914503230843477736459680612741945231409153, 0)), ((9755839019356453473975802630504449, 0), (630661528307853406710478771512041013248001, 0))), (((362452406058063923714513838513638188874671380758529, 0), (80551216544565992567407178950177739243521, 0)), ((79625403312309853302582994836675764562462447492935463206913, 0), (64510480774070787772331055373892884327977451521, 0))))), (((((65716525762851373057, 924265328829869889255172913000193820878362175373049857), (50998490514279867295800669652677454462977, 0)), ((222681718121375709913674678273, 0), (182587648720925462140246898202797116789381677395039973539841, 0))), (((1350588881086010864009256937887266394733543425, 0), (9210749679546648417936740449255425, 0)), ((847290959226217657799404244918937917816231932623585281, 0), (245205416520705680892768957961602829257042256176768904855553, 0)))), ((((1251171142425262419277246645665793, 811332257902802805357300127229596870695396549835851436130305), (50499266074694688532691922024845852846615439671820289, 0)), ((586715920427478726636248821842508728238081, 0), (275679024551086186822530136517297283247758114817, 0))), (((1362388535829775195080570507136624864237059079621621841921, 0), (191793377690237899837394672090730826763539054593, 0)), ((595642587825227934082856386561, 0), (25178750207936952323716584918109126511865519116648449, 0)))))))

def pointFast (i : Fin 75) (j : Fin 10) : ℕ :=
  tableGet 7 pointFastData i.val / 1048576 ^ j.val % 1048576

private def pointFastAgreementAt (i : Fin 75) : Prop :=
  ∀ j : Fin 10, pointFast i j = pointCoordinate i j

private theorem pointFastAgreement000 : pointFastAgreementAt (0 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement001 : pointFastAgreementAt (1 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement002 : pointFastAgreementAt (2 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement003 : pointFastAgreementAt (3 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement004 : pointFastAgreementAt (4 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement005 : pointFastAgreementAt (5 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement006 : pointFastAgreementAt (6 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement007 : pointFastAgreementAt (7 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement008 : pointFastAgreementAt (8 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement009 : pointFastAgreementAt (9 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement010 : pointFastAgreementAt (10 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement011 : pointFastAgreementAt (11 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement012 : pointFastAgreementAt (12 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement013 : pointFastAgreementAt (13 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement014 : pointFastAgreementAt (14 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement015 : pointFastAgreementAt (15 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement016 : pointFastAgreementAt (16 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement017 : pointFastAgreementAt (17 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement018 : pointFastAgreementAt (18 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement019 : pointFastAgreementAt (19 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement020 : pointFastAgreementAt (20 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement021 : pointFastAgreementAt (21 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement022 : pointFastAgreementAt (22 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement023 : pointFastAgreementAt (23 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement024 : pointFastAgreementAt (24 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement025 : pointFastAgreementAt (25 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement026 : pointFastAgreementAt (26 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement027 : pointFastAgreementAt (27 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement028 : pointFastAgreementAt (28 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement029 : pointFastAgreementAt (29 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement030 : pointFastAgreementAt (30 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement031 : pointFastAgreementAt (31 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement032 : pointFastAgreementAt (32 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement033 : pointFastAgreementAt (33 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement034 : pointFastAgreementAt (34 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement035 : pointFastAgreementAt (35 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement036 : pointFastAgreementAt (36 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement037 : pointFastAgreementAt (37 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement038 : pointFastAgreementAt (38 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement039 : pointFastAgreementAt (39 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement040 : pointFastAgreementAt (40 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement041 : pointFastAgreementAt (41 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement042 : pointFastAgreementAt (42 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement043 : pointFastAgreementAt (43 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement044 : pointFastAgreementAt (44 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement045 : pointFastAgreementAt (45 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement046 : pointFastAgreementAt (46 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement047 : pointFastAgreementAt (47 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement048 : pointFastAgreementAt (48 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement049 : pointFastAgreementAt (49 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement050 : pointFastAgreementAt (50 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement051 : pointFastAgreementAt (51 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement052 : pointFastAgreementAt (52 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement053 : pointFastAgreementAt (53 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement054 : pointFastAgreementAt (54 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement055 : pointFastAgreementAt (55 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement056 : pointFastAgreementAt (56 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement057 : pointFastAgreementAt (57 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement058 : pointFastAgreementAt (58 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement059 : pointFastAgreementAt (59 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement060 : pointFastAgreementAt (60 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement061 : pointFastAgreementAt (61 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement062 : pointFastAgreementAt (62 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement063 : pointFastAgreementAt (63 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement064 : pointFastAgreementAt (64 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement065 : pointFastAgreementAt (65 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement066 : pointFastAgreementAt (66 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement067 : pointFastAgreementAt (67 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement068 : pointFastAgreementAt (68 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement069 : pointFastAgreementAt (69 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement070 : pointFastAgreementAt (70 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement071 : pointFastAgreementAt (71 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement072 : pointFastAgreementAt (72 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement073 : pointFastAgreementAt (73 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel
private theorem pointFastAgreement074 : pointFastAgreementAt (74 : Fin 75) := by unfold pointFastAgreementAt; decide +kernel

private theorem pointFastAgreement : ∀ i : Fin 75, pointFastAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne pointFastAgreement000) (finOne pointFastAgreement001)) (finSplit (finOne pointFastAgreement002) (finOne pointFastAgreement003))) (finSplit (finSplit (finOne pointFastAgreement004) (finOne pointFastAgreement005)) (finSplit (finOne pointFastAgreement006) (finSplit (finOne pointFastAgreement007) (finOne pointFastAgreement008))))) (finSplit (finSplit (finSplit (finOne pointFastAgreement009) (finOne pointFastAgreement010)) (finSplit (finOne pointFastAgreement011) (finOne pointFastAgreement012))) (finSplit (finSplit (finOne pointFastAgreement013) (finOne pointFastAgreement014)) (finSplit (finOne pointFastAgreement015) (finSplit (finOne pointFastAgreement016) (finOne pointFastAgreement017)))))) (finSplit (finSplit (finSplit (finSplit (finOne pointFastAgreement018) (finOne pointFastAgreement019)) (finSplit (finOne pointFastAgreement020) (finOne pointFastAgreement021))) (finSplit (finSplit (finOne pointFastAgreement022) (finOne pointFastAgreement023)) (finSplit (finOne pointFastAgreement024) (finSplit (finOne pointFastAgreement025) (finOne pointFastAgreement026))))) (finSplit (finSplit (finSplit (finOne pointFastAgreement027) (finOne pointFastAgreement028)) (finSplit (finOne pointFastAgreement029) (finSplit (finOne pointFastAgreement030) (finOne pointFastAgreement031)))) (finSplit (finSplit (finOne pointFastAgreement032) (finOne pointFastAgreement033)) (finSplit (finOne pointFastAgreement034) (finSplit (finOne pointFastAgreement035) (finOne pointFastAgreement036))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne pointFastAgreement037) (finOne pointFastAgreement038)) (finSplit (finOne pointFastAgreement039) (finOne pointFastAgreement040))) (finSplit (finSplit (finOne pointFastAgreement041) (finOne pointFastAgreement042)) (finSplit (finOne pointFastAgreement043) (finSplit (finOne pointFastAgreement044) (finOne pointFastAgreement045))))) (finSplit (finSplit (finSplit (finOne pointFastAgreement046) (finOne pointFastAgreement047)) (finSplit (finOne pointFastAgreement048) (finSplit (finOne pointFastAgreement049) (finOne pointFastAgreement050)))) (finSplit (finSplit (finOne pointFastAgreement051) (finOne pointFastAgreement052)) (finSplit (finOne pointFastAgreement053) (finSplit (finOne pointFastAgreement054) (finOne pointFastAgreement055)))))) (finSplit (finSplit (finSplit (finSplit (finOne pointFastAgreement056) (finOne pointFastAgreement057)) (finSplit (finOne pointFastAgreement058) (finOne pointFastAgreement059))) (finSplit (finSplit (finOne pointFastAgreement060) (finOne pointFastAgreement061)) (finSplit (finOne pointFastAgreement062) (finSplit (finOne pointFastAgreement063) (finOne pointFastAgreement064))))) (finSplit (finSplit (finSplit (finOne pointFastAgreement065) (finOne pointFastAgreement066)) (finSplit (finOne pointFastAgreement067) (finSplit (finOne pointFastAgreement068) (finOne pointFastAgreement069)))) (finSplit (finSplit (finOne pointFastAgreement070) (finOne pointFastAgreement071)) (finSplit (finOne pointFastAgreement072) (finSplit (finOne pointFastAgreement073) (finOne pointFastAgreement074))))))))


theorem pointFast_eq (i : Fin 75) (j : Fin 10) :
    pointFast i j = pointCoordinate i j := pointFastAgreement i j

private def tracePointFastData : Table ℕ 7 :=
  (((((((1, 413898821059022422017), (590295810359805163339776, 0)), ((1065151890432, 852361785884869610438657), (1104507809176749056, 0))), (((929793, 64563604258984821760), (502933032476534306242560, 0)), ((349335215895875682304, 5903367932252658860032), (859833125306369, 0)))), ((((1099511627776, 328290939672285856923648), (250347202281472, 0)), ((1021211751920560777462784, 1030657474552318182556672), (397309810926439890944, 0))), (((746471638236659713, 715964254360852074497), (32712671023333376, 0)), ((509591305037300105216, 0), (959776293888, 0))))), (((((1048576, 759120412121296203153409), (1173508072119006742446080, 0)), ((881579627057775616, 547464326103672291328), (291909348674011704328192, 0))), (((158913789953, 436819226176415166627841), (21392099163242497, 0)), ((594836864368640, 0), (717233425030841344, 0)))), ((((1152921504606846976, 790945071105), (1097630811981619397632, 0)), ((888405396291584, 698058327716790272), (355099824295082198016, 0))), (((369525177284549737971713, 627193318321684480), (795088897, 0)), ((685674142778785792, 0), (263271931420099758522369, 0)))))), ((((((1024, 154657502481106649219072), (742482574866716295168, 0)), ((484884627850240, 775297431503872), (1166424521268803350299648, 0))), (((866123777, 937325183461189746688), (584392852255931418804224, 0)), ((250285423592091197374464, 926512041639561658368), (1074729215242906007241728, 0)))), ((((1125899906842624, 998540176462446593), (634777828975346928582656, 0)), ((22549626880, 789255923817250817), (1036559443850804728954881, 0))), (((815115503757040812033, 107752744550401), (1021488708168364065792, 0)), ((1043642992714192665968640, 0), (948015071436889804243968, 0))))), (((((1073741824, 531724245404938665985), (792178130422887591444480, 0)), ((365476116960370492416, 394317602065085332717568), (917725517667480109057, 0))), (((804842511532033, 1155227608201390194688), (296868140496897, 0)), ((641762947974037504, 0), (1011465556993, 0)))), ((((1180591620717411303424, 637259347273552897), (227126059775084724224, 0)), ((410953465998606336, 573083406917698560), (387234562753869687816192, 0))), (((746587136, 17708874869313076462592), (326555093959680, 0)), ((168326540772111286272, 0), (960592292129838444052480, 0)))))))

def tracePointFast (i : Fin 90) (j : Fin 8) : ℕ :=
  tableGet 7 tracePointFastData i.val / 1024 ^ j.val % 1024

private def tracePointFastAgreementAt (i : Fin 90) : Prop :=
  ∀ j : Fin 8, tracePointFast i j = traceCoordinate i j

private theorem tracePointFastAgreement000 : tracePointFastAgreementAt (0 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement001 : tracePointFastAgreementAt (1 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement002 : tracePointFastAgreementAt (2 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement003 : tracePointFastAgreementAt (3 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement004 : tracePointFastAgreementAt (4 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement005 : tracePointFastAgreementAt (5 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement006 : tracePointFastAgreementAt (6 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement007 : tracePointFastAgreementAt (7 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement008 : tracePointFastAgreementAt (8 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement009 : tracePointFastAgreementAt (9 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement010 : tracePointFastAgreementAt (10 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement011 : tracePointFastAgreementAt (11 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement012 : tracePointFastAgreementAt (12 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement013 : tracePointFastAgreementAt (13 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement014 : tracePointFastAgreementAt (14 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement015 : tracePointFastAgreementAt (15 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement016 : tracePointFastAgreementAt (16 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement017 : tracePointFastAgreementAt (17 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement018 : tracePointFastAgreementAt (18 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement019 : tracePointFastAgreementAt (19 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement020 : tracePointFastAgreementAt (20 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement021 : tracePointFastAgreementAt (21 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement022 : tracePointFastAgreementAt (22 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement023 : tracePointFastAgreementAt (23 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement024 : tracePointFastAgreementAt (24 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement025 : tracePointFastAgreementAt (25 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement026 : tracePointFastAgreementAt (26 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement027 : tracePointFastAgreementAt (27 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement028 : tracePointFastAgreementAt (28 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement029 : tracePointFastAgreementAt (29 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement030 : tracePointFastAgreementAt (30 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement031 : tracePointFastAgreementAt (31 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement032 : tracePointFastAgreementAt (32 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement033 : tracePointFastAgreementAt (33 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement034 : tracePointFastAgreementAt (34 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement035 : tracePointFastAgreementAt (35 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement036 : tracePointFastAgreementAt (36 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement037 : tracePointFastAgreementAt (37 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement038 : tracePointFastAgreementAt (38 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement039 : tracePointFastAgreementAt (39 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement040 : tracePointFastAgreementAt (40 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement041 : tracePointFastAgreementAt (41 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement042 : tracePointFastAgreementAt (42 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement043 : tracePointFastAgreementAt (43 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement044 : tracePointFastAgreementAt (44 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement045 : tracePointFastAgreementAt (45 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement046 : tracePointFastAgreementAt (46 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement047 : tracePointFastAgreementAt (47 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement048 : tracePointFastAgreementAt (48 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement049 : tracePointFastAgreementAt (49 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement050 : tracePointFastAgreementAt (50 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement051 : tracePointFastAgreementAt (51 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement052 : tracePointFastAgreementAt (52 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement053 : tracePointFastAgreementAt (53 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement054 : tracePointFastAgreementAt (54 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement055 : tracePointFastAgreementAt (55 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement056 : tracePointFastAgreementAt (56 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement057 : tracePointFastAgreementAt (57 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement058 : tracePointFastAgreementAt (58 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement059 : tracePointFastAgreementAt (59 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement060 : tracePointFastAgreementAt (60 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement061 : tracePointFastAgreementAt (61 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement062 : tracePointFastAgreementAt (62 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement063 : tracePointFastAgreementAt (63 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement064 : tracePointFastAgreementAt (64 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement065 : tracePointFastAgreementAt (65 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement066 : tracePointFastAgreementAt (66 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement067 : tracePointFastAgreementAt (67 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement068 : tracePointFastAgreementAt (68 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement069 : tracePointFastAgreementAt (69 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement070 : tracePointFastAgreementAt (70 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement071 : tracePointFastAgreementAt (71 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement072 : tracePointFastAgreementAt (72 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement073 : tracePointFastAgreementAt (73 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement074 : tracePointFastAgreementAt (74 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement075 : tracePointFastAgreementAt (75 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement076 : tracePointFastAgreementAt (76 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement077 : tracePointFastAgreementAt (77 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement078 : tracePointFastAgreementAt (78 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement079 : tracePointFastAgreementAt (79 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement080 : tracePointFastAgreementAt (80 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement081 : tracePointFastAgreementAt (81 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement082 : tracePointFastAgreementAt (82 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement083 : tracePointFastAgreementAt (83 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement084 : tracePointFastAgreementAt (84 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement085 : tracePointFastAgreementAt (85 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement086 : tracePointFastAgreementAt (86 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement087 : tracePointFastAgreementAt (87 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement088 : tracePointFastAgreementAt (88 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel
private theorem tracePointFastAgreement089 : tracePointFastAgreementAt (89 : Fin 90) := by unfold tracePointFastAgreementAt; decide +kernel

private theorem tracePointFastAgreement : ∀ i : Fin 90, tracePointFastAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne tracePointFastAgreement000) (finOne tracePointFastAgreement001)) (finSplit (finOne tracePointFastAgreement002) (finSplit (finOne tracePointFastAgreement003) (finOne tracePointFastAgreement004)))) (finSplit (finSplit (finOne tracePointFastAgreement005) (finSplit (finOne tracePointFastAgreement006) (finOne tracePointFastAgreement007))) (finSplit (finOne tracePointFastAgreement008) (finSplit (finOne tracePointFastAgreement009) (finOne tracePointFastAgreement010))))) (finSplit (finSplit (finSplit (finOne tracePointFastAgreement011) (finOne tracePointFastAgreement012)) (finSplit (finOne tracePointFastAgreement013) (finSplit (finOne tracePointFastAgreement014) (finOne tracePointFastAgreement015)))) (finSplit (finSplit (finOne tracePointFastAgreement016) (finSplit (finOne tracePointFastAgreement017) (finOne tracePointFastAgreement018))) (finSplit (finOne tracePointFastAgreement019) (finSplit (finOne tracePointFastAgreement020) (finOne tracePointFastAgreement021)))))) (finSplit (finSplit (finSplit (finSplit (finOne tracePointFastAgreement022) (finOne tracePointFastAgreement023)) (finSplit (finOne tracePointFastAgreement024) (finSplit (finOne tracePointFastAgreement025) (finOne tracePointFastAgreement026)))) (finSplit (finSplit (finOne tracePointFastAgreement027) (finSplit (finOne tracePointFastAgreement028) (finOne tracePointFastAgreement029))) (finSplit (finOne tracePointFastAgreement030) (finSplit (finOne tracePointFastAgreement031) (finOne tracePointFastAgreement032))))) (finSplit (finSplit (finSplit (finOne tracePointFastAgreement033) (finSplit (finOne tracePointFastAgreement034) (finOne tracePointFastAgreement035))) (finSplit (finOne tracePointFastAgreement036) (finSplit (finOne tracePointFastAgreement037) (finOne tracePointFastAgreement038)))) (finSplit (finSplit (finOne tracePointFastAgreement039) (finSplit (finOne tracePointFastAgreement040) (finOne tracePointFastAgreement041))) (finSplit (finOne tracePointFastAgreement042) (finSplit (finOne tracePointFastAgreement043) (finOne tracePointFastAgreement044))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne tracePointFastAgreement045) (finOne tracePointFastAgreement046)) (finSplit (finOne tracePointFastAgreement047) (finSplit (finOne tracePointFastAgreement048) (finOne tracePointFastAgreement049)))) (finSplit (finSplit (finOne tracePointFastAgreement050) (finSplit (finOne tracePointFastAgreement051) (finOne tracePointFastAgreement052))) (finSplit (finOne tracePointFastAgreement053) (finSplit (finOne tracePointFastAgreement054) (finOne tracePointFastAgreement055))))) (finSplit (finSplit (finSplit (finOne tracePointFastAgreement056) (finOne tracePointFastAgreement057)) (finSplit (finOne tracePointFastAgreement058) (finSplit (finOne tracePointFastAgreement059) (finOne tracePointFastAgreement060)))) (finSplit (finSplit (finOne tracePointFastAgreement061) (finSplit (finOne tracePointFastAgreement062) (finOne tracePointFastAgreement063))) (finSplit (finOne tracePointFastAgreement064) (finSplit (finOne tracePointFastAgreement065) (finOne tracePointFastAgreement066)))))) (finSplit (finSplit (finSplit (finSplit (finOne tracePointFastAgreement067) (finOne tracePointFastAgreement068)) (finSplit (finOne tracePointFastAgreement069) (finSplit (finOne tracePointFastAgreement070) (finOne tracePointFastAgreement071)))) (finSplit (finSplit (finOne tracePointFastAgreement072) (finSplit (finOne tracePointFastAgreement073) (finOne tracePointFastAgreement074))) (finSplit (finOne tracePointFastAgreement075) (finSplit (finOne tracePointFastAgreement076) (finOne tracePointFastAgreement077))))) (finSplit (finSplit (finSplit (finOne tracePointFastAgreement078) (finSplit (finOne tracePointFastAgreement079) (finOne tracePointFastAgreement080))) (finSplit (finOne tracePointFastAgreement081) (finSplit (finOne tracePointFastAgreement082) (finOne tracePointFastAgreement083)))) (finSplit (finSplit (finOne tracePointFastAgreement084) (finSplit (finOne tracePointFastAgreement085) (finOne tracePointFastAgreement086))) (finSplit (finOne tracePointFastAgreement087) (finSplit (finOne tracePointFastAgreement088) (finOne tracePointFastAgreement089))))))))


theorem tracePointFast_eq (i : Fin 90) (j : Fin 8) :
    tracePointFast i j = traceCoordinate i j := tracePointFastAgreement i j

def normalTriples : Table ℕ 7 := (((((((0, 221), (830, 971)), ((710, 541), (960, 0))), (((800, 331), (550, 0)), ((720, 851), (211, 0)))), ((((400, 621), (640, 0)), ((320, 941), (880, 0))), (((310, 731), (950, 0)), ((430, 861), (611, 0))))), (((((200, 421), (440, 981)), ((910, 741), (870, 0))), (((110, 531), (750, 0)), ((920, 661), (411, 0)))), ((((600, 821), (840, 0)), ((520, 651), (990, 0))), (((510, 931), (760, 0)), ((630, 771), (811, 0)))))), ((((((100, 321), (930, 881)), ((810, 641), (770, 0))), (((900, 431), (650, 0)), ((820, 951), (311, 0)))), ((((500, 721), (740, 0)), ((420, 551), (980, 0))), (((410, 831), (660, 0)), ((530, 961), (711, 0))))), (((((300, 521), (540, 991)), ((220, 841), (970, 0))), (((210, 631), (850, 0)), ((330, 761), (511, 0)))), ((((700, 921), (940, 0)), ((620, 751), (111, 0))), (((610, 441), (860, 0)), ((730, 871), (911, 0)))))))
def traceTriples : Table ℕ 7 := (((((((0, 146), (488, 491)), ((208, 426), (465, 493))), (((72, 346), (329, 364)), ((408, 411), (417, 0)))), ((((256, 402), (73, 292)), ((464, 506), (409, 438))), (((328, 354), (209, 500)), ((416, 419), (489, 0))))), (((((128, 274), (496, 499)), ((336, 434), (281, 501))), (((200, 474), (457, 492)), ((288, 291), (361, 0)))), ((((384, 218), (201, 420)), ((280, 283), (289, 510))), (((456, 482), (337, 365)), ((360, 363), (497, 0)))))), ((((((64, 210), (432, 435)), ((272, 490), (217, 437))), (((136, 410), (393, 428)), ((472, 475), (481, 0)))), ((((320, 466), (137, 356)), ((216, 219), (473, 502))), (((392, 418), (273, 508)), ((480, 483), (433, 0))))), (((((192, 338), (504, 507)), ((400, 498), (345, 509))), (((264, 290), (145, 436)), ((352, 355), (425, 0)))), ((((448, 282), (265, 484)), ((344, 347), (353, 511))), (((144, 362), (401, 429)), ((424, 427), (505, 0)))))))


private def normalTripleAgreementAt (i : Fin 100) : Prop :=
  ∀ j : Fin 10, tripleExponentDigit 10 (tableGet 7 normalTriples i.val) j = normalExponent i j

private theorem normalTripleAgreement000 : normalTripleAgreementAt (0 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement001 : normalTripleAgreementAt (1 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement002 : normalTripleAgreementAt (2 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement003 : normalTripleAgreementAt (3 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement004 : normalTripleAgreementAt (4 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement005 : normalTripleAgreementAt (5 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement006 : normalTripleAgreementAt (6 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement007 : normalTripleAgreementAt (7 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement008 : normalTripleAgreementAt (8 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement009 : normalTripleAgreementAt (9 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement010 : normalTripleAgreementAt (10 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement011 : normalTripleAgreementAt (11 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement012 : normalTripleAgreementAt (12 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement013 : normalTripleAgreementAt (13 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement014 : normalTripleAgreementAt (14 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement015 : normalTripleAgreementAt (15 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement016 : normalTripleAgreementAt (16 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement017 : normalTripleAgreementAt (17 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement018 : normalTripleAgreementAt (18 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement019 : normalTripleAgreementAt (19 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement020 : normalTripleAgreementAt (20 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement021 : normalTripleAgreementAt (21 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement022 : normalTripleAgreementAt (22 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement023 : normalTripleAgreementAt (23 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement024 : normalTripleAgreementAt (24 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement025 : normalTripleAgreementAt (25 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement026 : normalTripleAgreementAt (26 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement027 : normalTripleAgreementAt (27 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement028 : normalTripleAgreementAt (28 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement029 : normalTripleAgreementAt (29 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement030 : normalTripleAgreementAt (30 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement031 : normalTripleAgreementAt (31 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement032 : normalTripleAgreementAt (32 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement033 : normalTripleAgreementAt (33 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement034 : normalTripleAgreementAt (34 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement035 : normalTripleAgreementAt (35 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement036 : normalTripleAgreementAt (36 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement037 : normalTripleAgreementAt (37 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement038 : normalTripleAgreementAt (38 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement039 : normalTripleAgreementAt (39 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement040 : normalTripleAgreementAt (40 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement041 : normalTripleAgreementAt (41 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement042 : normalTripleAgreementAt (42 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement043 : normalTripleAgreementAt (43 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement044 : normalTripleAgreementAt (44 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement045 : normalTripleAgreementAt (45 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement046 : normalTripleAgreementAt (46 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement047 : normalTripleAgreementAt (47 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement048 : normalTripleAgreementAt (48 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement049 : normalTripleAgreementAt (49 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement050 : normalTripleAgreementAt (50 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement051 : normalTripleAgreementAt (51 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement052 : normalTripleAgreementAt (52 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement053 : normalTripleAgreementAt (53 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement054 : normalTripleAgreementAt (54 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement055 : normalTripleAgreementAt (55 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement056 : normalTripleAgreementAt (56 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement057 : normalTripleAgreementAt (57 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement058 : normalTripleAgreementAt (58 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement059 : normalTripleAgreementAt (59 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement060 : normalTripleAgreementAt (60 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement061 : normalTripleAgreementAt (61 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement062 : normalTripleAgreementAt (62 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement063 : normalTripleAgreementAt (63 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement064 : normalTripleAgreementAt (64 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement065 : normalTripleAgreementAt (65 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement066 : normalTripleAgreementAt (66 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement067 : normalTripleAgreementAt (67 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement068 : normalTripleAgreementAt (68 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement069 : normalTripleAgreementAt (69 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement070 : normalTripleAgreementAt (70 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement071 : normalTripleAgreementAt (71 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement072 : normalTripleAgreementAt (72 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement073 : normalTripleAgreementAt (73 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement074 : normalTripleAgreementAt (74 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement075 : normalTripleAgreementAt (75 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement076 : normalTripleAgreementAt (76 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement077 : normalTripleAgreementAt (77 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement078 : normalTripleAgreementAt (78 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement079 : normalTripleAgreementAt (79 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement080 : normalTripleAgreementAt (80 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement081 : normalTripleAgreementAt (81 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement082 : normalTripleAgreementAt (82 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement083 : normalTripleAgreementAt (83 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement084 : normalTripleAgreementAt (84 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement085 : normalTripleAgreementAt (85 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement086 : normalTripleAgreementAt (86 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement087 : normalTripleAgreementAt (87 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement088 : normalTripleAgreementAt (88 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement089 : normalTripleAgreementAt (89 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement090 : normalTripleAgreementAt (90 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement091 : normalTripleAgreementAt (91 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement092 : normalTripleAgreementAt (92 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement093 : normalTripleAgreementAt (93 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement094 : normalTripleAgreementAt (94 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement095 : normalTripleAgreementAt (95 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement096 : normalTripleAgreementAt (96 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement097 : normalTripleAgreementAt (97 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement098 : normalTripleAgreementAt (98 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel
private theorem normalTripleAgreement099 : normalTripleAgreementAt (99 : Fin 100) := by unfold normalTripleAgreementAt; decide +kernel

private theorem normalTripleAgreement : ∀ i : Fin 100, normalTripleAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalTripleAgreement000) (finSplit (finOne normalTripleAgreement001) (finOne normalTripleAgreement002))) (finSplit (finOne normalTripleAgreement003) (finSplit (finOne normalTripleAgreement004) (finOne normalTripleAgreement005)))) (finSplit (finSplit (finOne normalTripleAgreement006) (finSplit (finOne normalTripleAgreement007) (finOne normalTripleAgreement008))) (finSplit (finOne normalTripleAgreement009) (finSplit (finOne normalTripleAgreement010) (finOne normalTripleAgreement011))))) (finSplit (finSplit (finSplit (finOne normalTripleAgreement012) (finSplit (finOne normalTripleAgreement013) (finOne normalTripleAgreement014))) (finSplit (finOne normalTripleAgreement015) (finSplit (finOne normalTripleAgreement016) (finOne normalTripleAgreement017)))) (finSplit (finSplit (finOne normalTripleAgreement018) (finSplit (finOne normalTripleAgreement019) (finOne normalTripleAgreement020))) (finSplit (finSplit (finOne normalTripleAgreement021) (finOne normalTripleAgreement022)) (finSplit (finOne normalTripleAgreement023) (finOne normalTripleAgreement024)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalTripleAgreement025) (finSplit (finOne normalTripleAgreement026) (finOne normalTripleAgreement027))) (finSplit (finOne normalTripleAgreement028) (finSplit (finOne normalTripleAgreement029) (finOne normalTripleAgreement030)))) (finSplit (finSplit (finOne normalTripleAgreement031) (finSplit (finOne normalTripleAgreement032) (finOne normalTripleAgreement033))) (finSplit (finOne normalTripleAgreement034) (finSplit (finOne normalTripleAgreement035) (finOne normalTripleAgreement036))))) (finSplit (finSplit (finSplit (finOne normalTripleAgreement037) (finSplit (finOne normalTripleAgreement038) (finOne normalTripleAgreement039))) (finSplit (finOne normalTripleAgreement040) (finSplit (finOne normalTripleAgreement041) (finOne normalTripleAgreement042)))) (finSplit (finSplit (finOne normalTripleAgreement043) (finSplit (finOne normalTripleAgreement044) (finOne normalTripleAgreement045))) (finSplit (finSplit (finOne normalTripleAgreement046) (finOne normalTripleAgreement047)) (finSplit (finOne normalTripleAgreement048) (finOne normalTripleAgreement049))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne normalTripleAgreement050) (finSplit (finOne normalTripleAgreement051) (finOne normalTripleAgreement052))) (finSplit (finOne normalTripleAgreement053) (finSplit (finOne normalTripleAgreement054) (finOne normalTripleAgreement055)))) (finSplit (finSplit (finOne normalTripleAgreement056) (finSplit (finOne normalTripleAgreement057) (finOne normalTripleAgreement058))) (finSplit (finOne normalTripleAgreement059) (finSplit (finOne normalTripleAgreement060) (finOne normalTripleAgreement061))))) (finSplit (finSplit (finSplit (finOne normalTripleAgreement062) (finSplit (finOne normalTripleAgreement063) (finOne normalTripleAgreement064))) (finSplit (finOne normalTripleAgreement065) (finSplit (finOne normalTripleAgreement066) (finOne normalTripleAgreement067)))) (finSplit (finSplit (finOne normalTripleAgreement068) (finSplit (finOne normalTripleAgreement069) (finOne normalTripleAgreement070))) (finSplit (finSplit (finOne normalTripleAgreement071) (finOne normalTripleAgreement072)) (finSplit (finOne normalTripleAgreement073) (finOne normalTripleAgreement074)))))) (finSplit (finSplit (finSplit (finSplit (finOne normalTripleAgreement075) (finSplit (finOne normalTripleAgreement076) (finOne normalTripleAgreement077))) (finSplit (finOne normalTripleAgreement078) (finSplit (finOne normalTripleAgreement079) (finOne normalTripleAgreement080)))) (finSplit (finSplit (finOne normalTripleAgreement081) (finSplit (finOne normalTripleAgreement082) (finOne normalTripleAgreement083))) (finSplit (finOne normalTripleAgreement084) (finSplit (finOne normalTripleAgreement085) (finOne normalTripleAgreement086))))) (finSplit (finSplit (finSplit (finOne normalTripleAgreement087) (finSplit (finOne normalTripleAgreement088) (finOne normalTripleAgreement089))) (finSplit (finOne normalTripleAgreement090) (finSplit (finOne normalTripleAgreement091) (finOne normalTripleAgreement092)))) (finSplit (finSplit (finOne normalTripleAgreement093) (finSplit (finOne normalTripleAgreement094) (finOne normalTripleAgreement095))) (finSplit (finSplit (finOne normalTripleAgreement096) (finOne normalTripleAgreement097)) (finSplit (finOne normalTripleAgreement098) (finOne normalTripleAgreement099))))))))

private def traceTripleAgreementAt (i : Fin 120) : Prop :=
  ∀ j : Fin 8, tripleExponentDigit 8 (tableGet 7 traceTriples i.val) j = traceExponent i j

private theorem traceTripleAgreement000 : traceTripleAgreementAt (0 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement001 : traceTripleAgreementAt (1 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement002 : traceTripleAgreementAt (2 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement003 : traceTripleAgreementAt (3 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement004 : traceTripleAgreementAt (4 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement005 : traceTripleAgreementAt (5 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement006 : traceTripleAgreementAt (6 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement007 : traceTripleAgreementAt (7 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement008 : traceTripleAgreementAt (8 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement009 : traceTripleAgreementAt (9 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement010 : traceTripleAgreementAt (10 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement011 : traceTripleAgreementAt (11 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement012 : traceTripleAgreementAt (12 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement013 : traceTripleAgreementAt (13 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement014 : traceTripleAgreementAt (14 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement015 : traceTripleAgreementAt (15 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement016 : traceTripleAgreementAt (16 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement017 : traceTripleAgreementAt (17 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement018 : traceTripleAgreementAt (18 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement019 : traceTripleAgreementAt (19 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement020 : traceTripleAgreementAt (20 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement021 : traceTripleAgreementAt (21 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement022 : traceTripleAgreementAt (22 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement023 : traceTripleAgreementAt (23 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement024 : traceTripleAgreementAt (24 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement025 : traceTripleAgreementAt (25 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement026 : traceTripleAgreementAt (26 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement027 : traceTripleAgreementAt (27 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement028 : traceTripleAgreementAt (28 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement029 : traceTripleAgreementAt (29 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement030 : traceTripleAgreementAt (30 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement031 : traceTripleAgreementAt (31 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement032 : traceTripleAgreementAt (32 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement033 : traceTripleAgreementAt (33 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement034 : traceTripleAgreementAt (34 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement035 : traceTripleAgreementAt (35 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement036 : traceTripleAgreementAt (36 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement037 : traceTripleAgreementAt (37 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement038 : traceTripleAgreementAt (38 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement039 : traceTripleAgreementAt (39 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement040 : traceTripleAgreementAt (40 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement041 : traceTripleAgreementAt (41 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement042 : traceTripleAgreementAt (42 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement043 : traceTripleAgreementAt (43 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement044 : traceTripleAgreementAt (44 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement045 : traceTripleAgreementAt (45 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement046 : traceTripleAgreementAt (46 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement047 : traceTripleAgreementAt (47 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement048 : traceTripleAgreementAt (48 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement049 : traceTripleAgreementAt (49 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement050 : traceTripleAgreementAt (50 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement051 : traceTripleAgreementAt (51 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement052 : traceTripleAgreementAt (52 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement053 : traceTripleAgreementAt (53 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement054 : traceTripleAgreementAt (54 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement055 : traceTripleAgreementAt (55 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement056 : traceTripleAgreementAt (56 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement057 : traceTripleAgreementAt (57 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement058 : traceTripleAgreementAt (58 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement059 : traceTripleAgreementAt (59 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement060 : traceTripleAgreementAt (60 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement061 : traceTripleAgreementAt (61 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement062 : traceTripleAgreementAt (62 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement063 : traceTripleAgreementAt (63 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement064 : traceTripleAgreementAt (64 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement065 : traceTripleAgreementAt (65 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement066 : traceTripleAgreementAt (66 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement067 : traceTripleAgreementAt (67 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement068 : traceTripleAgreementAt (68 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement069 : traceTripleAgreementAt (69 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement070 : traceTripleAgreementAt (70 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement071 : traceTripleAgreementAt (71 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement072 : traceTripleAgreementAt (72 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement073 : traceTripleAgreementAt (73 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement074 : traceTripleAgreementAt (74 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement075 : traceTripleAgreementAt (75 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement076 : traceTripleAgreementAt (76 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement077 : traceTripleAgreementAt (77 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement078 : traceTripleAgreementAt (78 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement079 : traceTripleAgreementAt (79 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement080 : traceTripleAgreementAt (80 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement081 : traceTripleAgreementAt (81 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement082 : traceTripleAgreementAt (82 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement083 : traceTripleAgreementAt (83 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement084 : traceTripleAgreementAt (84 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement085 : traceTripleAgreementAt (85 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement086 : traceTripleAgreementAt (86 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement087 : traceTripleAgreementAt (87 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement088 : traceTripleAgreementAt (88 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement089 : traceTripleAgreementAt (89 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement090 : traceTripleAgreementAt (90 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement091 : traceTripleAgreementAt (91 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement092 : traceTripleAgreementAt (92 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement093 : traceTripleAgreementAt (93 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement094 : traceTripleAgreementAt (94 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement095 : traceTripleAgreementAt (95 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement096 : traceTripleAgreementAt (96 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement097 : traceTripleAgreementAt (97 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement098 : traceTripleAgreementAt (98 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement099 : traceTripleAgreementAt (99 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement100 : traceTripleAgreementAt (100 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement101 : traceTripleAgreementAt (101 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement102 : traceTripleAgreementAt (102 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement103 : traceTripleAgreementAt (103 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement104 : traceTripleAgreementAt (104 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement105 : traceTripleAgreementAt (105 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement106 : traceTripleAgreementAt (106 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement107 : traceTripleAgreementAt (107 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement108 : traceTripleAgreementAt (108 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement109 : traceTripleAgreementAt (109 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement110 : traceTripleAgreementAt (110 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement111 : traceTripleAgreementAt (111 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement112 : traceTripleAgreementAt (112 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement113 : traceTripleAgreementAt (113 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement114 : traceTripleAgreementAt (114 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement115 : traceTripleAgreementAt (115 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement116 : traceTripleAgreementAt (116 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement117 : traceTripleAgreementAt (117 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement118 : traceTripleAgreementAt (118 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel
private theorem traceTripleAgreement119 : traceTripleAgreementAt (119 : Fin 120) := by unfold traceTripleAgreementAt; decide +kernel

private theorem traceTripleAgreement : ∀ i : Fin 120, traceTripleAgreementAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne traceTripleAgreement000) (finSplit (finOne traceTripleAgreement001) (finOne traceTripleAgreement002))) (finSplit (finSplit (finOne traceTripleAgreement003) (finOne traceTripleAgreement004)) (finSplit (finOne traceTripleAgreement005) (finOne traceTripleAgreement006)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement007) (finOne traceTripleAgreement008)) (finSplit (finOne traceTripleAgreement009) (finOne traceTripleAgreement010))) (finSplit (finSplit (finOne traceTripleAgreement011) (finOne traceTripleAgreement012)) (finSplit (finOne traceTripleAgreement013) (finOne traceTripleAgreement014))))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement015) (finSplit (finOne traceTripleAgreement016) (finOne traceTripleAgreement017))) (finSplit (finSplit (finOne traceTripleAgreement018) (finOne traceTripleAgreement019)) (finSplit (finOne traceTripleAgreement020) (finOne traceTripleAgreement021)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement022) (finOne traceTripleAgreement023)) (finSplit (finOne traceTripleAgreement024) (finOne traceTripleAgreement025))) (finSplit (finSplit (finOne traceTripleAgreement026) (finOne traceTripleAgreement027)) (finSplit (finOne traceTripleAgreement028) (finOne traceTripleAgreement029)))))) (finSplit (finSplit (finSplit (finSplit (finOne traceTripleAgreement030) (finSplit (finOne traceTripleAgreement031) (finOne traceTripleAgreement032))) (finSplit (finSplit (finOne traceTripleAgreement033) (finOne traceTripleAgreement034)) (finSplit (finOne traceTripleAgreement035) (finOne traceTripleAgreement036)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement037) (finOne traceTripleAgreement038)) (finSplit (finOne traceTripleAgreement039) (finOne traceTripleAgreement040))) (finSplit (finSplit (finOne traceTripleAgreement041) (finOne traceTripleAgreement042)) (finSplit (finOne traceTripleAgreement043) (finOne traceTripleAgreement044))))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement045) (finSplit (finOne traceTripleAgreement046) (finOne traceTripleAgreement047))) (finSplit (finSplit (finOne traceTripleAgreement048) (finOne traceTripleAgreement049)) (finSplit (finOne traceTripleAgreement050) (finOne traceTripleAgreement051)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement052) (finOne traceTripleAgreement053)) (finSplit (finOne traceTripleAgreement054) (finOne traceTripleAgreement055))) (finSplit (finSplit (finOne traceTripleAgreement056) (finOne traceTripleAgreement057)) (finSplit (finOne traceTripleAgreement058) (finOne traceTripleAgreement059))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne traceTripleAgreement060) (finSplit (finOne traceTripleAgreement061) (finOne traceTripleAgreement062))) (finSplit (finSplit (finOne traceTripleAgreement063) (finOne traceTripleAgreement064)) (finSplit (finOne traceTripleAgreement065) (finOne traceTripleAgreement066)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement067) (finOne traceTripleAgreement068)) (finSplit (finOne traceTripleAgreement069) (finOne traceTripleAgreement070))) (finSplit (finSplit (finOne traceTripleAgreement071) (finOne traceTripleAgreement072)) (finSplit (finOne traceTripleAgreement073) (finOne traceTripleAgreement074))))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement075) (finSplit (finOne traceTripleAgreement076) (finOne traceTripleAgreement077))) (finSplit (finSplit (finOne traceTripleAgreement078) (finOne traceTripleAgreement079)) (finSplit (finOne traceTripleAgreement080) (finOne traceTripleAgreement081)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement082) (finOne traceTripleAgreement083)) (finSplit (finOne traceTripleAgreement084) (finOne traceTripleAgreement085))) (finSplit (finSplit (finOne traceTripleAgreement086) (finOne traceTripleAgreement087)) (finSplit (finOne traceTripleAgreement088) (finOne traceTripleAgreement089)))))) (finSplit (finSplit (finSplit (finSplit (finOne traceTripleAgreement090) (finSplit (finOne traceTripleAgreement091) (finOne traceTripleAgreement092))) (finSplit (finSplit (finOne traceTripleAgreement093) (finOne traceTripleAgreement094)) (finSplit (finOne traceTripleAgreement095) (finOne traceTripleAgreement096)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement097) (finOne traceTripleAgreement098)) (finSplit (finOne traceTripleAgreement099) (finOne traceTripleAgreement100))) (finSplit (finSplit (finOne traceTripleAgreement101) (finOne traceTripleAgreement102)) (finSplit (finOne traceTripleAgreement103) (finOne traceTripleAgreement104))))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement105) (finSplit (finOne traceTripleAgreement106) (finOne traceTripleAgreement107))) (finSplit (finSplit (finOne traceTripleAgreement108) (finOne traceTripleAgreement109)) (finSplit (finOne traceTripleAgreement110) (finOne traceTripleAgreement111)))) (finSplit (finSplit (finSplit (finOne traceTripleAgreement112) (finOne traceTripleAgreement113)) (finSplit (finOne traceTripleAgreement114) (finOne traceTripleAgreement115))) (finSplit (finSplit (finOne traceTripleAgreement116) (finOne traceTripleAgreement117)) (finSplit (finOne traceTripleAgreement118) (finOne traceTripleAgreement119))))))))

theorem normalTriple_exp (i : Fin 100) :
    tripleExponent 10 (tableGet 7 normalTriples i.val) = normalExponent i :=
  Finsupp.ext fun j => (tripleExponent_apply _ _ _).trans (normalTripleAgreement i j)

theorem traceTriple_exp (i : Fin 120) :
    tripleExponent 8 (tableGet 7 traceTriples i.val) = traceExponent i :=
  Finsupp.ext fun j => (tripleExponent_apply _ _ _).trans (traceTripleAgreement i j)

end IdealGeneration.CubicTen
