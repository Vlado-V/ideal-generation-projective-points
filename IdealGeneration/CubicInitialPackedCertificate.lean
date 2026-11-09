module

public import IdealGeneration.CubicInitialCert.Checks000
public import IdealGeneration.CubicInitialCert.Checks032
public import IdealGeneration.CubicInitialCert.Checks064
public import IdealGeneration.CubicInitialCert.Checks096
public import IdealGeneration.CubicInitialCert.Checks128
public import IdealGeneration.CubicInitialCert.Checks160
public import IdealGeneration.CubicInitialCert.Checks192
public import IdealGeneration.CubicInitialCert.Checks224
public import IdealGeneration.CubicInitialCert.Checks256
public import IdealGeneration.CubicInitialCert.Checks288
public import IdealGeneration.CubicInitialCert.Checks320
public import IdealGeneration.CubicInitialCert.Checks352
public import IdealGeneration.CubicInitialCert.Checks384
public import IdealGeneration.CubicInitialCert.Checks416
public import IdealGeneration.CubicInitialCert.Checks448
public import IdealGeneration.CubicInitialCert.Checks480
public import IdealGeneration.CubicInitialCert.Checks512
public import IdealGeneration.CertifiedPackedBounds
public import IdealGeneration.CertifiedLowerUpperRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.List.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedRank.C2.PackedCertificate

private instance : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

/-- Bundle a checked row so finite index conversion does not unfold its arithmetic. -/
private structure PackedRowCertificate (i : Fin 542) : Prop where
  upperEncoding : packedUpper i = packSparse (2 ^ 40) (upperRows i)
  productIdentity : packedProduct (lowerRows i) packedUpper =
    packSparse (2 ^ 40) (targetRows i) + 1009 * Nat.ofDigits (2 ^ 40) (quotientRows i)
  rowFacts : PackedRowFacts i

private theorem forall_fin_of_rows {n : Nat} [NeZero n] {P : Fin n → Prop}
    (h : List.Forall (fun j => P (Fin.ofNat n j)) (List.range n)) : ∀ i, P i := by
  intro i
  have hi : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hi ▸ (List.forall_iff_forall_mem.mp h i.val (List.mem_range.mpr i.isLt))

private theorem checked000 : PackedRowCertificate 0 :=
  ⟨upper000, packed000, rowFacts000⟩

private theorem checked001 : PackedRowCertificate 1 :=
  ⟨upper001, packed001, rowFacts001⟩

private theorem checked002 : PackedRowCertificate 2 :=
  ⟨upper002, packed002, rowFacts002⟩

private theorem checked003 : PackedRowCertificate 3 :=
  ⟨upper003, packed003, rowFacts003⟩

private theorem checked004 : PackedRowCertificate 4 :=
  ⟨upper004, packed004, rowFacts004⟩

private theorem checked005 : PackedRowCertificate 5 :=
  ⟨upper005, packed005, rowFacts005⟩

private theorem checked006 : PackedRowCertificate 6 :=
  ⟨upper006, packed006, rowFacts006⟩

private theorem checked007 : PackedRowCertificate 7 :=
  ⟨upper007, packed007, rowFacts007⟩

private theorem checked008 : PackedRowCertificate 8 :=
  ⟨upper008, packed008, rowFacts008⟩

private theorem checked009 : PackedRowCertificate 9 :=
  ⟨upper009, packed009, rowFacts009⟩

private theorem checked010 : PackedRowCertificate 10 :=
  ⟨upper010, packed010, rowFacts010⟩

private theorem checked011 : PackedRowCertificate 11 :=
  ⟨upper011, packed011, rowFacts011⟩

private theorem checked012 : PackedRowCertificate 12 :=
  ⟨upper012, packed012, rowFacts012⟩

private theorem checked013 : PackedRowCertificate 13 :=
  ⟨upper013, packed013, rowFacts013⟩

private theorem checked014 : PackedRowCertificate 14 :=
  ⟨upper014, packed014, rowFacts014⟩

private theorem checked015 : PackedRowCertificate 15 :=
  ⟨upper015, packed015, rowFacts015⟩

private theorem checked016 : PackedRowCertificate 16 :=
  ⟨upper016, packed016, rowFacts016⟩

private theorem checked017 : PackedRowCertificate 17 :=
  ⟨upper017, packed017, rowFacts017⟩

private theorem checked018 : PackedRowCertificate 18 :=
  ⟨upper018, packed018, rowFacts018⟩

private theorem checked019 : PackedRowCertificate 19 :=
  ⟨upper019, packed019, rowFacts019⟩

private theorem checked020 : PackedRowCertificate 20 :=
  ⟨upper020, packed020, rowFacts020⟩

private theorem checked021 : PackedRowCertificate 21 :=
  ⟨upper021, packed021, rowFacts021⟩

private theorem checked022 : PackedRowCertificate 22 :=
  ⟨upper022, packed022, rowFacts022⟩

private theorem checked023 : PackedRowCertificate 23 :=
  ⟨upper023, packed023, rowFacts023⟩

private theorem checked024 : PackedRowCertificate 24 :=
  ⟨upper024, packed024, rowFacts024⟩

private theorem checked025 : PackedRowCertificate 25 :=
  ⟨upper025, packed025, rowFacts025⟩

private theorem checked026 : PackedRowCertificate 26 :=
  ⟨upper026, packed026, rowFacts026⟩

private theorem checked027 : PackedRowCertificate 27 :=
  ⟨upper027, packed027, rowFacts027⟩

private theorem checked028 : PackedRowCertificate 28 :=
  ⟨upper028, packed028, rowFacts028⟩

private theorem checked029 : PackedRowCertificate 29 :=
  ⟨upper029, packed029, rowFacts029⟩

private theorem checked030 : PackedRowCertificate 30 :=
  ⟨upper030, packed030, rowFacts030⟩

private theorem checked031 : PackedRowCertificate 31 :=
  ⟨upper031, packed031, rowFacts031⟩

private theorem checked032 : PackedRowCertificate 32 :=
  ⟨upper032, packed032, rowFacts032⟩

private theorem checked033 : PackedRowCertificate 33 :=
  ⟨upper033, packed033, rowFacts033⟩

private theorem checked034 : PackedRowCertificate 34 :=
  ⟨upper034, packed034, rowFacts034⟩

private theorem checked035 : PackedRowCertificate 35 :=
  ⟨upper035, packed035, rowFacts035⟩

private theorem checked036 : PackedRowCertificate 36 :=
  ⟨upper036, packed036, rowFacts036⟩

private theorem checked037 : PackedRowCertificate 37 :=
  ⟨upper037, packed037, rowFacts037⟩

private theorem checked038 : PackedRowCertificate 38 :=
  ⟨upper038, packed038, rowFacts038⟩

private theorem checked039 : PackedRowCertificate 39 :=
  ⟨upper039, packed039, rowFacts039⟩

private theorem checked040 : PackedRowCertificate 40 :=
  ⟨upper040, packed040, rowFacts040⟩

private theorem checked041 : PackedRowCertificate 41 :=
  ⟨upper041, packed041, rowFacts041⟩

private theorem checked042 : PackedRowCertificate 42 :=
  ⟨upper042, packed042, rowFacts042⟩

private theorem checked043 : PackedRowCertificate 43 :=
  ⟨upper043, packed043, rowFacts043⟩

private theorem checked044 : PackedRowCertificate 44 :=
  ⟨upper044, packed044, rowFacts044⟩

private theorem checked045 : PackedRowCertificate 45 :=
  ⟨upper045, packed045, rowFacts045⟩

private theorem checked046 : PackedRowCertificate 46 :=
  ⟨upper046, packed046, rowFacts046⟩

private theorem checked047 : PackedRowCertificate 47 :=
  ⟨upper047, packed047, rowFacts047⟩

private theorem checked048 : PackedRowCertificate 48 :=
  ⟨upper048, packed048, rowFacts048⟩

private theorem checked049 : PackedRowCertificate 49 :=
  ⟨upper049, packed049, rowFacts049⟩

private theorem checked050 : PackedRowCertificate 50 :=
  ⟨upper050, packed050, rowFacts050⟩

private theorem checked051 : PackedRowCertificate 51 :=
  ⟨upper051, packed051, rowFacts051⟩

private theorem checked052 : PackedRowCertificate 52 :=
  ⟨upper052, packed052, rowFacts052⟩

private theorem checked053 : PackedRowCertificate 53 :=
  ⟨upper053, packed053, rowFacts053⟩

private theorem checked054 : PackedRowCertificate 54 :=
  ⟨upper054, packed054, rowFacts054⟩

private theorem checked055 : PackedRowCertificate 55 :=
  ⟨upper055, packed055, rowFacts055⟩

private theorem checked056 : PackedRowCertificate 56 :=
  ⟨upper056, packed056, rowFacts056⟩

private theorem checked057 : PackedRowCertificate 57 :=
  ⟨upper057, packed057, rowFacts057⟩

private theorem checked058 : PackedRowCertificate 58 :=
  ⟨upper058, packed058, rowFacts058⟩

private theorem checked059 : PackedRowCertificate 59 :=
  ⟨upper059, packed059, rowFacts059⟩

private theorem checked060 : PackedRowCertificate 60 :=
  ⟨upper060, packed060, rowFacts060⟩

private theorem checked061 : PackedRowCertificate 61 :=
  ⟨upper061, packed061, rowFacts061⟩

private theorem checked062 : PackedRowCertificate 62 :=
  ⟨upper062, packed062, rowFacts062⟩

private theorem checked063 : PackedRowCertificate 63 :=
  ⟨upper063, packed063, rowFacts063⟩

private theorem checked064 : PackedRowCertificate 64 :=
  ⟨upper064, packed064, rowFacts064⟩

private theorem checked065 : PackedRowCertificate 65 :=
  ⟨upper065, packed065, rowFacts065⟩

private theorem checked066 : PackedRowCertificate 66 :=
  ⟨upper066, packed066, rowFacts066⟩

private theorem checked067 : PackedRowCertificate 67 :=
  ⟨upper067, packed067, rowFacts067⟩

private theorem checked068 : PackedRowCertificate 68 :=
  ⟨upper068, packed068, rowFacts068⟩

private theorem checked069 : PackedRowCertificate 69 :=
  ⟨upper069, packed069, rowFacts069⟩

private theorem checked070 : PackedRowCertificate 70 :=
  ⟨upper070, packed070, rowFacts070⟩

private theorem checked071 : PackedRowCertificate 71 :=
  ⟨upper071, packed071, rowFacts071⟩

private theorem checked072 : PackedRowCertificate 72 :=
  ⟨upper072, packed072, rowFacts072⟩

private theorem checked073 : PackedRowCertificate 73 :=
  ⟨upper073, packed073, rowFacts073⟩

private theorem checked074 : PackedRowCertificate 74 :=
  ⟨upper074, packed074, rowFacts074⟩

private theorem checked075 : PackedRowCertificate 75 :=
  ⟨upper075, packed075, rowFacts075⟩

private theorem checked076 : PackedRowCertificate 76 :=
  ⟨upper076, packed076, rowFacts076⟩

private theorem checked077 : PackedRowCertificate 77 :=
  ⟨upper077, packed077, rowFacts077⟩

private theorem checked078 : PackedRowCertificate 78 :=
  ⟨upper078, packed078, rowFacts078⟩

private theorem checked079 : PackedRowCertificate 79 :=
  ⟨upper079, packed079, rowFacts079⟩

private theorem checked080 : PackedRowCertificate 80 :=
  ⟨upper080, packed080, rowFacts080⟩

private theorem checked081 : PackedRowCertificate 81 :=
  ⟨upper081, packed081, rowFacts081⟩

private theorem checked082 : PackedRowCertificate 82 :=
  ⟨upper082, packed082, rowFacts082⟩

private theorem checked083 : PackedRowCertificate 83 :=
  ⟨upper083, packed083, rowFacts083⟩

private theorem checked084 : PackedRowCertificate 84 :=
  ⟨upper084, packed084, rowFacts084⟩

private theorem checked085 : PackedRowCertificate 85 :=
  ⟨upper085, packed085, rowFacts085⟩

private theorem checked086 : PackedRowCertificate 86 :=
  ⟨upper086, packed086, rowFacts086⟩

private theorem checked087 : PackedRowCertificate 87 :=
  ⟨upper087, packed087, rowFacts087⟩

private theorem checked088 : PackedRowCertificate 88 :=
  ⟨upper088, packed088, rowFacts088⟩

private theorem checked089 : PackedRowCertificate 89 :=
  ⟨upper089, packed089, rowFacts089⟩

private theorem checked090 : PackedRowCertificate 90 :=
  ⟨upper090, packed090, rowFacts090⟩

private theorem checked091 : PackedRowCertificate 91 :=
  ⟨upper091, packed091, rowFacts091⟩

private theorem checked092 : PackedRowCertificate 92 :=
  ⟨upper092, packed092, rowFacts092⟩

private theorem checked093 : PackedRowCertificate 93 :=
  ⟨upper093, packed093, rowFacts093⟩

private theorem checked094 : PackedRowCertificate 94 :=
  ⟨upper094, packed094, rowFacts094⟩

private theorem checked095 : PackedRowCertificate 95 :=
  ⟨upper095, packed095, rowFacts095⟩

private theorem checked096 : PackedRowCertificate 96 :=
  ⟨upper096, packed096, rowFacts096⟩

private theorem checked097 : PackedRowCertificate 97 :=
  ⟨upper097, packed097, rowFacts097⟩

private theorem checked098 : PackedRowCertificate 98 :=
  ⟨upper098, packed098, rowFacts098⟩

private theorem checked099 : PackedRowCertificate 99 :=
  ⟨upper099, packed099, rowFacts099⟩

private theorem checked100 : PackedRowCertificate 100 :=
  ⟨upper100, packed100, rowFacts100⟩

private theorem checked101 : PackedRowCertificate 101 :=
  ⟨upper101, packed101, rowFacts101⟩

private theorem checked102 : PackedRowCertificate 102 :=
  ⟨upper102, packed102, rowFacts102⟩

private theorem checked103 : PackedRowCertificate 103 :=
  ⟨upper103, packed103, rowFacts103⟩

private theorem checked104 : PackedRowCertificate 104 :=
  ⟨upper104, packed104, rowFacts104⟩

private theorem checked105 : PackedRowCertificate 105 :=
  ⟨upper105, packed105, rowFacts105⟩

private theorem checked106 : PackedRowCertificate 106 :=
  ⟨upper106, packed106, rowFacts106⟩

private theorem checked107 : PackedRowCertificate 107 :=
  ⟨upper107, packed107, rowFacts107⟩

private theorem checked108 : PackedRowCertificate 108 :=
  ⟨upper108, packed108, rowFacts108⟩

private theorem checked109 : PackedRowCertificate 109 :=
  ⟨upper109, packed109, rowFacts109⟩

private theorem checked110 : PackedRowCertificate 110 :=
  ⟨upper110, packed110, rowFacts110⟩

private theorem checked111 : PackedRowCertificate 111 :=
  ⟨upper111, packed111, rowFacts111⟩

private theorem checked112 : PackedRowCertificate 112 :=
  ⟨upper112, packed112, rowFacts112⟩

private theorem checked113 : PackedRowCertificate 113 :=
  ⟨upper113, packed113, rowFacts113⟩

private theorem checked114 : PackedRowCertificate 114 :=
  ⟨upper114, packed114, rowFacts114⟩

private theorem checked115 : PackedRowCertificate 115 :=
  ⟨upper115, packed115, rowFacts115⟩

private theorem checked116 : PackedRowCertificate 116 :=
  ⟨upper116, packed116, rowFacts116⟩

private theorem checked117 : PackedRowCertificate 117 :=
  ⟨upper117, packed117, rowFacts117⟩

private theorem checked118 : PackedRowCertificate 118 :=
  ⟨upper118, packed118, rowFacts118⟩

private theorem checked119 : PackedRowCertificate 119 :=
  ⟨upper119, packed119, rowFacts119⟩

private theorem checked120 : PackedRowCertificate 120 :=
  ⟨upper120, packed120, rowFacts120⟩

private theorem checked121 : PackedRowCertificate 121 :=
  ⟨upper121, packed121, rowFacts121⟩

private theorem checked122 : PackedRowCertificate 122 :=
  ⟨upper122, packed122, rowFacts122⟩

private theorem checked123 : PackedRowCertificate 123 :=
  ⟨upper123, packed123, rowFacts123⟩

private theorem checked124 : PackedRowCertificate 124 :=
  ⟨upper124, packed124, rowFacts124⟩

private theorem checked125 : PackedRowCertificate 125 :=
  ⟨upper125, packed125, rowFacts125⟩

private theorem checked126 : PackedRowCertificate 126 :=
  ⟨upper126, packed126, rowFacts126⟩

private theorem checked127 : PackedRowCertificate 127 :=
  ⟨upper127, packed127, rowFacts127⟩

private theorem checked128 : PackedRowCertificate 128 :=
  ⟨upper128, packed128, rowFacts128⟩

private theorem checked129 : PackedRowCertificate 129 :=
  ⟨upper129, packed129, rowFacts129⟩

private theorem checked130 : PackedRowCertificate 130 :=
  ⟨upper130, packed130, rowFacts130⟩

private theorem checked131 : PackedRowCertificate 131 :=
  ⟨upper131, packed131, rowFacts131⟩

private theorem checked132 : PackedRowCertificate 132 :=
  ⟨upper132, packed132, rowFacts132⟩

private theorem checked133 : PackedRowCertificate 133 :=
  ⟨upper133, packed133, rowFacts133⟩

private theorem checked134 : PackedRowCertificate 134 :=
  ⟨upper134, packed134, rowFacts134⟩

private theorem checked135 : PackedRowCertificate 135 :=
  ⟨upper135, packed135, rowFacts135⟩

private theorem checked136 : PackedRowCertificate 136 :=
  ⟨upper136, packed136, rowFacts136⟩

private theorem checked137 : PackedRowCertificate 137 :=
  ⟨upper137, packed137, rowFacts137⟩

private theorem checked138 : PackedRowCertificate 138 :=
  ⟨upper138, packed138, rowFacts138⟩

private theorem checked139 : PackedRowCertificate 139 :=
  ⟨upper139, packed139, rowFacts139⟩

private theorem checked140 : PackedRowCertificate 140 :=
  ⟨upper140, packed140, rowFacts140⟩

private theorem checked141 : PackedRowCertificate 141 :=
  ⟨upper141, packed141, rowFacts141⟩

private theorem checked142 : PackedRowCertificate 142 :=
  ⟨upper142, packed142, rowFacts142⟩

private theorem checked143 : PackedRowCertificate 143 :=
  ⟨upper143, packed143, rowFacts143⟩

private theorem checked144 : PackedRowCertificate 144 :=
  ⟨upper144, packed144, rowFacts144⟩

private theorem checked145 : PackedRowCertificate 145 :=
  ⟨upper145, packed145, rowFacts145⟩

private theorem checked146 : PackedRowCertificate 146 :=
  ⟨upper146, packed146, rowFacts146⟩

private theorem checked147 : PackedRowCertificate 147 :=
  ⟨upper147, packed147, rowFacts147⟩

private theorem checked148 : PackedRowCertificate 148 :=
  ⟨upper148, packed148, rowFacts148⟩

private theorem checked149 : PackedRowCertificate 149 :=
  ⟨upper149, packed149, rowFacts149⟩

private theorem checked150 : PackedRowCertificate 150 :=
  ⟨upper150, packed150, rowFacts150⟩

private theorem checked151 : PackedRowCertificate 151 :=
  ⟨upper151, packed151, rowFacts151⟩

private theorem checked152 : PackedRowCertificate 152 :=
  ⟨upper152, packed152, rowFacts152⟩

private theorem checked153 : PackedRowCertificate 153 :=
  ⟨upper153, packed153, rowFacts153⟩

private theorem checked154 : PackedRowCertificate 154 :=
  ⟨upper154, packed154, rowFacts154⟩

private theorem checked155 : PackedRowCertificate 155 :=
  ⟨upper155, packed155, rowFacts155⟩

private theorem checked156 : PackedRowCertificate 156 :=
  ⟨upper156, packed156, rowFacts156⟩

private theorem checked157 : PackedRowCertificate 157 :=
  ⟨upper157, packed157, rowFacts157⟩

private theorem checked158 : PackedRowCertificate 158 :=
  ⟨upper158, packed158, rowFacts158⟩

private theorem checked159 : PackedRowCertificate 159 :=
  ⟨upper159, packed159, rowFacts159⟩

private theorem checked160 : PackedRowCertificate 160 :=
  ⟨upper160, packed160, rowFacts160⟩

private theorem checked161 : PackedRowCertificate 161 :=
  ⟨upper161, packed161, rowFacts161⟩

private theorem checked162 : PackedRowCertificate 162 :=
  ⟨upper162, packed162, rowFacts162⟩

private theorem checked163 : PackedRowCertificate 163 :=
  ⟨upper163, packed163, rowFacts163⟩

private theorem checked164 : PackedRowCertificate 164 :=
  ⟨upper164, packed164, rowFacts164⟩

private theorem checked165 : PackedRowCertificate 165 :=
  ⟨upper165, packed165, rowFacts165⟩

private theorem checked166 : PackedRowCertificate 166 :=
  ⟨upper166, packed166, rowFacts166⟩

private theorem checked167 : PackedRowCertificate 167 :=
  ⟨upper167, packed167, rowFacts167⟩

private theorem checked168 : PackedRowCertificate 168 :=
  ⟨upper168, packed168, rowFacts168⟩

private theorem checked169 : PackedRowCertificate 169 :=
  ⟨upper169, packed169, rowFacts169⟩

private theorem checked170 : PackedRowCertificate 170 :=
  ⟨upper170, packed170, rowFacts170⟩

private theorem checked171 : PackedRowCertificate 171 :=
  ⟨upper171, packed171, rowFacts171⟩

private theorem checked172 : PackedRowCertificate 172 :=
  ⟨upper172, packed172, rowFacts172⟩

private theorem checked173 : PackedRowCertificate 173 :=
  ⟨upper173, packed173, rowFacts173⟩

private theorem checked174 : PackedRowCertificate 174 :=
  ⟨upper174, packed174, rowFacts174⟩

private theorem checked175 : PackedRowCertificate 175 :=
  ⟨upper175, packed175, rowFacts175⟩

private theorem checked176 : PackedRowCertificate 176 :=
  ⟨upper176, packed176, rowFacts176⟩

private theorem checked177 : PackedRowCertificate 177 :=
  ⟨upper177, packed177, rowFacts177⟩

private theorem checked178 : PackedRowCertificate 178 :=
  ⟨upper178, packed178, rowFacts178⟩

private theorem checked179 : PackedRowCertificate 179 :=
  ⟨upper179, packed179, rowFacts179⟩

private theorem checked180 : PackedRowCertificate 180 :=
  ⟨upper180, packed180, rowFacts180⟩

private theorem checked181 : PackedRowCertificate 181 :=
  ⟨upper181, packed181, rowFacts181⟩

private theorem checked182 : PackedRowCertificate 182 :=
  ⟨upper182, packed182, rowFacts182⟩

private theorem checked183 : PackedRowCertificate 183 :=
  ⟨upper183, packed183, rowFacts183⟩

private theorem checked184 : PackedRowCertificate 184 :=
  ⟨upper184, packed184, rowFacts184⟩

private theorem checked185 : PackedRowCertificate 185 :=
  ⟨upper185, packed185, rowFacts185⟩

private theorem checked186 : PackedRowCertificate 186 :=
  ⟨upper186, packed186, rowFacts186⟩

private theorem checked187 : PackedRowCertificate 187 :=
  ⟨upper187, packed187, rowFacts187⟩

private theorem checked188 : PackedRowCertificate 188 :=
  ⟨upper188, packed188, rowFacts188⟩

private theorem checked189 : PackedRowCertificate 189 :=
  ⟨upper189, packed189, rowFacts189⟩

private theorem checked190 : PackedRowCertificate 190 :=
  ⟨upper190, packed190, rowFacts190⟩

private theorem checked191 : PackedRowCertificate 191 :=
  ⟨upper191, packed191, rowFacts191⟩

private theorem checked192 : PackedRowCertificate 192 :=
  ⟨upper192, packed192, rowFacts192⟩

private theorem checked193 : PackedRowCertificate 193 :=
  ⟨upper193, packed193, rowFacts193⟩

private theorem checked194 : PackedRowCertificate 194 :=
  ⟨upper194, packed194, rowFacts194⟩

private theorem checked195 : PackedRowCertificate 195 :=
  ⟨upper195, packed195, rowFacts195⟩

private theorem checked196 : PackedRowCertificate 196 :=
  ⟨upper196, packed196, rowFacts196⟩

private theorem checked197 : PackedRowCertificate 197 :=
  ⟨upper197, packed197, rowFacts197⟩

private theorem checked198 : PackedRowCertificate 198 :=
  ⟨upper198, packed198, rowFacts198⟩

private theorem checked199 : PackedRowCertificate 199 :=
  ⟨upper199, packed199, rowFacts199⟩

private theorem checked200 : PackedRowCertificate 200 :=
  ⟨upper200, packed200, rowFacts200⟩

private theorem checked201 : PackedRowCertificate 201 :=
  ⟨upper201, packed201, rowFacts201⟩

private theorem checked202 : PackedRowCertificate 202 :=
  ⟨upper202, packed202, rowFacts202⟩

private theorem checked203 : PackedRowCertificate 203 :=
  ⟨upper203, packed203, rowFacts203⟩

private theorem checked204 : PackedRowCertificate 204 :=
  ⟨upper204, packed204, rowFacts204⟩

private theorem checked205 : PackedRowCertificate 205 :=
  ⟨upper205, packed205, rowFacts205⟩

private theorem checked206 : PackedRowCertificate 206 :=
  ⟨upper206, packed206, rowFacts206⟩

private theorem checked207 : PackedRowCertificate 207 :=
  ⟨upper207, packed207, rowFacts207⟩

private theorem checked208 : PackedRowCertificate 208 :=
  ⟨upper208, packed208, rowFacts208⟩

private theorem checked209 : PackedRowCertificate 209 :=
  ⟨upper209, packed209, rowFacts209⟩

private theorem checked210 : PackedRowCertificate 210 :=
  ⟨upper210, packed210, rowFacts210⟩

private theorem checked211 : PackedRowCertificate 211 :=
  ⟨upper211, packed211, rowFacts211⟩

private theorem checked212 : PackedRowCertificate 212 :=
  ⟨upper212, packed212, rowFacts212⟩

private theorem checked213 : PackedRowCertificate 213 :=
  ⟨upper213, packed213, rowFacts213⟩

private theorem checked214 : PackedRowCertificate 214 :=
  ⟨upper214, packed214, rowFacts214⟩

private theorem checked215 : PackedRowCertificate 215 :=
  ⟨upper215, packed215, rowFacts215⟩

private theorem checked216 : PackedRowCertificate 216 :=
  ⟨upper216, packed216, rowFacts216⟩

private theorem checked217 : PackedRowCertificate 217 :=
  ⟨upper217, packed217, rowFacts217⟩

private theorem checked218 : PackedRowCertificate 218 :=
  ⟨upper218, packed218, rowFacts218⟩

private theorem checked219 : PackedRowCertificate 219 :=
  ⟨upper219, packed219, rowFacts219⟩

private theorem checked220 : PackedRowCertificate 220 :=
  ⟨upper220, packed220, rowFacts220⟩

private theorem checked221 : PackedRowCertificate 221 :=
  ⟨upper221, packed221, rowFacts221⟩

private theorem checked222 : PackedRowCertificate 222 :=
  ⟨upper222, packed222, rowFacts222⟩

private theorem checked223 : PackedRowCertificate 223 :=
  ⟨upper223, packed223, rowFacts223⟩

private theorem checked224 : PackedRowCertificate 224 :=
  ⟨upper224, packed224, rowFacts224⟩

private theorem checked225 : PackedRowCertificate 225 :=
  ⟨upper225, packed225, rowFacts225⟩

private theorem checked226 : PackedRowCertificate 226 :=
  ⟨upper226, packed226, rowFacts226⟩

private theorem checked227 : PackedRowCertificate 227 :=
  ⟨upper227, packed227, rowFacts227⟩

private theorem checked228 : PackedRowCertificate 228 :=
  ⟨upper228, packed228, rowFacts228⟩

private theorem checked229 : PackedRowCertificate 229 :=
  ⟨upper229, packed229, rowFacts229⟩

private theorem checked230 : PackedRowCertificate 230 :=
  ⟨upper230, packed230, rowFacts230⟩

private theorem checked231 : PackedRowCertificate 231 :=
  ⟨upper231, packed231, rowFacts231⟩

private theorem checked232 : PackedRowCertificate 232 :=
  ⟨upper232, packed232, rowFacts232⟩

private theorem checked233 : PackedRowCertificate 233 :=
  ⟨upper233, packed233, rowFacts233⟩

private theorem checked234 : PackedRowCertificate 234 :=
  ⟨upper234, packed234, rowFacts234⟩

private theorem checked235 : PackedRowCertificate 235 :=
  ⟨upper235, packed235, rowFacts235⟩

private theorem checked236 : PackedRowCertificate 236 :=
  ⟨upper236, packed236, rowFacts236⟩

private theorem checked237 : PackedRowCertificate 237 :=
  ⟨upper237, packed237, rowFacts237⟩

private theorem checked238 : PackedRowCertificate 238 :=
  ⟨upper238, packed238, rowFacts238⟩

private theorem checked239 : PackedRowCertificate 239 :=
  ⟨upper239, packed239, rowFacts239⟩

private theorem checked240 : PackedRowCertificate 240 :=
  ⟨upper240, packed240, rowFacts240⟩

private theorem checked241 : PackedRowCertificate 241 :=
  ⟨upper241, packed241, rowFacts241⟩

private theorem checked242 : PackedRowCertificate 242 :=
  ⟨upper242, packed242, rowFacts242⟩

private theorem checked243 : PackedRowCertificate 243 :=
  ⟨upper243, packed243, rowFacts243⟩

private theorem checked244 : PackedRowCertificate 244 :=
  ⟨upper244, packed244, rowFacts244⟩

private theorem checked245 : PackedRowCertificate 245 :=
  ⟨upper245, packed245, rowFacts245⟩

private theorem checked246 : PackedRowCertificate 246 :=
  ⟨upper246, packed246, rowFacts246⟩

private theorem checked247 : PackedRowCertificate 247 :=
  ⟨upper247, packed247, rowFacts247⟩

private theorem checked248 : PackedRowCertificate 248 :=
  ⟨upper248, packed248, rowFacts248⟩

private theorem checked249 : PackedRowCertificate 249 :=
  ⟨upper249, packed249, rowFacts249⟩

private theorem checked250 : PackedRowCertificate 250 :=
  ⟨upper250, packed250, rowFacts250⟩

private theorem checked251 : PackedRowCertificate 251 :=
  ⟨upper251, packed251, rowFacts251⟩

private theorem checked252 : PackedRowCertificate 252 :=
  ⟨upper252, packed252, rowFacts252⟩

private theorem checked253 : PackedRowCertificate 253 :=
  ⟨upper253, packed253, rowFacts253⟩

private theorem checked254 : PackedRowCertificate 254 :=
  ⟨upper254, packed254, rowFacts254⟩

private theorem checked255 : PackedRowCertificate 255 :=
  ⟨upper255, packed255, rowFacts255⟩

private theorem checked256 : PackedRowCertificate 256 :=
  ⟨upper256, packed256, rowFacts256⟩

private theorem checked257 : PackedRowCertificate 257 :=
  ⟨upper257, packed257, rowFacts257⟩

private theorem checked258 : PackedRowCertificate 258 :=
  ⟨upper258, packed258, rowFacts258⟩

private theorem checked259 : PackedRowCertificate 259 :=
  ⟨upper259, packed259, rowFacts259⟩

private theorem checked260 : PackedRowCertificate 260 :=
  ⟨upper260, packed260, rowFacts260⟩

private theorem checked261 : PackedRowCertificate 261 :=
  ⟨upper261, packed261, rowFacts261⟩

private theorem checked262 : PackedRowCertificate 262 :=
  ⟨upper262, packed262, rowFacts262⟩

private theorem checked263 : PackedRowCertificate 263 :=
  ⟨upper263, packed263, rowFacts263⟩

private theorem checked264 : PackedRowCertificate 264 :=
  ⟨upper264, packed264, rowFacts264⟩

private theorem checked265 : PackedRowCertificate 265 :=
  ⟨upper265, packed265, rowFacts265⟩

private theorem checked266 : PackedRowCertificate 266 :=
  ⟨upper266, packed266, rowFacts266⟩

private theorem checked267 : PackedRowCertificate 267 :=
  ⟨upper267, packed267, rowFacts267⟩

private theorem checked268 : PackedRowCertificate 268 :=
  ⟨upper268, packed268, rowFacts268⟩

private theorem checked269 : PackedRowCertificate 269 :=
  ⟨upper269, packed269, rowFacts269⟩

private theorem checked270 : PackedRowCertificate 270 :=
  ⟨upper270, packed270, rowFacts270⟩

private theorem checked271 : PackedRowCertificate 271 :=
  ⟨upper271, packed271, rowFacts271⟩

private theorem checked272 : PackedRowCertificate 272 :=
  ⟨upper272, packed272, rowFacts272⟩

private theorem checked273 : PackedRowCertificate 273 :=
  ⟨upper273, packed273, rowFacts273⟩

private theorem checked274 : PackedRowCertificate 274 :=
  ⟨upper274, packed274, rowFacts274⟩

private theorem checked275 : PackedRowCertificate 275 :=
  ⟨upper275, packed275, rowFacts275⟩

private theorem checked276 : PackedRowCertificate 276 :=
  ⟨upper276, packed276, rowFacts276⟩

private theorem checked277 : PackedRowCertificate 277 :=
  ⟨upper277, packed277, rowFacts277⟩

private theorem checked278 : PackedRowCertificate 278 :=
  ⟨upper278, packed278, rowFacts278⟩

private theorem checked279 : PackedRowCertificate 279 :=
  ⟨upper279, packed279, rowFacts279⟩

private theorem checked280 : PackedRowCertificate 280 :=
  ⟨upper280, packed280, rowFacts280⟩

private theorem checked281 : PackedRowCertificate 281 :=
  ⟨upper281, packed281, rowFacts281⟩

private theorem checked282 : PackedRowCertificate 282 :=
  ⟨upper282, packed282, rowFacts282⟩

private theorem checked283 : PackedRowCertificate 283 :=
  ⟨upper283, packed283, rowFacts283⟩

private theorem checked284 : PackedRowCertificate 284 :=
  ⟨upper284, packed284, rowFacts284⟩

private theorem checked285 : PackedRowCertificate 285 :=
  ⟨upper285, packed285, rowFacts285⟩

private theorem checked286 : PackedRowCertificate 286 :=
  ⟨upper286, packed286, rowFacts286⟩

private theorem checked287 : PackedRowCertificate 287 :=
  ⟨upper287, packed287, rowFacts287⟩

private theorem checked288 : PackedRowCertificate 288 :=
  ⟨upper288, packed288, rowFacts288⟩

private theorem checked289 : PackedRowCertificate 289 :=
  ⟨upper289, packed289, rowFacts289⟩

private theorem checked290 : PackedRowCertificate 290 :=
  ⟨upper290, packed290, rowFacts290⟩

private theorem checked291 : PackedRowCertificate 291 :=
  ⟨upper291, packed291, rowFacts291⟩

private theorem checked292 : PackedRowCertificate 292 :=
  ⟨upper292, packed292, rowFacts292⟩

private theorem checked293 : PackedRowCertificate 293 :=
  ⟨upper293, packed293, rowFacts293⟩

private theorem checked294 : PackedRowCertificate 294 :=
  ⟨upper294, packed294, rowFacts294⟩

private theorem checked295 : PackedRowCertificate 295 :=
  ⟨upper295, packed295, rowFacts295⟩

private theorem checked296 : PackedRowCertificate 296 :=
  ⟨upper296, packed296, rowFacts296⟩

private theorem checked297 : PackedRowCertificate 297 :=
  ⟨upper297, packed297, rowFacts297⟩

private theorem checked298 : PackedRowCertificate 298 :=
  ⟨upper298, packed298, rowFacts298⟩

private theorem checked299 : PackedRowCertificate 299 :=
  ⟨upper299, packed299, rowFacts299⟩

private theorem checked300 : PackedRowCertificate 300 :=
  ⟨upper300, packed300, rowFacts300⟩

private theorem checked301 : PackedRowCertificate 301 :=
  ⟨upper301, packed301, rowFacts301⟩

private theorem checked302 : PackedRowCertificate 302 :=
  ⟨upper302, packed302, rowFacts302⟩

private theorem checked303 : PackedRowCertificate 303 :=
  ⟨upper303, packed303, rowFacts303⟩

private theorem checked304 : PackedRowCertificate 304 :=
  ⟨upper304, packed304, rowFacts304⟩

private theorem checked305 : PackedRowCertificate 305 :=
  ⟨upper305, packed305, rowFacts305⟩

private theorem checked306 : PackedRowCertificate 306 :=
  ⟨upper306, packed306, rowFacts306⟩

private theorem checked307 : PackedRowCertificate 307 :=
  ⟨upper307, packed307, rowFacts307⟩

private theorem checked308 : PackedRowCertificate 308 :=
  ⟨upper308, packed308, rowFacts308⟩

private theorem checked309 : PackedRowCertificate 309 :=
  ⟨upper309, packed309, rowFacts309⟩

private theorem checked310 : PackedRowCertificate 310 :=
  ⟨upper310, packed310, rowFacts310⟩

private theorem checked311 : PackedRowCertificate 311 :=
  ⟨upper311, packed311, rowFacts311⟩

private theorem checked312 : PackedRowCertificate 312 :=
  ⟨upper312, packed312, rowFacts312⟩

private theorem checked313 : PackedRowCertificate 313 :=
  ⟨upper313, packed313, rowFacts313⟩

private theorem checked314 : PackedRowCertificate 314 :=
  ⟨upper314, packed314, rowFacts314⟩

private theorem checked315 : PackedRowCertificate 315 :=
  ⟨upper315, packed315, rowFacts315⟩

private theorem checked316 : PackedRowCertificate 316 :=
  ⟨upper316, packed316, rowFacts316⟩

private theorem checked317 : PackedRowCertificate 317 :=
  ⟨upper317, packed317, rowFacts317⟩

private theorem checked318 : PackedRowCertificate 318 :=
  ⟨upper318, packed318, rowFacts318⟩

private theorem checked319 : PackedRowCertificate 319 :=
  ⟨upper319, packed319, rowFacts319⟩

private theorem checked320 : PackedRowCertificate 320 :=
  ⟨upper320, packed320, rowFacts320⟩

private theorem checked321 : PackedRowCertificate 321 :=
  ⟨upper321, packed321, rowFacts321⟩

private theorem checked322 : PackedRowCertificate 322 :=
  ⟨upper322, packed322, rowFacts322⟩

private theorem checked323 : PackedRowCertificate 323 :=
  ⟨upper323, packed323, rowFacts323⟩

private theorem checked324 : PackedRowCertificate 324 :=
  ⟨upper324, packed324, rowFacts324⟩

private theorem checked325 : PackedRowCertificate 325 :=
  ⟨upper325, packed325, rowFacts325⟩

private theorem checked326 : PackedRowCertificate 326 :=
  ⟨upper326, packed326, rowFacts326⟩

private theorem checked327 : PackedRowCertificate 327 :=
  ⟨upper327, packed327, rowFacts327⟩

private theorem checked328 : PackedRowCertificate 328 :=
  ⟨upper328, packed328, rowFacts328⟩

private theorem checked329 : PackedRowCertificate 329 :=
  ⟨upper329, packed329, rowFacts329⟩

private theorem checked330 : PackedRowCertificate 330 :=
  ⟨upper330, packed330, rowFacts330⟩

private theorem checked331 : PackedRowCertificate 331 :=
  ⟨upper331, packed331, rowFacts331⟩

private theorem checked332 : PackedRowCertificate 332 :=
  ⟨upper332, packed332, rowFacts332⟩

private theorem checked333 : PackedRowCertificate 333 :=
  ⟨upper333, packed333, rowFacts333⟩

private theorem checked334 : PackedRowCertificate 334 :=
  ⟨upper334, packed334, rowFacts334⟩

private theorem checked335 : PackedRowCertificate 335 :=
  ⟨upper335, packed335, rowFacts335⟩

private theorem checked336 : PackedRowCertificate 336 :=
  ⟨upper336, packed336, rowFacts336⟩

private theorem checked337 : PackedRowCertificate 337 :=
  ⟨upper337, packed337, rowFacts337⟩

private theorem checked338 : PackedRowCertificate 338 :=
  ⟨upper338, packed338, rowFacts338⟩

private theorem checked339 : PackedRowCertificate 339 :=
  ⟨upper339, packed339, rowFacts339⟩

private theorem checked340 : PackedRowCertificate 340 :=
  ⟨upper340, packed340, rowFacts340⟩

private theorem checked341 : PackedRowCertificate 341 :=
  ⟨upper341, packed341, rowFacts341⟩

private theorem checked342 : PackedRowCertificate 342 :=
  ⟨upper342, packed342, rowFacts342⟩

private theorem checked343 : PackedRowCertificate 343 :=
  ⟨upper343, packed343, rowFacts343⟩

private theorem checked344 : PackedRowCertificate 344 :=
  ⟨upper344, packed344, rowFacts344⟩

private theorem checked345 : PackedRowCertificate 345 :=
  ⟨upper345, packed345, rowFacts345⟩

private theorem checked346 : PackedRowCertificate 346 :=
  ⟨upper346, packed346, rowFacts346⟩

private theorem checked347 : PackedRowCertificate 347 :=
  ⟨upper347, packed347, rowFacts347⟩

private theorem checked348 : PackedRowCertificate 348 :=
  ⟨upper348, packed348, rowFacts348⟩

private theorem checked349 : PackedRowCertificate 349 :=
  ⟨upper349, packed349, rowFacts349⟩

private theorem checked350 : PackedRowCertificate 350 :=
  ⟨upper350, packed350, rowFacts350⟩

private theorem checked351 : PackedRowCertificate 351 :=
  ⟨upper351, packed351, rowFacts351⟩

private theorem checked352 : PackedRowCertificate 352 :=
  ⟨upper352, packed352, rowFacts352⟩

private theorem checked353 : PackedRowCertificate 353 :=
  ⟨upper353, packed353, rowFacts353⟩

private theorem checked354 : PackedRowCertificate 354 :=
  ⟨upper354, packed354, rowFacts354⟩

private theorem checked355 : PackedRowCertificate 355 :=
  ⟨upper355, packed355, rowFacts355⟩

private theorem checked356 : PackedRowCertificate 356 :=
  ⟨upper356, packed356, rowFacts356⟩

private theorem checked357 : PackedRowCertificate 357 :=
  ⟨upper357, packed357, rowFacts357⟩

private theorem checked358 : PackedRowCertificate 358 :=
  ⟨upper358, packed358, rowFacts358⟩

private theorem checked359 : PackedRowCertificate 359 :=
  ⟨upper359, packed359, rowFacts359⟩

private theorem checked360 : PackedRowCertificate 360 :=
  ⟨upper360, packed360, rowFacts360⟩

private theorem checked361 : PackedRowCertificate 361 :=
  ⟨upper361, packed361, rowFacts361⟩

private theorem checked362 : PackedRowCertificate 362 :=
  ⟨upper362, packed362, rowFacts362⟩

private theorem checked363 : PackedRowCertificate 363 :=
  ⟨upper363, packed363, rowFacts363⟩

private theorem checked364 : PackedRowCertificate 364 :=
  ⟨upper364, packed364, rowFacts364⟩

private theorem checked365 : PackedRowCertificate 365 :=
  ⟨upper365, packed365, rowFacts365⟩

private theorem checked366 : PackedRowCertificate 366 :=
  ⟨upper366, packed366, rowFacts366⟩

private theorem checked367 : PackedRowCertificate 367 :=
  ⟨upper367, packed367, rowFacts367⟩

private theorem checked368 : PackedRowCertificate 368 :=
  ⟨upper368, packed368, rowFacts368⟩

private theorem checked369 : PackedRowCertificate 369 :=
  ⟨upper369, packed369, rowFacts369⟩

private theorem checked370 : PackedRowCertificate 370 :=
  ⟨upper370, packed370, rowFacts370⟩

private theorem checked371 : PackedRowCertificate 371 :=
  ⟨upper371, packed371, rowFacts371⟩

private theorem checked372 : PackedRowCertificate 372 :=
  ⟨upper372, packed372, rowFacts372⟩

private theorem checked373 : PackedRowCertificate 373 :=
  ⟨upper373, packed373, rowFacts373⟩

private theorem checked374 : PackedRowCertificate 374 :=
  ⟨upper374, packed374, rowFacts374⟩

private theorem checked375 : PackedRowCertificate 375 :=
  ⟨upper375, packed375, rowFacts375⟩

private theorem checked376 : PackedRowCertificate 376 :=
  ⟨upper376, packed376, rowFacts376⟩

private theorem checked377 : PackedRowCertificate 377 :=
  ⟨upper377, packed377, rowFacts377⟩

private theorem checked378 : PackedRowCertificate 378 :=
  ⟨upper378, packed378, rowFacts378⟩

private theorem checked379 : PackedRowCertificate 379 :=
  ⟨upper379, packed379, rowFacts379⟩

private theorem checked380 : PackedRowCertificate 380 :=
  ⟨upper380, packed380, rowFacts380⟩

private theorem checked381 : PackedRowCertificate 381 :=
  ⟨upper381, packed381, rowFacts381⟩

private theorem checked382 : PackedRowCertificate 382 :=
  ⟨upper382, packed382, rowFacts382⟩

private theorem checked383 : PackedRowCertificate 383 :=
  ⟨upper383, packed383, rowFacts383⟩

private theorem checked384 : PackedRowCertificate 384 :=
  ⟨upper384, packed384, rowFacts384⟩

private theorem checked385 : PackedRowCertificate 385 :=
  ⟨upper385, packed385, rowFacts385⟩

private theorem checked386 : PackedRowCertificate 386 :=
  ⟨upper386, packed386, rowFacts386⟩

private theorem checked387 : PackedRowCertificate 387 :=
  ⟨upper387, packed387, rowFacts387⟩

private theorem checked388 : PackedRowCertificate 388 :=
  ⟨upper388, packed388, rowFacts388⟩

private theorem checked389 : PackedRowCertificate 389 :=
  ⟨upper389, packed389, rowFacts389⟩

private theorem checked390 : PackedRowCertificate 390 :=
  ⟨upper390, packed390, rowFacts390⟩

private theorem checked391 : PackedRowCertificate 391 :=
  ⟨upper391, packed391, rowFacts391⟩

private theorem checked392 : PackedRowCertificate 392 :=
  ⟨upper392, packed392, rowFacts392⟩

private theorem checked393 : PackedRowCertificate 393 :=
  ⟨upper393, packed393, rowFacts393⟩

private theorem checked394 : PackedRowCertificate 394 :=
  ⟨upper394, packed394, rowFacts394⟩

private theorem checked395 : PackedRowCertificate 395 :=
  ⟨upper395, packed395, rowFacts395⟩

private theorem checked396 : PackedRowCertificate 396 :=
  ⟨upper396, packed396, rowFacts396⟩

private theorem checked397 : PackedRowCertificate 397 :=
  ⟨upper397, packed397, rowFacts397⟩

private theorem checked398 : PackedRowCertificate 398 :=
  ⟨upper398, packed398, rowFacts398⟩

private theorem checked399 : PackedRowCertificate 399 :=
  ⟨upper399, packed399, rowFacts399⟩

private theorem checked400 : PackedRowCertificate 400 :=
  ⟨upper400, packed400, rowFacts400⟩

private theorem checked401 : PackedRowCertificate 401 :=
  ⟨upper401, packed401, rowFacts401⟩

private theorem checked402 : PackedRowCertificate 402 :=
  ⟨upper402, packed402, rowFacts402⟩

private theorem checked403 : PackedRowCertificate 403 :=
  ⟨upper403, packed403, rowFacts403⟩

private theorem checked404 : PackedRowCertificate 404 :=
  ⟨upper404, packed404, rowFacts404⟩

private theorem checked405 : PackedRowCertificate 405 :=
  ⟨upper405, packed405, rowFacts405⟩

private theorem checked406 : PackedRowCertificate 406 :=
  ⟨upper406, packed406, rowFacts406⟩

private theorem checked407 : PackedRowCertificate 407 :=
  ⟨upper407, packed407, rowFacts407⟩

private theorem checked408 : PackedRowCertificate 408 :=
  ⟨upper408, packed408, rowFacts408⟩

private theorem checked409 : PackedRowCertificate 409 :=
  ⟨upper409, packed409, rowFacts409⟩

private theorem checked410 : PackedRowCertificate 410 :=
  ⟨upper410, packed410, rowFacts410⟩

private theorem checked411 : PackedRowCertificate 411 :=
  ⟨upper411, packed411, rowFacts411⟩

private theorem checked412 : PackedRowCertificate 412 :=
  ⟨upper412, packed412, rowFacts412⟩

private theorem checked413 : PackedRowCertificate 413 :=
  ⟨upper413, packed413, rowFacts413⟩

private theorem checked414 : PackedRowCertificate 414 :=
  ⟨upper414, packed414, rowFacts414⟩

private theorem checked415 : PackedRowCertificate 415 :=
  ⟨upper415, packed415, rowFacts415⟩

private theorem checked416 : PackedRowCertificate 416 :=
  ⟨upper416, packed416, rowFacts416⟩

private theorem checked417 : PackedRowCertificate 417 :=
  ⟨upper417, packed417, rowFacts417⟩

private theorem checked418 : PackedRowCertificate 418 :=
  ⟨upper418, packed418, rowFacts418⟩

private theorem checked419 : PackedRowCertificate 419 :=
  ⟨upper419, packed419, rowFacts419⟩

private theorem checked420 : PackedRowCertificate 420 :=
  ⟨upper420, packed420, rowFacts420⟩

private theorem checked421 : PackedRowCertificate 421 :=
  ⟨upper421, packed421, rowFacts421⟩

private theorem checked422 : PackedRowCertificate 422 :=
  ⟨upper422, packed422, rowFacts422⟩

private theorem checked423 : PackedRowCertificate 423 :=
  ⟨upper423, packed423, rowFacts423⟩

private theorem checked424 : PackedRowCertificate 424 :=
  ⟨upper424, packed424, rowFacts424⟩

private theorem checked425 : PackedRowCertificate 425 :=
  ⟨upper425, packed425, rowFacts425⟩

private theorem checked426 : PackedRowCertificate 426 :=
  ⟨upper426, packed426, rowFacts426⟩

private theorem checked427 : PackedRowCertificate 427 :=
  ⟨upper427, packed427, rowFacts427⟩

private theorem checked428 : PackedRowCertificate 428 :=
  ⟨upper428, packed428, rowFacts428⟩

private theorem checked429 : PackedRowCertificate 429 :=
  ⟨upper429, packed429, rowFacts429⟩

private theorem checked430 : PackedRowCertificate 430 :=
  ⟨upper430, packed430, rowFacts430⟩

private theorem checked431 : PackedRowCertificate 431 :=
  ⟨upper431, packed431, rowFacts431⟩

private theorem checked432 : PackedRowCertificate 432 :=
  ⟨upper432, packed432, rowFacts432⟩

private theorem checked433 : PackedRowCertificate 433 :=
  ⟨upper433, packed433, rowFacts433⟩

private theorem checked434 : PackedRowCertificate 434 :=
  ⟨upper434, packed434, rowFacts434⟩

private theorem checked435 : PackedRowCertificate 435 :=
  ⟨upper435, packed435, rowFacts435⟩

private theorem checked436 : PackedRowCertificate 436 :=
  ⟨upper436, packed436, rowFacts436⟩

private theorem checked437 : PackedRowCertificate 437 :=
  ⟨upper437, packed437, rowFacts437⟩

private theorem checked438 : PackedRowCertificate 438 :=
  ⟨upper438, packed438, rowFacts438⟩

private theorem checked439 : PackedRowCertificate 439 :=
  ⟨upper439, packed439, rowFacts439⟩

private theorem checked440 : PackedRowCertificate 440 :=
  ⟨upper440, packed440, rowFacts440⟩

private theorem checked441 : PackedRowCertificate 441 :=
  ⟨upper441, packed441, rowFacts441⟩

private theorem checked442 : PackedRowCertificate 442 :=
  ⟨upper442, packed442, rowFacts442⟩

private theorem checked443 : PackedRowCertificate 443 :=
  ⟨upper443, packed443, rowFacts443⟩

private theorem checked444 : PackedRowCertificate 444 :=
  ⟨upper444, packed444, rowFacts444⟩

private theorem checked445 : PackedRowCertificate 445 :=
  ⟨upper445, packed445, rowFacts445⟩

private theorem checked446 : PackedRowCertificate 446 :=
  ⟨upper446, packed446, rowFacts446⟩

private theorem checked447 : PackedRowCertificate 447 :=
  ⟨upper447, packed447, rowFacts447⟩

private theorem checked448 : PackedRowCertificate 448 :=
  ⟨upper448, packed448, rowFacts448⟩

private theorem checked449 : PackedRowCertificate 449 :=
  ⟨upper449, packed449, rowFacts449⟩

private theorem checked450 : PackedRowCertificate 450 :=
  ⟨upper450, packed450, rowFacts450⟩

private theorem checked451 : PackedRowCertificate 451 :=
  ⟨upper451, packed451, rowFacts451⟩

private theorem checked452 : PackedRowCertificate 452 :=
  ⟨upper452, packed452, rowFacts452⟩

private theorem checked453 : PackedRowCertificate 453 :=
  ⟨upper453, packed453, rowFacts453⟩

private theorem checked454 : PackedRowCertificate 454 :=
  ⟨upper454, packed454, rowFacts454⟩

private theorem checked455 : PackedRowCertificate 455 :=
  ⟨upper455, packed455, rowFacts455⟩

private theorem checked456 : PackedRowCertificate 456 :=
  ⟨upper456, packed456, rowFacts456⟩

private theorem checked457 : PackedRowCertificate 457 :=
  ⟨upper457, packed457, rowFacts457⟩

private theorem checked458 : PackedRowCertificate 458 :=
  ⟨upper458, packed458, rowFacts458⟩

private theorem checked459 : PackedRowCertificate 459 :=
  ⟨upper459, packed459, rowFacts459⟩

private theorem checked460 : PackedRowCertificate 460 :=
  ⟨upper460, packed460, rowFacts460⟩

private theorem checked461 : PackedRowCertificate 461 :=
  ⟨upper461, packed461, rowFacts461⟩

private theorem checked462 : PackedRowCertificate 462 :=
  ⟨upper462, packed462, rowFacts462⟩

private theorem checked463 : PackedRowCertificate 463 :=
  ⟨upper463, packed463, rowFacts463⟩

private theorem checked464 : PackedRowCertificate 464 :=
  ⟨upper464, packed464, rowFacts464⟩

private theorem checked465 : PackedRowCertificate 465 :=
  ⟨upper465, packed465, rowFacts465⟩

private theorem checked466 : PackedRowCertificate 466 :=
  ⟨upper466, packed466, rowFacts466⟩

private theorem checked467 : PackedRowCertificate 467 :=
  ⟨upper467, packed467, rowFacts467⟩

private theorem checked468 : PackedRowCertificate 468 :=
  ⟨upper468, packed468, rowFacts468⟩

private theorem checked469 : PackedRowCertificate 469 :=
  ⟨upper469, packed469, rowFacts469⟩

private theorem checked470 : PackedRowCertificate 470 :=
  ⟨upper470, packed470, rowFacts470⟩

private theorem checked471 : PackedRowCertificate 471 :=
  ⟨upper471, packed471, rowFacts471⟩

private theorem checked472 : PackedRowCertificate 472 :=
  ⟨upper472, packed472, rowFacts472⟩

private theorem checked473 : PackedRowCertificate 473 :=
  ⟨upper473, packed473, rowFacts473⟩

private theorem checked474 : PackedRowCertificate 474 :=
  ⟨upper474, packed474, rowFacts474⟩

private theorem checked475 : PackedRowCertificate 475 :=
  ⟨upper475, packed475, rowFacts475⟩

private theorem checked476 : PackedRowCertificate 476 :=
  ⟨upper476, packed476, rowFacts476⟩

private theorem checked477 : PackedRowCertificate 477 :=
  ⟨upper477, packed477, rowFacts477⟩

private theorem checked478 : PackedRowCertificate 478 :=
  ⟨upper478, packed478, rowFacts478⟩

private theorem checked479 : PackedRowCertificate 479 :=
  ⟨upper479, packed479, rowFacts479⟩

private theorem checked480 : PackedRowCertificate 480 :=
  ⟨upper480, packed480, rowFacts480⟩

private theorem checked481 : PackedRowCertificate 481 :=
  ⟨upper481, packed481, rowFacts481⟩

private theorem checked482 : PackedRowCertificate 482 :=
  ⟨upper482, packed482, rowFacts482⟩

private theorem checked483 : PackedRowCertificate 483 :=
  ⟨upper483, packed483, rowFacts483⟩

private theorem checked484 : PackedRowCertificate 484 :=
  ⟨upper484, packed484, rowFacts484⟩

private theorem checked485 : PackedRowCertificate 485 :=
  ⟨upper485, packed485, rowFacts485⟩

private theorem checked486 : PackedRowCertificate 486 :=
  ⟨upper486, packed486, rowFacts486⟩

private theorem checked487 : PackedRowCertificate 487 :=
  ⟨upper487, packed487, rowFacts487⟩

private theorem checked488 : PackedRowCertificate 488 :=
  ⟨upper488, packed488, rowFacts488⟩

private theorem checked489 : PackedRowCertificate 489 :=
  ⟨upper489, packed489, rowFacts489⟩

private theorem checked490 : PackedRowCertificate 490 :=
  ⟨upper490, packed490, rowFacts490⟩

private theorem checked491 : PackedRowCertificate 491 :=
  ⟨upper491, packed491, rowFacts491⟩

private theorem checked492 : PackedRowCertificate 492 :=
  ⟨upper492, packed492, rowFacts492⟩

private theorem checked493 : PackedRowCertificate 493 :=
  ⟨upper493, packed493, rowFacts493⟩

private theorem checked494 : PackedRowCertificate 494 :=
  ⟨upper494, packed494, rowFacts494⟩

private theorem checked495 : PackedRowCertificate 495 :=
  ⟨upper495, packed495, rowFacts495⟩

private theorem checked496 : PackedRowCertificate 496 :=
  ⟨upper496, packed496, rowFacts496⟩

private theorem checked497 : PackedRowCertificate 497 :=
  ⟨upper497, packed497, rowFacts497⟩

private theorem checked498 : PackedRowCertificate 498 :=
  ⟨upper498, packed498, rowFacts498⟩

private theorem checked499 : PackedRowCertificate 499 :=
  ⟨upper499, packed499, rowFacts499⟩

private theorem checked500 : PackedRowCertificate 500 :=
  ⟨upper500, packed500, rowFacts500⟩

private theorem checked501 : PackedRowCertificate 501 :=
  ⟨upper501, packed501, rowFacts501⟩

private theorem checked502 : PackedRowCertificate 502 :=
  ⟨upper502, packed502, rowFacts502⟩

private theorem checked503 : PackedRowCertificate 503 :=
  ⟨upper503, packed503, rowFacts503⟩

private theorem checked504 : PackedRowCertificate 504 :=
  ⟨upper504, packed504, rowFacts504⟩

private theorem checked505 : PackedRowCertificate 505 :=
  ⟨upper505, packed505, rowFacts505⟩

private theorem checked506 : PackedRowCertificate 506 :=
  ⟨upper506, packed506, rowFacts506⟩

private theorem checked507 : PackedRowCertificate 507 :=
  ⟨upper507, packed507, rowFacts507⟩

private theorem checked508 : PackedRowCertificate 508 :=
  ⟨upper508, packed508, rowFacts508⟩

private theorem checked509 : PackedRowCertificate 509 :=
  ⟨upper509, packed509, rowFacts509⟩

private theorem checked510 : PackedRowCertificate 510 :=
  ⟨upper510, packed510, rowFacts510⟩

private theorem checked511 : PackedRowCertificate 511 :=
  ⟨upper511, packed511, rowFacts511⟩

private theorem checked512 : PackedRowCertificate 512 :=
  ⟨upper512, packed512, rowFacts512⟩

private theorem checked513 : PackedRowCertificate 513 :=
  ⟨upper513, packed513, rowFacts513⟩

private theorem checked514 : PackedRowCertificate 514 :=
  ⟨upper514, packed514, rowFacts514⟩

private theorem checked515 : PackedRowCertificate 515 :=
  ⟨upper515, packed515, rowFacts515⟩

private theorem checked516 : PackedRowCertificate 516 :=
  ⟨upper516, packed516, rowFacts516⟩

private theorem checked517 : PackedRowCertificate 517 :=
  ⟨upper517, packed517, rowFacts517⟩

private theorem checked518 : PackedRowCertificate 518 :=
  ⟨upper518, packed518, rowFacts518⟩

private theorem checked519 : PackedRowCertificate 519 :=
  ⟨upper519, packed519, rowFacts519⟩

private theorem checked520 : PackedRowCertificate 520 :=
  ⟨upper520, packed520, rowFacts520⟩

private theorem checked521 : PackedRowCertificate 521 :=
  ⟨upper521, packed521, rowFacts521⟩

private theorem checked522 : PackedRowCertificate 522 :=
  ⟨upper522, packed522, rowFacts522⟩

private theorem checked523 : PackedRowCertificate 523 :=
  ⟨upper523, packed523, rowFacts523⟩

private theorem checked524 : PackedRowCertificate 524 :=
  ⟨upper524, packed524, rowFacts524⟩

private theorem checked525 : PackedRowCertificate 525 :=
  ⟨upper525, packed525, rowFacts525⟩

private theorem checked526 : PackedRowCertificate 526 :=
  ⟨upper526, packed526, rowFacts526⟩

private theorem checked527 : PackedRowCertificate 527 :=
  ⟨upper527, packed527, rowFacts527⟩

private theorem checked528 : PackedRowCertificate 528 :=
  ⟨upper528, packed528, rowFacts528⟩

private theorem checked529 : PackedRowCertificate 529 :=
  ⟨upper529, packed529, rowFacts529⟩

private theorem checked530 : PackedRowCertificate 530 :=
  ⟨upper530, packed530, rowFacts530⟩

private theorem checked531 : PackedRowCertificate 531 :=
  ⟨upper531, packed531, rowFacts531⟩

private theorem checked532 : PackedRowCertificate 532 :=
  ⟨upper532, packed532, rowFacts532⟩

private theorem checked533 : PackedRowCertificate 533 :=
  ⟨upper533, packed533, rowFacts533⟩

private theorem checked534 : PackedRowCertificate 534 :=
  ⟨upper534, packed534, rowFacts534⟩

private theorem checked535 : PackedRowCertificate 535 :=
  ⟨upper535, packed535, rowFacts535⟩

private theorem checked536 : PackedRowCertificate 536 :=
  ⟨upper536, packed536, rowFacts536⟩

private theorem checked537 : PackedRowCertificate 537 :=
  ⟨upper537, packed537, rowFacts537⟩

private theorem checked538 : PackedRowCertificate 538 :=
  ⟨upper538, packed538, rowFacts538⟩

private theorem checked539 : PackedRowCertificate 539 :=
  ⟨upper539, packed539, rowFacts539⟩

private theorem checked540 : PackedRowCertificate 540 :=
  ⟨upper540, packed540, rowFacts540⟩

private theorem checked541 : PackedRowCertificate 541 :=
  ⟨upper541, packed541, rowFacts541⟩

private abbrev checkedPredicate (j : Nat) : Prop :=
  PackedRowCertificate (Fin.ofNat 542 j)

private def blockIndices000 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

private theorem checkedBlock000 : List.Forall checkedPredicate blockIndices000 := by
  exact ⟨
    checked000, checked001, checked002, checked003, checked004, checked005, checked006, checked007,
    checked008, checked009, checked010, checked011, checked012, checked013, checked014, checked015,
    checked016, checked017, checked018, checked019, checked020, checked021, checked022, checked023,
    checked024, checked025, checked026, checked027, checked028, checked029, checked030, checked031
  ⟩

private def blockIndices032 : List Nat :=
  [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

private theorem checkedBlock032 : List.Forall checkedPredicate blockIndices032 := by
  exact ⟨
    checked032, checked033, checked034, checked035, checked036, checked037, checked038, checked039,
    checked040, checked041, checked042, checked043, checked044, checked045, checked046, checked047,
    checked048, checked049, checked050, checked051, checked052, checked053, checked054, checked055,
    checked056, checked057, checked058, checked059, checked060, checked061, checked062, checked063
  ⟩

private def blockIndices064 : List Nat :=
  [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

private theorem checkedBlock064 : List.Forall checkedPredicate blockIndices064 := by
  exact ⟨
    checked064, checked065, checked066, checked067, checked068, checked069, checked070, checked071,
    checked072, checked073, checked074, checked075, checked076, checked077, checked078, checked079,
    checked080, checked081, checked082, checked083, checked084, checked085, checked086, checked087,
    checked088, checked089, checked090, checked091, checked092, checked093, checked094, checked095
  ⟩

private def blockIndices096 : List Nat :=
  [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

private theorem checkedBlock096 : List.Forall checkedPredicate blockIndices096 := by
  exact ⟨
    checked096, checked097, checked098, checked099, checked100, checked101, checked102, checked103,
    checked104, checked105, checked106, checked107, checked108, checked109, checked110, checked111,
    checked112, checked113, checked114, checked115, checked116, checked117, checked118, checked119,
    checked120, checked121, checked122, checked123, checked124, checked125, checked126, checked127
  ⟩

private def blockIndices128 : List Nat :=
  [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]

private theorem checkedBlock128 : List.Forall checkedPredicate blockIndices128 := by
  exact ⟨
    checked128, checked129, checked130, checked131, checked132, checked133, checked134, checked135,
    checked136, checked137, checked138, checked139, checked140, checked141, checked142, checked143,
    checked144, checked145, checked146, checked147, checked148, checked149, checked150, checked151,
    checked152, checked153, checked154, checked155, checked156, checked157, checked158, checked159
  ⟩

private def blockIndices160 : List Nat :=
  [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

private theorem checkedBlock160 : List.Forall checkedPredicate blockIndices160 := by
  exact ⟨
    checked160, checked161, checked162, checked163, checked164, checked165, checked166, checked167,
    checked168, checked169, checked170, checked171, checked172, checked173, checked174, checked175,
    checked176, checked177, checked178, checked179, checked180, checked181, checked182, checked183,
    checked184, checked185, checked186, checked187, checked188, checked189, checked190, checked191
  ⟩

private def blockIndices192 : List Nat :=
  [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]

private theorem checkedBlock192 : List.Forall checkedPredicate blockIndices192 := by
  exact ⟨
    checked192, checked193, checked194, checked195, checked196, checked197, checked198, checked199,
    checked200, checked201, checked202, checked203, checked204, checked205, checked206, checked207,
    checked208, checked209, checked210, checked211, checked212, checked213, checked214, checked215,
    checked216, checked217, checked218, checked219, checked220, checked221, checked222, checked223
  ⟩

private def blockIndices224 : List Nat :=
  [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]

private theorem checkedBlock224 : List.Forall checkedPredicate blockIndices224 := by
  exact ⟨
    checked224, checked225, checked226, checked227, checked228, checked229, checked230, checked231,
    checked232, checked233, checked234, checked235, checked236, checked237, checked238, checked239,
    checked240, checked241, checked242, checked243, checked244, checked245, checked246, checked247,
    checked248, checked249, checked250, checked251, checked252, checked253, checked254, checked255
  ⟩

private def blockIndices256 : List Nat :=
  [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]

private theorem checkedBlock256 : List.Forall checkedPredicate blockIndices256 := by
  exact ⟨
    checked256, checked257, checked258, checked259, checked260, checked261, checked262, checked263,
    checked264, checked265, checked266, checked267, checked268, checked269, checked270, checked271,
    checked272, checked273, checked274, checked275, checked276, checked277, checked278, checked279,
    checked280, checked281, checked282, checked283, checked284, checked285, checked286, checked287
  ⟩

private def blockIndices288 : List Nat :=
  [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]

private theorem checkedBlock288 : List.Forall checkedPredicate blockIndices288 := by
  exact ⟨
    checked288, checked289, checked290, checked291, checked292, checked293, checked294, checked295,
    checked296, checked297, checked298, checked299, checked300, checked301, checked302, checked303,
    checked304, checked305, checked306, checked307, checked308, checked309, checked310, checked311,
    checked312, checked313, checked314, checked315, checked316, checked317, checked318, checked319
  ⟩

private def blockIndices320 : List Nat :=
  [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]

private theorem checkedBlock320 : List.Forall checkedPredicate blockIndices320 := by
  exact ⟨
    checked320, checked321, checked322, checked323, checked324, checked325, checked326, checked327,
    checked328, checked329, checked330, checked331, checked332, checked333, checked334, checked335,
    checked336, checked337, checked338, checked339, checked340, checked341, checked342, checked343,
    checked344, checked345, checked346, checked347, checked348, checked349, checked350, checked351
  ⟩

private def blockIndices352 : List Nat :=
  [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]

private theorem checkedBlock352 : List.Forall checkedPredicate blockIndices352 := by
  exact ⟨
    checked352, checked353, checked354, checked355, checked356, checked357, checked358, checked359,
    checked360, checked361, checked362, checked363, checked364, checked365, checked366, checked367,
    checked368, checked369, checked370, checked371, checked372, checked373, checked374, checked375,
    checked376, checked377, checked378, checked379, checked380, checked381, checked382, checked383
  ⟩

private def blockIndices384 : List Nat :=
  [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]

private theorem checkedBlock384 : List.Forall checkedPredicate blockIndices384 := by
  exact ⟨
    checked384, checked385, checked386, checked387, checked388, checked389, checked390, checked391,
    checked392, checked393, checked394, checked395, checked396, checked397, checked398, checked399,
    checked400, checked401, checked402, checked403, checked404, checked405, checked406, checked407,
    checked408, checked409, checked410, checked411, checked412, checked413, checked414, checked415
  ⟩

private def blockIndices416 : List Nat :=
  [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]

private theorem checkedBlock416 : List.Forall checkedPredicate blockIndices416 := by
  exact ⟨
    checked416, checked417, checked418, checked419, checked420, checked421, checked422, checked423,
    checked424, checked425, checked426, checked427, checked428, checked429, checked430, checked431,
    checked432, checked433, checked434, checked435, checked436, checked437, checked438, checked439,
    checked440, checked441, checked442, checked443, checked444, checked445, checked446, checked447
  ⟩

private def blockIndices448 : List Nat :=
  [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]

private theorem checkedBlock448 : List.Forall checkedPredicate blockIndices448 := by
  exact ⟨
    checked448, checked449, checked450, checked451, checked452, checked453, checked454, checked455,
    checked456, checked457, checked458, checked459, checked460, checked461, checked462, checked463,
    checked464, checked465, checked466, checked467, checked468, checked469, checked470, checked471,
    checked472, checked473, checked474, checked475, checked476, checked477, checked478, checked479
  ⟩

private def blockIndices480 : List Nat :=
  [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]

private theorem checkedBlock480 : List.Forall checkedPredicate blockIndices480 := by
  exact ⟨
    checked480, checked481, checked482, checked483, checked484, checked485, checked486, checked487,
    checked488, checked489, checked490, checked491, checked492, checked493, checked494, checked495,
    checked496, checked497, checked498, checked499, checked500, checked501, checked502, checked503,
    checked504, checked505, checked506, checked507, checked508, checked509, checked510, checked511
  ⟩

private def blockIndices512 : List Nat :=
  [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541]

private theorem checkedBlock512 : List.Forall checkedPredicate blockIndices512 := by
  exact ⟨
    checked512, checked513, checked514, checked515, checked516, checked517, checked518, checked519,
    checked520, checked521, checked522, checked523, checked524, checked525, checked526, checked527,
    checked528, checked529, checked530, checked531, checked532, checked533, checked534, checked535,
    checked536, checked537, checked538, checked539, checked540, checked541
  ⟩

private theorem checkedSuffix480 :
    List.Forall checkedPredicate (blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices480)
    (ys := blockIndices512)).mpr ⟨checkedBlock480, checkedBlock512⟩

private theorem checkedSuffix448 :
    List.Forall checkedPredicate (blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices448)
    (ys := blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock448, checkedSuffix480⟩

private theorem checkedSuffix416 :
    List.Forall checkedPredicate (blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices416)
    (ys := blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock416, checkedSuffix448⟩

private theorem checkedSuffix384 :
    List.Forall checkedPredicate (blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices384)
    (ys := blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock384, checkedSuffix416⟩

private theorem checkedSuffix352 :
    List.Forall checkedPredicate (blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices352)
    (ys := blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock352, checkedSuffix384⟩

private theorem checkedSuffix320 :
    List.Forall checkedPredicate (blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices320)
    (ys := blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock320, checkedSuffix352⟩

private theorem checkedSuffix288 :
    List.Forall checkedPredicate (blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices288)
    (ys := blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock288, checkedSuffix320⟩

private theorem checkedSuffix256 :
    List.Forall checkedPredicate (blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices256)
    (ys := blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock256, checkedSuffix288⟩

private theorem checkedSuffix224 :
    List.Forall checkedPredicate (blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices224)
    (ys := blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock224, checkedSuffix256⟩

private theorem checkedSuffix192 :
    List.Forall checkedPredicate (blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices192)
    (ys := blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock192, checkedSuffix224⟩

private theorem checkedSuffix160 :
    List.Forall checkedPredicate (blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices160)
    (ys := blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock160, checkedSuffix192⟩

private theorem checkedSuffix128 :
    List.Forall checkedPredicate (blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices128)
    (ys := blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock128, checkedSuffix160⟩

private theorem checkedSuffix096 :
    List.Forall checkedPredicate (blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices096)
    (ys := blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock096, checkedSuffix128⟩

private theorem checkedSuffix064 :
    List.Forall checkedPredicate (blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices064)
    (ys := blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock064, checkedSuffix096⟩

private theorem checkedSuffix032 :
    List.Forall checkedPredicate (blockIndices032 ++ blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices032)
    (ys := blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock032, checkedSuffix064⟩

private theorem checkedSuffix000 :
    List.Forall checkedPredicate (blockIndices000 ++ blockIndices032 ++ blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512) :=
  (List.forall_append (p := checkedPredicate) (xs := blockIndices000)
    (ys := blockIndices032 ++ blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512)).mpr ⟨checkedBlock000, checkedSuffix032⟩

private theorem rangeIndices_eq : List.range 542 = blockIndices000 ++ blockIndices032 ++ blockIndices064 ++ blockIndices096 ++ blockIndices128 ++ blockIndices160 ++ blockIndices192 ++ blockIndices224 ++ blockIndices256 ++ blockIndices288 ++ blockIndices320 ++ blockIndices352 ++ blockIndices384 ++ blockIndices416 ++ blockIndices448 ++ blockIndices480 ++ blockIndices512 := by
  decide +kernel

private theorem all_checked : ∀ i : Fin 542, PackedRowCertificate i := by
  apply forall_fin_of_rows (n := 542) (P := PackedRowCertificate)
  exact rangeIndices_eq.symm ▸ checkedSuffix000

theorem packed_upper_rows : ∀ i, packedUpper i = packSparse (2 ^ 40) (upperRows i) :=
  fun i => (all_checked i).upperEncoding

theorem packed_checks : ∀ i, packedProduct (lowerRows i) packedUpper =
    packSparse (2 ^ 40) (targetRows i) + 1009 * Nat.ofDigits (2 ^ 40) (quotientRows i) :=
  fun i => (all_checked i).productIdentity

theorem row_facts : ∀ i, PackedRowFacts i :=
  fun i => (all_checked i).rowFacts

private theorem coefficients_lt {row : SparseRow 542 Nat} (h : SparseRowBound row) :
    ∀ e ∈ row, e.2 < 1009 :=
  fun e he => of_decide_eq_true ((List.all_eq_true.mp h.2) e he)

/-- The exact product identity over the residue field. -/
theorem factorization : residueMatrix 1009 lowerRows * residueMatrix 1009 upperRows =
    residueMatrix 1009 targetRows := by
  refine checked_packed_product 1009 (2 ^ 40) (2 ^ 30) (542 * 1009)
    (by decide +kernel) (by decide +kernel) lowerRows upperRows targetRows packedUpper quotientRows
    packed_upper_rows ?_ ?_ quotientRows_length quotientRows_all_lt packed_checks
  · intro i j
    have h := rowValue_multiplyRow_le_dimension_sq_mul (lowerRows i) upperRows j 1009
      (row_facts i).lowerBound.1 (coefficients_lt (row_facts i).lowerBound)
      (fun k => (row_facts k).upperBound.1) (fun k => coefficients_lt (row_facts k).upperBound)
    exact h.trans_lt (by decide +kernel : 542 ^ 2 * 1009 ^ 2 < 2 ^ 40)
  · intro i j
    exact rowValue_le_dimension_mul (targetRows i) j 1009
      (row_facts i).targetBound.1 (coefficients_lt (row_facts i).targetBound)

theorem lower_support : ∀ i, (lowerRows i).all (fun e => decide (e.1 ≤ i)) = true :=
  fun i => (row_facts i).lowerSupport

theorem upper_support : ∀ i, (upperRows i).all (fun e => decide (i ≤ e.1)) = true :=
  fun i => (row_facts i).upperSupport

theorem lower_diagonal : ∀ i, rowValue (lowerRows i) i % 1009 ≠ 0 :=
  fun i => (row_facts i).lowerDiagonal

theorem upper_diagonal : ∀ i, rowValue (upperRows i) i % 1009 ≠ 0 :=
  fun i => (row_facts i).upperDiagonal

theorem columns_left_inverse : Function.LeftInverse inverseSelectedColumns selectedColumns :=
  fun i => (row_facts i).columnLeftInverse

theorem columns_right_inverse : Function.LeftInverse selectedColumns inverseSelectedColumns :=
  fun i => (row_facts i).columnRightInverse

/-- The packed certificate's target is the selected minor of the listed matrix. -/
theorem target_is_minor : residueMatrix 1009 targetRows =
    (residueMatrix 1009 originalRows).submatrix selectedRows selectedColumns :=
  residueMatrix_reindex 1009 originalRows selectedRows inverseSelectedColumns
    selectedColumns columns_left_inverse columns_right_inverse

/-- The selected square minor has full rank. -/
theorem target_rank : (residueMatrix 1009 targetRows).rank = 542 := by
  have hr := full_column_rank_of_lower_upper (residueMatrix 1009 targetRows) id id
    (residueMatrix 1009 lowerRows) (residueMatrix 1009 upperRows) factorization.symm
    (lower_of_support 1009 lowerRows lower_support)
    (upper_of_support 1009 upperRows upper_support)
    (diagonal_ne_zero 1009 lowerRows lower_diagonal)
    (diagonal_ne_zero 1009 upperRows upper_diagonal)
  simpa only [Fintype.card_fin] using hr

/-- The listed C2 multiplication matrix has full column rank. -/
theorem original_rank : (residueMatrix 1009 originalRows).rank = 542 := by
  have hr := full_column_rank_of_lower_upper (residueMatrix 1009 originalRows)
    selectedRows selectedColumns (residueMatrix 1009 lowerRows) (residueMatrix 1009 upperRows)
    (target_is_minor.symm.trans factorization.symm)
    (lower_of_support 1009 lowerRows lower_support)
    (upper_of_support 1009 upperRows upper_support)
    (diagonal_ne_zero 1009 lowerRows lower_diagonal)
    (diagonal_ne_zero 1009 upperRows upper_diagonal)
  simpa only [Fintype.card_fin] using hr

#print axioms factorization
#print axioms target_rank
#print axioms original_rank
end CertifiedRank.C2.PackedCertificate
