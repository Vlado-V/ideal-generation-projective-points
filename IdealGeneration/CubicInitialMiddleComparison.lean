module

public import IdealGeneration.CubicInitialMiddleChecks000
public import IdealGeneration.CubicInitialMiddleChecks032
public import IdealGeneration.CubicInitialMiddleChecks064
public import IdealGeneration.CubicInitialMiddleChecks096
public import IdealGeneration.CubicInitialMiddleChecks128
public import IdealGeneration.CubicInitialMiddleChecks160
public import IdealGeneration.CubicInitialMiddleChecks192
public import IdealGeneration.CubicInitialMiddleChecks224
public import IdealGeneration.CubicInitialMiddleChecks256
public import IdealGeneration.CubicInitialMiddleChecks288
public import IdealGeneration.CubicInitialMiddleChecks320
public import IdealGeneration.CubicInitialMiddleChecks352
public import IdealGeneration.CubicInitialMiddleChecks384
public import IdealGeneration.CubicInitialMiddleChecks416
public import IdealGeneration.CubicInitialMiddleChecks448
public import IdealGeneration.CubicInitialMiddleChecks480
public import IdealGeneration.CubicInitialMiddleChecks512
public import IdealGeneration.CubicInitialMiddleChecks544
public import IdealGeneration.CubicInitialMiddleChecks576
public import IdealGeneration.CubicInitialMiddleChecks608
public import IdealGeneration.CubicInitialMiddleChecks640
public import IdealGeneration.CertifiedFinCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 2048

namespace IdealGeneration.CubicInitial
open ConeMonomialChart CertifiedRank

theorem middleRowCertificateAll : ∀ i, MiddleRowCertificate i := by
  refine forall_fin_of_rows (n := 650) ?_
  exact ⟨
    middleRowCertificate000, middleRowCertificate001, middleRowCertificate002,
    middleRowCertificate003, middleRowCertificate004, middleRowCertificate005,
    middleRowCertificate006, middleRowCertificate007, middleRowCertificate008,
    middleRowCertificate009, middleRowCertificate010, middleRowCertificate011,
    middleRowCertificate012, middleRowCertificate013, middleRowCertificate014,
    middleRowCertificate015, middleRowCertificate016, middleRowCertificate017,
    middleRowCertificate018, middleRowCertificate019, middleRowCertificate020,
    middleRowCertificate021, middleRowCertificate022, middleRowCertificate023,
    middleRowCertificate024, middleRowCertificate025, middleRowCertificate026,
    middleRowCertificate027, middleRowCertificate028, middleRowCertificate029,
    middleRowCertificate030, middleRowCertificate031, middleRowCertificate032,
    middleRowCertificate033, middleRowCertificate034, middleRowCertificate035,
    middleRowCertificate036, middleRowCertificate037, middleRowCertificate038,
    middleRowCertificate039, middleRowCertificate040, middleRowCertificate041,
    middleRowCertificate042, middleRowCertificate043, middleRowCertificate044,
    middleRowCertificate045, middleRowCertificate046, middleRowCertificate047,
    middleRowCertificate048, middleRowCertificate049, middleRowCertificate050,
    middleRowCertificate051, middleRowCertificate052, middleRowCertificate053,
    middleRowCertificate054, middleRowCertificate055, middleRowCertificate056,
    middleRowCertificate057, middleRowCertificate058, middleRowCertificate059,
    middleRowCertificate060, middleRowCertificate061, middleRowCertificate062,
    middleRowCertificate063, middleRowCertificate064, middleRowCertificate065,
    middleRowCertificate066, middleRowCertificate067, middleRowCertificate068,
    middleRowCertificate069, middleRowCertificate070, middleRowCertificate071,
    middleRowCertificate072, middleRowCertificate073, middleRowCertificate074,
    middleRowCertificate075, middleRowCertificate076, middleRowCertificate077,
    middleRowCertificate078, middleRowCertificate079, middleRowCertificate080,
    middleRowCertificate081, middleRowCertificate082, middleRowCertificate083,
    middleRowCertificate084, middleRowCertificate085, middleRowCertificate086,
    middleRowCertificate087, middleRowCertificate088, middleRowCertificate089,
    middleRowCertificate090, middleRowCertificate091, middleRowCertificate092,
    middleRowCertificate093, middleRowCertificate094, middleRowCertificate095,
    middleRowCertificate096, middleRowCertificate097, middleRowCertificate098,
    middleRowCertificate099, middleRowCertificate100, middleRowCertificate101,
    middleRowCertificate102, middleRowCertificate103, middleRowCertificate104,
    middleRowCertificate105, middleRowCertificate106, middleRowCertificate107,
    middleRowCertificate108, middleRowCertificate109, middleRowCertificate110,
    middleRowCertificate111, middleRowCertificate112, middleRowCertificate113,
    middleRowCertificate114, middleRowCertificate115, middleRowCertificate116,
    middleRowCertificate117, middleRowCertificate118, middleRowCertificate119,
    middleRowCertificate120, middleRowCertificate121, middleRowCertificate122,
    middleRowCertificate123, middleRowCertificate124, middleRowCertificate125,
    middleRowCertificate126, middleRowCertificate127, middleRowCertificate128,
    middleRowCertificate129, middleRowCertificate130, middleRowCertificate131,
    middleRowCertificate132, middleRowCertificate133, middleRowCertificate134,
    middleRowCertificate135, middleRowCertificate136, middleRowCertificate137,
    middleRowCertificate138, middleRowCertificate139, middleRowCertificate140,
    middleRowCertificate141, middleRowCertificate142, middleRowCertificate143,
    middleRowCertificate144, middleRowCertificate145, middleRowCertificate146,
    middleRowCertificate147, middleRowCertificate148, middleRowCertificate149,
    middleRowCertificate150, middleRowCertificate151, middleRowCertificate152,
    middleRowCertificate153, middleRowCertificate154, middleRowCertificate155,
    middleRowCertificate156, middleRowCertificate157, middleRowCertificate158,
    middleRowCertificate159, middleRowCertificate160, middleRowCertificate161,
    middleRowCertificate162, middleRowCertificate163, middleRowCertificate164,
    middleRowCertificate165, middleRowCertificate166, middleRowCertificate167,
    middleRowCertificate168, middleRowCertificate169, middleRowCertificate170,
    middleRowCertificate171, middleRowCertificate172, middleRowCertificate173,
    middleRowCertificate174, middleRowCertificate175, middleRowCertificate176,
    middleRowCertificate177, middleRowCertificate178, middleRowCertificate179,
    middleRowCertificate180, middleRowCertificate181, middleRowCertificate182,
    middleRowCertificate183, middleRowCertificate184, middleRowCertificate185,
    middleRowCertificate186, middleRowCertificate187, middleRowCertificate188,
    middleRowCertificate189, middleRowCertificate190, middleRowCertificate191,
    middleRowCertificate192, middleRowCertificate193, middleRowCertificate194,
    middleRowCertificate195, middleRowCertificate196, middleRowCertificate197,
    middleRowCertificate198, middleRowCertificate199, middleRowCertificate200,
    middleRowCertificate201, middleRowCertificate202, middleRowCertificate203,
    middleRowCertificate204, middleRowCertificate205, middleRowCertificate206,
    middleRowCertificate207, middleRowCertificate208, middleRowCertificate209,
    middleRowCertificate210, middleRowCertificate211, middleRowCertificate212,
    middleRowCertificate213, middleRowCertificate214, middleRowCertificate215,
    middleRowCertificate216, middleRowCertificate217, middleRowCertificate218,
    middleRowCertificate219, middleRowCertificate220, middleRowCertificate221,
    middleRowCertificate222, middleRowCertificate223, middleRowCertificate224,
    middleRowCertificate225, middleRowCertificate226, middleRowCertificate227,
    middleRowCertificate228, middleRowCertificate229, middleRowCertificate230,
    middleRowCertificate231, middleRowCertificate232, middleRowCertificate233,
    middleRowCertificate234, middleRowCertificate235, middleRowCertificate236,
    middleRowCertificate237, middleRowCertificate238, middleRowCertificate239,
    middleRowCertificate240, middleRowCertificate241, middleRowCertificate242,
    middleRowCertificate243, middleRowCertificate244, middleRowCertificate245,
    middleRowCertificate246, middleRowCertificate247, middleRowCertificate248,
    middleRowCertificate249, middleRowCertificate250, middleRowCertificate251,
    middleRowCertificate252, middleRowCertificate253, middleRowCertificate254,
    middleRowCertificate255, middleRowCertificate256, middleRowCertificate257,
    middleRowCertificate258, middleRowCertificate259, middleRowCertificate260,
    middleRowCertificate261, middleRowCertificate262, middleRowCertificate263,
    middleRowCertificate264, middleRowCertificate265, middleRowCertificate266,
    middleRowCertificate267, middleRowCertificate268, middleRowCertificate269,
    middleRowCertificate270, middleRowCertificate271, middleRowCertificate272,
    middleRowCertificate273, middleRowCertificate274, middleRowCertificate275,
    middleRowCertificate276, middleRowCertificate277, middleRowCertificate278,
    middleRowCertificate279, middleRowCertificate280, middleRowCertificate281,
    middleRowCertificate282, middleRowCertificate283, middleRowCertificate284,
    middleRowCertificate285, middleRowCertificate286, middleRowCertificate287,
    middleRowCertificate288, middleRowCertificate289, middleRowCertificate290,
    middleRowCertificate291, middleRowCertificate292, middleRowCertificate293,
    middleRowCertificate294, middleRowCertificate295, middleRowCertificate296,
    middleRowCertificate297, middleRowCertificate298, middleRowCertificate299,
    middleRowCertificate300, middleRowCertificate301, middleRowCertificate302,
    middleRowCertificate303, middleRowCertificate304, middleRowCertificate305,
    middleRowCertificate306, middleRowCertificate307, middleRowCertificate308,
    middleRowCertificate309, middleRowCertificate310, middleRowCertificate311,
    middleRowCertificate312, middleRowCertificate313, middleRowCertificate314,
    middleRowCertificate315, middleRowCertificate316, middleRowCertificate317,
    middleRowCertificate318, middleRowCertificate319, middleRowCertificate320,
    middleRowCertificate321, middleRowCertificate322, middleRowCertificate323,
    middleRowCertificate324, middleRowCertificate325, middleRowCertificate326,
    middleRowCertificate327, middleRowCertificate328, middleRowCertificate329,
    middleRowCertificate330, middleRowCertificate331, middleRowCertificate332,
    middleRowCertificate333, middleRowCertificate334, middleRowCertificate335,
    middleRowCertificate336, middleRowCertificate337, middleRowCertificate338,
    middleRowCertificate339, middleRowCertificate340, middleRowCertificate341,
    middleRowCertificate342, middleRowCertificate343, middleRowCertificate344,
    middleRowCertificate345, middleRowCertificate346, middleRowCertificate347,
    middleRowCertificate348, middleRowCertificate349, middleRowCertificate350,
    middleRowCertificate351, middleRowCertificate352, middleRowCertificate353,
    middleRowCertificate354, middleRowCertificate355, middleRowCertificate356,
    middleRowCertificate357, middleRowCertificate358, middleRowCertificate359,
    middleRowCertificate360, middleRowCertificate361, middleRowCertificate362,
    middleRowCertificate363, middleRowCertificate364, middleRowCertificate365,
    middleRowCertificate366, middleRowCertificate367, middleRowCertificate368,
    middleRowCertificate369, middleRowCertificate370, middleRowCertificate371,
    middleRowCertificate372, middleRowCertificate373, middleRowCertificate374,
    middleRowCertificate375, middleRowCertificate376, middleRowCertificate377,
    middleRowCertificate378, middleRowCertificate379, middleRowCertificate380,
    middleRowCertificate381, middleRowCertificate382, middleRowCertificate383,
    middleRowCertificate384, middleRowCertificate385, middleRowCertificate386,
    middleRowCertificate387, middleRowCertificate388, middleRowCertificate389,
    middleRowCertificate390, middleRowCertificate391, middleRowCertificate392,
    middleRowCertificate393, middleRowCertificate394, middleRowCertificate395,
    middleRowCertificate396, middleRowCertificate397, middleRowCertificate398,
    middleRowCertificate399, middleRowCertificate400, middleRowCertificate401,
    middleRowCertificate402, middleRowCertificate403, middleRowCertificate404,
    middleRowCertificate405, middleRowCertificate406, middleRowCertificate407,
    middleRowCertificate408, middleRowCertificate409, middleRowCertificate410,
    middleRowCertificate411, middleRowCertificate412, middleRowCertificate413,
    middleRowCertificate414, middleRowCertificate415, middleRowCertificate416,
    middleRowCertificate417, middleRowCertificate418, middleRowCertificate419,
    middleRowCertificate420, middleRowCertificate421, middleRowCertificate422,
    middleRowCertificate423, middleRowCertificate424, middleRowCertificate425,
    middleRowCertificate426, middleRowCertificate427, middleRowCertificate428,
    middleRowCertificate429, middleRowCertificate430, middleRowCertificate431,
    middleRowCertificate432, middleRowCertificate433, middleRowCertificate434,
    middleRowCertificate435, middleRowCertificate436, middleRowCertificate437,
    middleRowCertificate438, middleRowCertificate439, middleRowCertificate440,
    middleRowCertificate441, middleRowCertificate442, middleRowCertificate443,
    middleRowCertificate444, middleRowCertificate445, middleRowCertificate446,
    middleRowCertificate447, middleRowCertificate448, middleRowCertificate449,
    middleRowCertificate450, middleRowCertificate451, middleRowCertificate452,
    middleRowCertificate453, middleRowCertificate454, middleRowCertificate455,
    middleRowCertificate456, middleRowCertificate457, middleRowCertificate458,
    middleRowCertificate459, middleRowCertificate460, middleRowCertificate461,
    middleRowCertificate462, middleRowCertificate463, middleRowCertificate464,
    middleRowCertificate465, middleRowCertificate466, middleRowCertificate467,
    middleRowCertificate468, middleRowCertificate469, middleRowCertificate470,
    middleRowCertificate471, middleRowCertificate472, middleRowCertificate473,
    middleRowCertificate474, middleRowCertificate475, middleRowCertificate476,
    middleRowCertificate477, middleRowCertificate478, middleRowCertificate479,
    middleRowCertificate480, middleRowCertificate481, middleRowCertificate482,
    middleRowCertificate483, middleRowCertificate484, middleRowCertificate485,
    middleRowCertificate486, middleRowCertificate487, middleRowCertificate488,
    middleRowCertificate489, middleRowCertificate490, middleRowCertificate491,
    middleRowCertificate492, middleRowCertificate493, middleRowCertificate494,
    middleRowCertificate495, middleRowCertificate496, middleRowCertificate497,
    middleRowCertificate498, middleRowCertificate499, middleRowCertificate500,
    middleRowCertificate501, middleRowCertificate502, middleRowCertificate503,
    middleRowCertificate504, middleRowCertificate505, middleRowCertificate506,
    middleRowCertificate507, middleRowCertificate508, middleRowCertificate509,
    middleRowCertificate510, middleRowCertificate511, middleRowCertificate512,
    middleRowCertificate513, middleRowCertificate514, middleRowCertificate515,
    middleRowCertificate516, middleRowCertificate517, middleRowCertificate518,
    middleRowCertificate519, middleRowCertificate520, middleRowCertificate521,
    middleRowCertificate522, middleRowCertificate523, middleRowCertificate524,
    middleRowCertificate525, middleRowCertificate526, middleRowCertificate527,
    middleRowCertificate528, middleRowCertificate529, middleRowCertificate530,
    middleRowCertificate531, middleRowCertificate532, middleRowCertificate533,
    middleRowCertificate534, middleRowCertificate535, middleRowCertificate536,
    middleRowCertificate537, middleRowCertificate538, middleRowCertificate539,
    middleRowCertificate540, middleRowCertificate541, middleRowCertificate542,
    middleRowCertificate543, middleRowCertificate544, middleRowCertificate545,
    middleRowCertificate546, middleRowCertificate547, middleRowCertificate548,
    middleRowCertificate549, middleRowCertificate550, middleRowCertificate551,
    middleRowCertificate552, middleRowCertificate553, middleRowCertificate554,
    middleRowCertificate555, middleRowCertificate556, middleRowCertificate557,
    middleRowCertificate558, middleRowCertificate559, middleRowCertificate560,
    middleRowCertificate561, middleRowCertificate562, middleRowCertificate563,
    middleRowCertificate564, middleRowCertificate565, middleRowCertificate566,
    middleRowCertificate567, middleRowCertificate568, middleRowCertificate569,
    middleRowCertificate570, middleRowCertificate571, middleRowCertificate572,
    middleRowCertificate573, middleRowCertificate574, middleRowCertificate575,
    middleRowCertificate576, middleRowCertificate577, middleRowCertificate578,
    middleRowCertificate579, middleRowCertificate580, middleRowCertificate581,
    middleRowCertificate582, middleRowCertificate583, middleRowCertificate584,
    middleRowCertificate585, middleRowCertificate586, middleRowCertificate587,
    middleRowCertificate588, middleRowCertificate589, middleRowCertificate590,
    middleRowCertificate591, middleRowCertificate592, middleRowCertificate593,
    middleRowCertificate594, middleRowCertificate595, middleRowCertificate596,
    middleRowCertificate597, middleRowCertificate598, middleRowCertificate599,
    middleRowCertificate600, middleRowCertificate601, middleRowCertificate602,
    middleRowCertificate603, middleRowCertificate604, middleRowCertificate605,
    middleRowCertificate606, middleRowCertificate607, middleRowCertificate608,
    middleRowCertificate609, middleRowCertificate610, middleRowCertificate611,
    middleRowCertificate612, middleRowCertificate613, middleRowCertificate614,
    middleRowCertificate615, middleRowCertificate616, middleRowCertificate617,
    middleRowCertificate618, middleRowCertificate619, middleRowCertificate620,
    middleRowCertificate621, middleRowCertificate622, middleRowCertificate623,
    middleRowCertificate624, middleRowCertificate625, middleRowCertificate626,
    middleRowCertificate627, middleRowCertificate628, middleRowCertificate629,
    middleRowCertificate630, middleRowCertificate631, middleRowCertificate632,
    middleRowCertificate633, middleRowCertificate634, middleRowCertificate635,
    middleRowCertificate636, middleRowCertificate637, middleRowCertificate638,
    middleRowCertificate639, middleRowCertificate640, middleRowCertificate641,
    middleRowCertificate642, middleRowCertificate643, middleRowCertificate644,
    middleRowCertificate645, middleRowCertificate646, middleRowCertificate647,
    middleRowCertificate648, middleRowCertificate649
  ⟩

theorem normalLookupCheckAll (i : Fin 650) :
    ∀ j : Fin 12, NormalLookupValid (c := 2) (m := 10)
      normalExponent (quarticExponent i) j (normalLookup i j) :=
  (middleRowCertificateAll i).normalLookupValid

theorem traceLookupCheckAll (i : Fin 650) :
    ∀ j, TraceLookupValid (c := 2) (m := 10)
      traceExponent (quarticExponent i) j (traceLookup i j) :=
  (middleRowCertificateAll i).traceLookupValid

theorem middleRowCheckAll (i : Fin 650) :
    rawMiddleRow i = CertifiedRank.C2.originalRows i :=
  (middleRowCertificateAll i).rowMatches

end IdealGeneration.CubicInitial
