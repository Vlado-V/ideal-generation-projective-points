module

public import IdealGeneration.CertifiedSparseRow
public import IdealGeneration.CubicInitialDataColumns

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedRank.C2

noncomputable def selectedRowsVector : Vector (Fin 650) 542 :=
  #v[
    row594, row615, row630, row640, row646, row649, row391, row400, row524, row563, row521, row525,
    row526, row558, row561, row564, row39, row48, row491, row536, row506, row512, row517, row543,
    row549, row554, row446, row455, row499, row500, row597, row598, row612, row641, row588, row591,
    row609, row617, row618, row624, row627, row631, row632, row634, row637, row642, row643, row645,
    row647, row648, row595, row596, row599, row584, row593, row600, row605, row614, row616, row619,
    row620, row629, row633, row639, row610, row585, row586, row589, row590, row592, row602, row603,
    row606, row607, row611, row613, row621, row622, row625, row626, row628, row635, row636, row638,
    row644, row587, row601, row604, row608, row623, row199, row485, row244, row530, row144, row430,
    row366, row367, row385, row394, row3, row4, row393, row401, row527, row560, row562, row522,
    row528, row557, row365, row375, row2, row23, row479, row384, row482, row520, row529, row556,
    row565, row480, row481, row483, row114, row105, row386, row498, row511, row551, row387, row389,
    row395, row547, row98, row475, row463, row469, row470, row474, row478, row507, row513, row518,
    row462, row468, row473, row477, row447, row542, row548, row553, row467, row454, row461, row250,
    row272, row508, row514, row519, row544, row550, row555, row108, row15, row205, row240, row99,
    row14, row456, row448, row501, row572, row445, row0, row569, row578, row583, row329, row579,
    row582, row575, row453, row486, row494, row34, row431, row308, row577, row443, row432, row451,
    row452, row376, row571, row364, row415, row429, row484, row438, row523, row570, row333, row409,
    row314, row330, row559, row7, row63, row313, row347, row310, row344, row399, row8, row315,
    row346, row322, row337, row68, row64, row361, row318, row332, row392, row363, row423, row312,
    row419, row345, row356, row416, row580, row411, row414, row331, row427, row352, row342, row77,
    row11, row67, row59, row57, row6, row71, row10, row70, row66, row55, row53, row5,
    row574, row311, row336, row327, row410, row58, row60, row9, row65, row62, row321, row317,
    row350, row340, row573, row335, row325, row439, row545, row552, row320, row509, row424, row316,
    row546, row355, row576, row13, row27, row471, row476, row464, row472, row535, row110, row113,
    row489, row41, row36, row353, row465, row466, row358, row115, row45, row534, row398, row539,
    row531, row538, row49, row396, row397, row111, row532, row112, row275, row268, row263, row109,
    row540, row541, row449, row377, row450, row343, row328, row388, row103, row390, row487, row35,
    row502, row510, row107, row102, row106, row492, row490, row515, row104, row516, row503, row504,
    row505, row441, row226, row239, row231, row444, row90, row360, row428, row349, row324, row339,
    row362, row422, row418, row413, row354, row426, row319, row309, row359, row292, row412, row293,
    row290, row294, row295, row303, row304, row291, row288, row300, row306, row297, row301, row299,
    row289, row296, row284, row307, row298, row281, row326, row334, row75, row417, row323, row421,
    row341, row436, row434, row435, row437, row381, row229, row457, row26, row28, row29, row383,
    row96, row382, row94, row379, row97, row233, row191, row221, row581, row351, row76, row61,
    row338, row425, row88, row407, row265, row190, row497, row51, row186, row210, row197, row117,
    row148, row236, row442, row241, row188, row279, row212, row252, row433, row230, row286, row182,
    row267, row280, row173, row153, row262, row246, row92, row207, row145, row218, row403, row204,
    row169, row160, row189, row193, row264, row177, row225, row121, row134, row38, row116, row238,
    row287, row282, row458, row440, row255, row405, row283, row496, row237, row215, row357, row459,
    row187, row402, row166, row69, row235, row495, row217, row152, row147, row157, row276, row278,
    row162, row25, row159, row52, row146, row271, row118, row273, row254, row285, row149, row213,
    row249, row214, row176, row232, row269, row122, row460, row260, row220, row202, row167, row216,
    row120, row161, row175, row208, row95, row266, row158, row164, row228, row194, row256, row183,
    row227, row195, row209, row165, row270, row222, row253, row170, row168, row172, row181, row179,
    row180, row224, row155, row261, row185, row219, row54, row174, row211, row257, row192, row242,
    row258, row156
  ]

noncomputable def selectedRows : Fin 542 → Fin 650 :=
  selectedRowsVector.get

noncomputable def selectedColumnsVector : Vector (Fin 542) 542 :=
  #v[
    column231, column273, column314, column354, column393, column431, column40, column45, column328, column369, column292, column364,
    column400, column297, column333, column405, column4, column9, column112, column153, column184, column220, column256, column189,
    column225, column261, column76, column81, column148, column117, column339, column375, column379, column390, column336, column373,
    column342, column345, column381, column347, column384, column350, column386, column351, column388, column356, column357, column359,
    column394, column395, column267, column303, column411, column206, column215, column237, column242, column251, column274, column277,
    column278, column287, column317, column323, column343, column335, column371, column337, column338, column374, column340, column376,
    column341, column377, column344, column380, column346, column382, column348, column349, column385, column352, column353, column389,
    column358, column209, column238, column241, column245, column281, column111, column113, column151, column152, column72, column74,
    column39, column43, column114, column154, column3, column10, column399, column403, column365, column332, column334, column363,
    column366, column331, column36, column37, column0, column1, column324, column38, column361, column291, column402, column295,
    column406, column325, column326, column362, column367, column327, column149, column147, column219, column259, column183, column255,
    column187, column223, column2, column288, column182, column218, column252, column254, column290, column185, column221, column257,
    column181, column217, column253, column289, column77, column188, column224, column260, column216, column80, column180, column368,
    column370, column186, column222, column258, column190, column226, column262, column8, column7, column329, column330, column6,
    column5, column82, column78, column150, column194, column110, column19, column191, column200, column205, column263, column264,
    column265, column197, column144, column116, column115, column118, column109, column228, column229, column108, column145, column146,
    column79, column75, column193, column62, column57, column71, column107, column73, column294, column192, column476, column51,
    column452, column467, column298, column29, column24, column466, column482, column457, column299, column44, column33, column453,
    column480, column460, column470, column21, column18, column486, column456, column474, column41, column407, column65, column464,
    column61, column477, column485, column58, column302, column53, column56, column471, column69, column481, column475, column22,
    column25, column17, column20, column16, column15, column13, column34, column31, column28, column14, column11, column12,
    column201, column461, column469, column465, column52, column27, column30, column23, column32, column26, column459, column455,
    column479, column473, column195, column468, column463, column360, column159, column166, column458, column128, column66, column454,
    column161, column483, column198, column397, column396, column94, column99, column87, column95, column296, column46, column404,
    column293, column42, column401, column537, column88, column89, column484, column176, column163, column165, column157, column155,
    column156, column158, column172, column173, column170, column169, column171, column177, column168, column178, column175, column164,
    column160, column167, column174, column162, column179, column531, column515, column125, column138, column121, column122, column120,
    column119, column136, column142, column143, column133, column134, column135, column130, column137, column123, column129, column124,
    column127, column140, column131, column139, column126, column141, column132, column213, column70, column478, column462, column472,
    column529, column64, column60, column55, column372, column68, column308, column522, column513, column436, column54, column437,
    column434, column438, column439, column447, column448, column435, column432, column444, column450, column441, column445, column443,
    column433, column440, column446, column451, column442, column449, column514, column306, column35, column59, column516, column63,
    column536, column90, column104, column96, column103, column83, column84, column85, column86, column98, column398, column102,
    column100, column106, column91, column101, column105, column92, column93, column97, column203, column307, column322, column519,
    column285, column67, column47, column49, column48, column50, column202, column212, column503, column491, column300, column214,
    column490, column409, column410, column493, column408, column210, column494, column496, column492, column488, column199, column501,
    column211, column487, column196, column301, column204, column502, column208, column230, column227, column207, column266, column489,
    column497, column495, column506, column498, column499, column500, column504, column505, column415, column392, column533, column315,
    column279, column240, column387, column309, column235, column246, column282, column305, column429, column427, column312, column419,
    column541, column414, column310, column391, column239, column272, column430, column269, column518, column268, column284, column249,
    column421, column247, column412, column234, column378, column525, column428, column271, column316, column417, column420, column286,
    column422, column321, column318, column270, column244, column524, column283, column539, column424, column425, column250, column416,
    column319, column320, column517, column507, column508, column509, column510, column511, column512, column311, column418, column426,
    column248, column236, column243, column233, column520, column521, column355, column523, column276, column232, column526, column527,
    column538, column304, column530, column423, column532, column275, column534, column535, column313, column280, column528, column383,
    column540, column413
  ]

noncomputable def selectedColumns : Fin 542 → Fin 542 :=
  selectedColumnsVector.get

noncomputable def inverseSelectedColumnsVector : Vector (Fin 542) 542 :=
  #v[
    column112, column113, column134, column100, column16, column168, column167, column164, column163, column17, column101, column250,
    column251, column245, column249, column244, column243, column241, column220, column174, column242, column219, column239, column259,
    column208, column240, column261, column257, column248, column207, column258, column247, column260, column214, column246, column380,
    column110, column111, column115, column96, column6, column224, column289, column97, column213, column7, column286, column410,
    column412, column411, column413, column203, column256, column233, column358, column351, column234, column196, column231, column381,
    column350, column228, column195, column383, column349, column226, column274, column409, column353, column236, column344, column197,
    column94, column199, column95, column193, column26, column148, column170, column192, column153, column27, column169, column389,
    column390, column391, column392, column283, column292, column293, column385, column398, column401, column402, column281, column284,
    column387, column403, column393, column282, column396, column399, column395, column388, column386, column400, column397, column198,
    column189, column186, column173, column90, column18, column91, column98, column184, column183, column29, column185, column324,
    column323, column321, column322, column333, column335, column319, column340, column336, column273, column334, column331, column338,
    column342, column328, column329, column330, column325, column332, column320, column339, column337, column341, column326, column327,
    column182, column190, column191, column127, column28, column126, column171, column92, column93, column19, column99, column299,
    column300, column298, column301, column270, column312, column276, column315, column296, column311, column297, column271, column313,
    column308, column305, column304, column306, column302, column303, column314, column310, column295, column307, column309, column316,
    column154, column144, column136, column130, column20, column141, column157, column132, column149, column23, column160, column175,
    column201, column194, column172, column266, column434, column181, column278, column430, column176, column252, column414, column404,
    column436, column177, column53, column441, column438, column85, column425, column432, column415, column343, column419, column54,
    column152, column145, column137, column128, column21, column142, column158, column133, column150, column24, column161, column440,
    column187, column188, column439, column0, column525, column519, column483, column460, column517, column55, column86, column472,
    column457, column87, column56, column518, column496, column88, column461, column481, column516, column479, column502, column57,
    column138, column146, column139, column131, column22, column143, column159, column129, column151, column25, column162, column178,
    column179, column180, column442, column50, column477, column475, column495, column487, column473, column1, column58, column533,
    column524, column59, column60, column456, column537, column89, column462, column498, column478, column408, column491, column61,
    column135, column147, column140, column117, column10, column288, column200, column119, column285, column13, column206, column212,
    column418, column435, column232, column51, column529, column463, column379, column405, column354, column459, column470, column513,
    column466, column536, column2, column455, column488, column62, column494, column504, column505, column493, column406, column63,
    column114, column121, column122, column125, column8, column165, column166, column109, column105, column14, column106, column65,
    column34, column67, column68, column30, column70, column72, column36, column64, column74, column37, column76, column39,
    column78, column79, column41, column43, column81, column82, column3, column522, column45, column46, column84, column47,
    column269, column116, column123, column107, column11, column104, column108, column124, column155, column9, column156, column66,
    column352, column35, column69, column31, column71, column73, column484, column32, column75, column38, column77, column539,
    column40, column80, column42, column458, column44, column83, column33, column471, column453, column4, column48, column49,
    column280, column279, column394, column102, column12, column290, column118, column103, column287, column15, column120, column225,
    column424, column421, column422, column52, column482, column541, column469, column452, column503, column489, column514, column467,
    column490, column480, column492, column531, column500, column501, column515, column465, column486, column464, column474, column5,
    column366, column372, column360, column365, column357, column359, column361, column362, column373, column369, column376, column371,
    column367, column370, column374, column363, column364, column377, column368, column375, column204, column215, column275, column263,
    column222, column211, column272, column262, column217, column253, column346, column268, column227, column255, column209, column205,
    column267, column254, column218, column235, column347, column265, column223, column238, column202, column229, column345, column264,
    column216, column237, column210, column277, column294, column230, column221, column433, column429, column443, column420, column417,
    column428, column423, column426, column445, column427, column444, column447, column448, column449, column431, column437, column416,
    column450, column451, column446, column507, column508, column509, column510, column511, column512, column356, column378, column318,
    column382, column506, column476, column407, column520, column521, column355, column523, column497, column485, column526, column527,
    column538, column348, column530, column317, column532, column454, column534, column535, column384, column291, column528, column499,
    column540, column468
  ]

noncomputable def inverseSelectedColumns : Fin 542 → Fin 542 :=
  inverseSelectedColumnsVector.get

end CertifiedRank.C2
