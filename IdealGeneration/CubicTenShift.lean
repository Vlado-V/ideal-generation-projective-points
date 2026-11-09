module

public import IdealGeneration.CubicTenGeometry
public import IdealGeneration.ConeLookupGuards

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Verified predecessor lookups in the selected cubic middle rows. -/

noncomputable section
namespace IdealGeneration.CubicTen
open ConeMonomialChart CubicTenPackedData Matrix
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

private def lookupValidAt (i : Fin 310) : Prop :=
  (∀ j : Fin 10, NormalLookupValid (c := 2) (m := 8) normalExponent (quarticExponent i) j
    (normalLookup i j)) ∧
  (∀ j : Fin 2, TraceLookupValid (c := 2) (m := 8) traceExponent (quarticExponent i) j
    (traceLookup i j))

private instance lookupValidAtDecidable (i : Fin 310) : Decidable (lookupValidAt i) := by
  unfold lookupValidAt
  letI : Decidable (∀ j : Fin 10,
      NormalLookupValid (c := 2) (m := 8) normalExponent (quarticExponent i) j
        (normalLookup i j)) :=
    @Fintype.decidableForallFintype (Fin 10) _ (fun j =>
      normalLookupValidDecidable (c := 2) (m := 8) normalExponent (quarticExponent i) j
        (normalLookup i j)) inferInstance
  letI : Decidable (∀ j : Fin 2,
      TraceLookupValid (c := 2) (m := 8) traceExponent (quarticExponent i) j
        (traceLookup i j)) :=
    @Fintype.decidableForallFintype (Fin 2) _ (fun j =>
      traceLookupValidDecidable (c := 2) (m := 8) traceExponent (quarticExponent i) j
        (traceLookup i j)) inferInstance
  infer_instance

private theorem lookupValid000 : lookupValidAt (0 : Fin 310) := by decide +kernel
private theorem lookupValid001 : lookupValidAt (1 : Fin 310) := by decide +kernel
private theorem lookupValid002 : lookupValidAt (2 : Fin 310) := by decide +kernel
private theorem lookupValid003 : lookupValidAt (3 : Fin 310) := by decide +kernel
private theorem lookupValid004 : lookupValidAt (4 : Fin 310) := by decide +kernel
private theorem lookupValid005 : lookupValidAt (5 : Fin 310) := by decide +kernel
private theorem lookupValid006 : lookupValidAt (6 : Fin 310) := by decide +kernel
private theorem lookupValid007 : lookupValidAt (7 : Fin 310) := by decide +kernel
private theorem lookupValid008 : lookupValidAt (8 : Fin 310) := by decide +kernel
private theorem lookupValid009 : lookupValidAt (9 : Fin 310) := by decide +kernel
private theorem lookupValid010 : lookupValidAt (10 : Fin 310) := by decide +kernel
private theorem lookupValid011 : lookupValidAt (11 : Fin 310) := by decide +kernel
private theorem lookupValid012 : lookupValidAt (12 : Fin 310) := by decide +kernel
private theorem lookupValid013 : lookupValidAt (13 : Fin 310) := by decide +kernel
private theorem lookupValid014 : lookupValidAt (14 : Fin 310) := by decide +kernel
private theorem lookupValid015 : lookupValidAt (15 : Fin 310) := by decide +kernel
private theorem lookupValid016 : lookupValidAt (16 : Fin 310) := by decide +kernel
private theorem lookupValid017 : lookupValidAt (17 : Fin 310) := by decide +kernel
private theorem lookupValid018 : lookupValidAt (18 : Fin 310) := by decide +kernel
private theorem lookupValid019 : lookupValidAt (19 : Fin 310) := by decide +kernel
private theorem lookupValid020 : lookupValidAt (20 : Fin 310) := by decide +kernel
private theorem lookupValid021 : lookupValidAt (21 : Fin 310) := by decide +kernel
private theorem lookupValid022 : lookupValidAt (22 : Fin 310) := by decide +kernel
private theorem lookupValid023 : lookupValidAt (23 : Fin 310) := by decide +kernel
private theorem lookupValid024 : lookupValidAt (24 : Fin 310) := by decide +kernel
private theorem lookupValid025 : lookupValidAt (25 : Fin 310) := by decide +kernel
private theorem lookupValid026 : lookupValidAt (26 : Fin 310) := by decide +kernel
private theorem lookupValid027 : lookupValidAt (27 : Fin 310) := by decide +kernel
private theorem lookupValid028 : lookupValidAt (28 : Fin 310) := by decide +kernel
private theorem lookupValid029 : lookupValidAt (29 : Fin 310) := by decide +kernel
private theorem lookupValid030 : lookupValidAt (30 : Fin 310) := by decide +kernel
private theorem lookupValid031 : lookupValidAt (31 : Fin 310) := by decide +kernel
private theorem lookupValid032 : lookupValidAt (32 : Fin 310) := by decide +kernel
private theorem lookupValid033 : lookupValidAt (33 : Fin 310) := by decide +kernel
private theorem lookupValid034 : lookupValidAt (34 : Fin 310) := by decide +kernel
private theorem lookupValid035 : lookupValidAt (35 : Fin 310) := by decide +kernel
private theorem lookupValid036 : lookupValidAt (36 : Fin 310) := by decide +kernel
private theorem lookupValid037 : lookupValidAt (37 : Fin 310) := by decide +kernel
private theorem lookupValid038 : lookupValidAt (38 : Fin 310) := by decide +kernel
private theorem lookupValid039 : lookupValidAt (39 : Fin 310) := by decide +kernel
private theorem lookupValid040 : lookupValidAt (40 : Fin 310) := by decide +kernel
private theorem lookupValid041 : lookupValidAt (41 : Fin 310) := by decide +kernel
private theorem lookupValid042 : lookupValidAt (42 : Fin 310) := by decide +kernel
private theorem lookupValid043 : lookupValidAt (43 : Fin 310) := by decide +kernel
private theorem lookupValid044 : lookupValidAt (44 : Fin 310) := by decide +kernel
private theorem lookupValid045 : lookupValidAt (45 : Fin 310) := by decide +kernel
private theorem lookupValid046 : lookupValidAt (46 : Fin 310) := by decide +kernel
private theorem lookupValid047 : lookupValidAt (47 : Fin 310) := by decide +kernel
private theorem lookupValid048 : lookupValidAt (48 : Fin 310) := by decide +kernel
private theorem lookupValid049 : lookupValidAt (49 : Fin 310) := by decide +kernel
private theorem lookupValid050 : lookupValidAt (50 : Fin 310) := by decide +kernel
private theorem lookupValid051 : lookupValidAt (51 : Fin 310) := by decide +kernel
private theorem lookupValid052 : lookupValidAt (52 : Fin 310) := by decide +kernel
private theorem lookupValid053 : lookupValidAt (53 : Fin 310) := by decide +kernel
private theorem lookupValid054 : lookupValidAt (54 : Fin 310) := by decide +kernel
private theorem lookupValid055 : lookupValidAt (55 : Fin 310) := by decide +kernel
private theorem lookupValid056 : lookupValidAt (56 : Fin 310) := by decide +kernel
private theorem lookupValid057 : lookupValidAt (57 : Fin 310) := by decide +kernel
private theorem lookupValid058 : lookupValidAt (58 : Fin 310) := by decide +kernel
private theorem lookupValid059 : lookupValidAt (59 : Fin 310) := by decide +kernel
private theorem lookupValid060 : lookupValidAt (60 : Fin 310) := by decide +kernel
private theorem lookupValid061 : lookupValidAt (61 : Fin 310) := by decide +kernel
private theorem lookupValid062 : lookupValidAt (62 : Fin 310) := by decide +kernel
private theorem lookupValid063 : lookupValidAt (63 : Fin 310) := by decide +kernel
private theorem lookupValid064 : lookupValidAt (64 : Fin 310) := by decide +kernel
private theorem lookupValid065 : lookupValidAt (65 : Fin 310) := by decide +kernel
private theorem lookupValid066 : lookupValidAt (66 : Fin 310) := by decide +kernel
private theorem lookupValid067 : lookupValidAt (67 : Fin 310) := by decide +kernel
private theorem lookupValid068 : lookupValidAt (68 : Fin 310) := by decide +kernel
private theorem lookupValid069 : lookupValidAt (69 : Fin 310) := by decide +kernel
private theorem lookupValid070 : lookupValidAt (70 : Fin 310) := by decide +kernel
private theorem lookupValid071 : lookupValidAt (71 : Fin 310) := by decide +kernel
private theorem lookupValid072 : lookupValidAt (72 : Fin 310) := by decide +kernel
private theorem lookupValid073 : lookupValidAt (73 : Fin 310) := by decide +kernel
private theorem lookupValid074 : lookupValidAt (74 : Fin 310) := by decide +kernel
private theorem lookupValid075 : lookupValidAt (75 : Fin 310) := by decide +kernel
private theorem lookupValid076 : lookupValidAt (76 : Fin 310) := by decide +kernel
private theorem lookupValid077 : lookupValidAt (77 : Fin 310) := by decide +kernel
private theorem lookupValid078 : lookupValidAt (78 : Fin 310) := by decide +kernel
private theorem lookupValid079 : lookupValidAt (79 : Fin 310) := by decide +kernel
private theorem lookupValid080 : lookupValidAt (80 : Fin 310) := by decide +kernel
private theorem lookupValid081 : lookupValidAt (81 : Fin 310) := by decide +kernel
private theorem lookupValid082 : lookupValidAt (82 : Fin 310) := by decide +kernel
private theorem lookupValid083 : lookupValidAt (83 : Fin 310) := by decide +kernel
private theorem lookupValid084 : lookupValidAt (84 : Fin 310) := by decide +kernel
private theorem lookupValid085 : lookupValidAt (85 : Fin 310) := by decide +kernel
private theorem lookupValid086 : lookupValidAt (86 : Fin 310) := by decide +kernel
private theorem lookupValid087 : lookupValidAt (87 : Fin 310) := by decide +kernel
private theorem lookupValid088 : lookupValidAt (88 : Fin 310) := by decide +kernel
private theorem lookupValid089 : lookupValidAt (89 : Fin 310) := by decide +kernel
private theorem lookupValid090 : lookupValidAt (90 : Fin 310) := by decide +kernel
private theorem lookupValid091 : lookupValidAt (91 : Fin 310) := by decide +kernel
private theorem lookupValid092 : lookupValidAt (92 : Fin 310) := by decide +kernel
private theorem lookupValid093 : lookupValidAt (93 : Fin 310) := by decide +kernel
private theorem lookupValid094 : lookupValidAt (94 : Fin 310) := by decide +kernel
private theorem lookupValid095 : lookupValidAt (95 : Fin 310) := by decide +kernel
private theorem lookupValid096 : lookupValidAt (96 : Fin 310) := by decide +kernel
private theorem lookupValid097 : lookupValidAt (97 : Fin 310) := by decide +kernel
private theorem lookupValid098 : lookupValidAt (98 : Fin 310) := by decide +kernel
private theorem lookupValid099 : lookupValidAt (99 : Fin 310) := by decide +kernel
private theorem lookupValid100 : lookupValidAt (100 : Fin 310) := by decide +kernel
private theorem lookupValid101 : lookupValidAt (101 : Fin 310) := by decide +kernel
private theorem lookupValid102 : lookupValidAt (102 : Fin 310) := by decide +kernel
private theorem lookupValid103 : lookupValidAt (103 : Fin 310) := by decide +kernel
private theorem lookupValid104 : lookupValidAt (104 : Fin 310) := by decide +kernel
private theorem lookupValid105 : lookupValidAt (105 : Fin 310) := by decide +kernel
private theorem lookupValid106 : lookupValidAt (106 : Fin 310) := by decide +kernel
private theorem lookupValid107 : lookupValidAt (107 : Fin 310) := by decide +kernel
private theorem lookupValid108 : lookupValidAt (108 : Fin 310) := by decide +kernel
private theorem lookupValid109 : lookupValidAt (109 : Fin 310) := by decide +kernel
private theorem lookupValid110 : lookupValidAt (110 : Fin 310) := by decide +kernel
private theorem lookupValid111 : lookupValidAt (111 : Fin 310) := by decide +kernel
private theorem lookupValid112 : lookupValidAt (112 : Fin 310) := by decide +kernel
private theorem lookupValid113 : lookupValidAt (113 : Fin 310) := by decide +kernel
private theorem lookupValid114 : lookupValidAt (114 : Fin 310) := by decide +kernel
private theorem lookupValid115 : lookupValidAt (115 : Fin 310) := by decide +kernel
private theorem lookupValid116 : lookupValidAt (116 : Fin 310) := by decide +kernel
private theorem lookupValid117 : lookupValidAt (117 : Fin 310) := by decide +kernel
private theorem lookupValid118 : lookupValidAt (118 : Fin 310) := by decide +kernel
private theorem lookupValid119 : lookupValidAt (119 : Fin 310) := by decide +kernel
private theorem lookupValid120 : lookupValidAt (120 : Fin 310) := by decide +kernel
private theorem lookupValid121 : lookupValidAt (121 : Fin 310) := by decide +kernel
private theorem lookupValid122 : lookupValidAt (122 : Fin 310) := by decide +kernel
private theorem lookupValid123 : lookupValidAt (123 : Fin 310) := by decide +kernel
private theorem lookupValid124 : lookupValidAt (124 : Fin 310) := by decide +kernel
private theorem lookupValid125 : lookupValidAt (125 : Fin 310) := by decide +kernel
private theorem lookupValid126 : lookupValidAt (126 : Fin 310) := by decide +kernel
private theorem lookupValid127 : lookupValidAt (127 : Fin 310) := by decide +kernel
private theorem lookupValid128 : lookupValidAt (128 : Fin 310) := by decide +kernel
private theorem lookupValid129 : lookupValidAt (129 : Fin 310) := by decide +kernel
private theorem lookupValid130 : lookupValidAt (130 : Fin 310) := by decide +kernel
private theorem lookupValid131 : lookupValidAt (131 : Fin 310) := by decide +kernel
private theorem lookupValid132 : lookupValidAt (132 : Fin 310) := by decide +kernel
private theorem lookupValid133 : lookupValidAt (133 : Fin 310) := by decide +kernel
private theorem lookupValid134 : lookupValidAt (134 : Fin 310) := by decide +kernel
private theorem lookupValid135 : lookupValidAt (135 : Fin 310) := by decide +kernel
private theorem lookupValid136 : lookupValidAt (136 : Fin 310) := by decide +kernel
private theorem lookupValid137 : lookupValidAt (137 : Fin 310) := by decide +kernel
private theorem lookupValid138 : lookupValidAt (138 : Fin 310) := by decide +kernel
private theorem lookupValid139 : lookupValidAt (139 : Fin 310) := by decide +kernel
private theorem lookupValid140 : lookupValidAt (140 : Fin 310) := by decide +kernel
private theorem lookupValid141 : lookupValidAt (141 : Fin 310) := by decide +kernel
private theorem lookupValid142 : lookupValidAt (142 : Fin 310) := by decide +kernel
private theorem lookupValid143 : lookupValidAt (143 : Fin 310) := by decide +kernel
private theorem lookupValid144 : lookupValidAt (144 : Fin 310) := by decide +kernel
private theorem lookupValid145 : lookupValidAt (145 : Fin 310) := by decide +kernel
private theorem lookupValid146 : lookupValidAt (146 : Fin 310) := by decide +kernel
private theorem lookupValid147 : lookupValidAt (147 : Fin 310) := by decide +kernel
private theorem lookupValid148 : lookupValidAt (148 : Fin 310) := by decide +kernel
private theorem lookupValid149 : lookupValidAt (149 : Fin 310) := by decide +kernel
private theorem lookupValid150 : lookupValidAt (150 : Fin 310) := by decide +kernel
private theorem lookupValid151 : lookupValidAt (151 : Fin 310) := by decide +kernel
private theorem lookupValid152 : lookupValidAt (152 : Fin 310) := by decide +kernel
private theorem lookupValid153 : lookupValidAt (153 : Fin 310) := by decide +kernel
private theorem lookupValid154 : lookupValidAt (154 : Fin 310) := by decide +kernel
private theorem lookupValid155 : lookupValidAt (155 : Fin 310) := by decide +kernel
private theorem lookupValid156 : lookupValidAt (156 : Fin 310) := by decide +kernel
private theorem lookupValid157 : lookupValidAt (157 : Fin 310) := by decide +kernel
private theorem lookupValid158 : lookupValidAt (158 : Fin 310) := by decide +kernel
private theorem lookupValid159 : lookupValidAt (159 : Fin 310) := by decide +kernel
private theorem lookupValid160 : lookupValidAt (160 : Fin 310) := by decide +kernel
private theorem lookupValid161 : lookupValidAt (161 : Fin 310) := by decide +kernel
private theorem lookupValid162 : lookupValidAt (162 : Fin 310) := by decide +kernel
private theorem lookupValid163 : lookupValidAt (163 : Fin 310) := by decide +kernel
private theorem lookupValid164 : lookupValidAt (164 : Fin 310) := by decide +kernel
private theorem lookupValid165 : lookupValidAt (165 : Fin 310) := by decide +kernel
private theorem lookupValid166 : lookupValidAt (166 : Fin 310) := by decide +kernel
private theorem lookupValid167 : lookupValidAt (167 : Fin 310) := by decide +kernel
private theorem lookupValid168 : lookupValidAt (168 : Fin 310) := by decide +kernel
private theorem lookupValid169 : lookupValidAt (169 : Fin 310) := by decide +kernel
private theorem lookupValid170 : lookupValidAt (170 : Fin 310) := by decide +kernel
private theorem lookupValid171 : lookupValidAt (171 : Fin 310) := by decide +kernel
private theorem lookupValid172 : lookupValidAt (172 : Fin 310) := by decide +kernel
private theorem lookupValid173 : lookupValidAt (173 : Fin 310) := by decide +kernel
private theorem lookupValid174 : lookupValidAt (174 : Fin 310) := by decide +kernel
private theorem lookupValid175 : lookupValidAt (175 : Fin 310) := by decide +kernel
private theorem lookupValid176 : lookupValidAt (176 : Fin 310) := by decide +kernel
private theorem lookupValid177 : lookupValidAt (177 : Fin 310) := by decide +kernel
private theorem lookupValid178 : lookupValidAt (178 : Fin 310) := by decide +kernel
private theorem lookupValid179 : lookupValidAt (179 : Fin 310) := by decide +kernel
private theorem lookupValid180 : lookupValidAt (180 : Fin 310) := by decide +kernel
private theorem lookupValid181 : lookupValidAt (181 : Fin 310) := by decide +kernel
private theorem lookupValid182 : lookupValidAt (182 : Fin 310) := by decide +kernel
private theorem lookupValid183 : lookupValidAt (183 : Fin 310) := by decide +kernel
private theorem lookupValid184 : lookupValidAt (184 : Fin 310) := by decide +kernel
private theorem lookupValid185 : lookupValidAt (185 : Fin 310) := by decide +kernel
private theorem lookupValid186 : lookupValidAt (186 : Fin 310) := by decide +kernel
private theorem lookupValid187 : lookupValidAt (187 : Fin 310) := by decide +kernel
private theorem lookupValid188 : lookupValidAt (188 : Fin 310) := by decide +kernel
private theorem lookupValid189 : lookupValidAt (189 : Fin 310) := by decide +kernel
private theorem lookupValid190 : lookupValidAt (190 : Fin 310) := by decide +kernel
private theorem lookupValid191 : lookupValidAt (191 : Fin 310) := by decide +kernel
private theorem lookupValid192 : lookupValidAt (192 : Fin 310) := by decide +kernel
private theorem lookupValid193 : lookupValidAt (193 : Fin 310) := by decide +kernel
private theorem lookupValid194 : lookupValidAt (194 : Fin 310) := by decide +kernel
private theorem lookupValid195 : lookupValidAt (195 : Fin 310) := by decide +kernel
private theorem lookupValid196 : lookupValidAt (196 : Fin 310) := by decide +kernel
private theorem lookupValid197 : lookupValidAt (197 : Fin 310) := by decide +kernel
private theorem lookupValid198 : lookupValidAt (198 : Fin 310) := by decide +kernel
private theorem lookupValid199 : lookupValidAt (199 : Fin 310) := by decide +kernel
private theorem lookupValid200 : lookupValidAt (200 : Fin 310) := by decide +kernel
private theorem lookupValid201 : lookupValidAt (201 : Fin 310) := by decide +kernel
private theorem lookupValid202 : lookupValidAt (202 : Fin 310) := by decide +kernel
private theorem lookupValid203 : lookupValidAt (203 : Fin 310) := by decide +kernel
private theorem lookupValid204 : lookupValidAt (204 : Fin 310) := by decide +kernel
private theorem lookupValid205 : lookupValidAt (205 : Fin 310) := by decide +kernel
private theorem lookupValid206 : lookupValidAt (206 : Fin 310) := by decide +kernel
private theorem lookupValid207 : lookupValidAt (207 : Fin 310) := by decide +kernel
private theorem lookupValid208 : lookupValidAt (208 : Fin 310) := by decide +kernel
private theorem lookupValid209 : lookupValidAt (209 : Fin 310) := by decide +kernel
private theorem lookupValid210 : lookupValidAt (210 : Fin 310) := by decide +kernel
private theorem lookupValid211 : lookupValidAt (211 : Fin 310) := by decide +kernel
private theorem lookupValid212 : lookupValidAt (212 : Fin 310) := by decide +kernel
private theorem lookupValid213 : lookupValidAt (213 : Fin 310) := by decide +kernel
private theorem lookupValid214 : lookupValidAt (214 : Fin 310) := by decide +kernel
private theorem lookupValid215 : lookupValidAt (215 : Fin 310) := by decide +kernel
private theorem lookupValid216 : lookupValidAt (216 : Fin 310) := by decide +kernel
private theorem lookupValid217 : lookupValidAt (217 : Fin 310) := by decide +kernel
private theorem lookupValid218 : lookupValidAt (218 : Fin 310) := by decide +kernel
private theorem lookupValid219 : lookupValidAt (219 : Fin 310) := by decide +kernel
private theorem lookupValid220 : lookupValidAt (220 : Fin 310) := by decide +kernel
private theorem lookupValid221 : lookupValidAt (221 : Fin 310) := by decide +kernel
private theorem lookupValid222 : lookupValidAt (222 : Fin 310) := by decide +kernel
private theorem lookupValid223 : lookupValidAt (223 : Fin 310) := by decide +kernel
private theorem lookupValid224 : lookupValidAt (224 : Fin 310) := by decide +kernel
private theorem lookupValid225 : lookupValidAt (225 : Fin 310) := by decide +kernel
private theorem lookupValid226 : lookupValidAt (226 : Fin 310) := by decide +kernel
private theorem lookupValid227 : lookupValidAt (227 : Fin 310) := by decide +kernel
private theorem lookupValid228 : lookupValidAt (228 : Fin 310) := by decide +kernel
private theorem lookupValid229 : lookupValidAt (229 : Fin 310) := by decide +kernel
private theorem lookupValid230 : lookupValidAt (230 : Fin 310) := by decide +kernel
private theorem lookupValid231 : lookupValidAt (231 : Fin 310) := by decide +kernel
private theorem lookupValid232 : lookupValidAt (232 : Fin 310) := by decide +kernel
private theorem lookupValid233 : lookupValidAt (233 : Fin 310) := by decide +kernel
private theorem lookupValid234 : lookupValidAt (234 : Fin 310) := by decide +kernel
private theorem lookupValid235 : lookupValidAt (235 : Fin 310) := by decide +kernel
private theorem lookupValid236 : lookupValidAt (236 : Fin 310) := by decide +kernel
private theorem lookupValid237 : lookupValidAt (237 : Fin 310) := by decide +kernel
private theorem lookupValid238 : lookupValidAt (238 : Fin 310) := by decide +kernel
private theorem lookupValid239 : lookupValidAt (239 : Fin 310) := by decide +kernel
private theorem lookupValid240 : lookupValidAt (240 : Fin 310) := by decide +kernel
private theorem lookupValid241 : lookupValidAt (241 : Fin 310) := by decide +kernel
private theorem lookupValid242 : lookupValidAt (242 : Fin 310) := by decide +kernel
private theorem lookupValid243 : lookupValidAt (243 : Fin 310) := by decide +kernel
private theorem lookupValid244 : lookupValidAt (244 : Fin 310) := by decide +kernel
private theorem lookupValid245 : lookupValidAt (245 : Fin 310) := by decide +kernel
private theorem lookupValid246 : lookupValidAt (246 : Fin 310) := by decide +kernel
private theorem lookupValid247 : lookupValidAt (247 : Fin 310) := by decide +kernel
private theorem lookupValid248 : lookupValidAt (248 : Fin 310) := by decide +kernel
private theorem lookupValid249 : lookupValidAt (249 : Fin 310) := by decide +kernel
private theorem lookupValid250 : lookupValidAt (250 : Fin 310) := by decide +kernel
private theorem lookupValid251 : lookupValidAt (251 : Fin 310) := by decide +kernel
private theorem lookupValid252 : lookupValidAt (252 : Fin 310) := by decide +kernel
private theorem lookupValid253 : lookupValidAt (253 : Fin 310) := by decide +kernel
private theorem lookupValid254 : lookupValidAt (254 : Fin 310) := by decide +kernel
private theorem lookupValid255 : lookupValidAt (255 : Fin 310) := by decide +kernel
private theorem lookupValid256 : lookupValidAt (256 : Fin 310) := by decide +kernel
private theorem lookupValid257 : lookupValidAt (257 : Fin 310) := by decide +kernel
private theorem lookupValid258 : lookupValidAt (258 : Fin 310) := by decide +kernel
private theorem lookupValid259 : lookupValidAt (259 : Fin 310) := by decide +kernel
private theorem lookupValid260 : lookupValidAt (260 : Fin 310) := by decide +kernel
private theorem lookupValid261 : lookupValidAt (261 : Fin 310) := by decide +kernel
private theorem lookupValid262 : lookupValidAt (262 : Fin 310) := by decide +kernel
private theorem lookupValid263 : lookupValidAt (263 : Fin 310) := by decide +kernel
private theorem lookupValid264 : lookupValidAt (264 : Fin 310) := by decide +kernel
private theorem lookupValid265 : lookupValidAt (265 : Fin 310) := by decide +kernel
private theorem lookupValid266 : lookupValidAt (266 : Fin 310) := by decide +kernel
private theorem lookupValid267 : lookupValidAt (267 : Fin 310) := by decide +kernel
private theorem lookupValid268 : lookupValidAt (268 : Fin 310) := by decide +kernel
private theorem lookupValid269 : lookupValidAt (269 : Fin 310) := by decide +kernel
private theorem lookupValid270 : lookupValidAt (270 : Fin 310) := by decide +kernel
private theorem lookupValid271 : lookupValidAt (271 : Fin 310) := by decide +kernel
private theorem lookupValid272 : lookupValidAt (272 : Fin 310) := by decide +kernel
private theorem lookupValid273 : lookupValidAt (273 : Fin 310) := by decide +kernel
private theorem lookupValid274 : lookupValidAt (274 : Fin 310) := by decide +kernel
private theorem lookupValid275 : lookupValidAt (275 : Fin 310) := by decide +kernel
private theorem lookupValid276 : lookupValidAt (276 : Fin 310) := by decide +kernel
private theorem lookupValid277 : lookupValidAt (277 : Fin 310) := by decide +kernel
private theorem lookupValid278 : lookupValidAt (278 : Fin 310) := by decide +kernel
private theorem lookupValid279 : lookupValidAt (279 : Fin 310) := by decide +kernel
private theorem lookupValid280 : lookupValidAt (280 : Fin 310) := by decide +kernel
private theorem lookupValid281 : lookupValidAt (281 : Fin 310) := by decide +kernel
private theorem lookupValid282 : lookupValidAt (282 : Fin 310) := by decide +kernel
private theorem lookupValid283 : lookupValidAt (283 : Fin 310) := by decide +kernel
private theorem lookupValid284 : lookupValidAt (284 : Fin 310) := by decide +kernel
private theorem lookupValid285 : lookupValidAt (285 : Fin 310) := by decide +kernel
private theorem lookupValid286 : lookupValidAt (286 : Fin 310) := by decide +kernel
private theorem lookupValid287 : lookupValidAt (287 : Fin 310) := by decide +kernel
private theorem lookupValid288 : lookupValidAt (288 : Fin 310) := by decide +kernel
private theorem lookupValid289 : lookupValidAt (289 : Fin 310) := by decide +kernel
private theorem lookupValid290 : lookupValidAt (290 : Fin 310) := by decide +kernel
private theorem lookupValid291 : lookupValidAt (291 : Fin 310) := by decide +kernel
private theorem lookupValid292 : lookupValidAt (292 : Fin 310) := by decide +kernel
private theorem lookupValid293 : lookupValidAt (293 : Fin 310) := by decide +kernel
private theorem lookupValid294 : lookupValidAt (294 : Fin 310) := by decide +kernel
private theorem lookupValid295 : lookupValidAt (295 : Fin 310) := by decide +kernel
private theorem lookupValid296 : lookupValidAt (296 : Fin 310) := by decide +kernel
private theorem lookupValid297 : lookupValidAt (297 : Fin 310) := by decide +kernel
private theorem lookupValid298 : lookupValidAt (298 : Fin 310) := by decide +kernel
private theorem lookupValid299 : lookupValidAt (299 : Fin 310) := by decide +kernel
private theorem lookupValid300 : lookupValidAt (300 : Fin 310) := by decide +kernel
private theorem lookupValid301 : lookupValidAt (301 : Fin 310) := by decide +kernel
private theorem lookupValid302 : lookupValidAt (302 : Fin 310) := by decide +kernel
private theorem lookupValid303 : lookupValidAt (303 : Fin 310) := by decide +kernel
private theorem lookupValid304 : lookupValidAt (304 : Fin 310) := by decide +kernel
private theorem lookupValid305 : lookupValidAt (305 : Fin 310) := by decide +kernel
private theorem lookupValid306 : lookupValidAt (306 : Fin 310) := by decide +kernel
private theorem lookupValid307 : lookupValidAt (307 : Fin 310) := by decide +kernel
private theorem lookupValid308 : lookupValidAt (308 : Fin 310) := by decide +kernel
private theorem lookupValid309 : lookupValidAt (309 : Fin 310) := by decide +kernel

private theorem lookupValid : ∀ i : Fin 310, lookupValidAt i :=
  (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid000) (finOne lookupValid001)) (finSplit (finOne lookupValid002) (finOne lookupValid003))) (finSplit (finSplit (finOne lookupValid004) (finOne lookupValid005)) (finSplit (finOne lookupValid006) (finSplit (finOne lookupValid007) (finOne lookupValid008))))) (finSplit (finSplit (finSplit (finOne lookupValid009) (finOne lookupValid010)) (finSplit (finOne lookupValid011) (finSplit (finOne lookupValid012) (finOne lookupValid013)))) (finSplit (finSplit (finOne lookupValid014) (finOne lookupValid015)) (finSplit (finOne lookupValid016) (finSplit (finOne lookupValid017) (finOne lookupValid018)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid019) (finOne lookupValid020)) (finSplit (finOne lookupValid021) (finOne lookupValid022))) (finSplit (finSplit (finOne lookupValid023) (finOne lookupValid024)) (finSplit (finOne lookupValid025) (finSplit (finOne lookupValid026) (finOne lookupValid027))))) (finSplit (finSplit (finSplit (finOne lookupValid028) (finOne lookupValid029)) (finSplit (finOne lookupValid030) (finSplit (finOne lookupValid031) (finOne lookupValid032)))) (finSplit (finSplit (finOne lookupValid033) (finOne lookupValid034)) (finSplit (finOne lookupValid035) (finSplit (finOne lookupValid036) (finOne lookupValid037))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid038) (finOne lookupValid039)) (finSplit (finOne lookupValid040) (finOne lookupValid041))) (finSplit (finSplit (finOne lookupValid042) (finOne lookupValid043)) (finSplit (finOne lookupValid044) (finSplit (finOne lookupValid045) (finOne lookupValid046))))) (finSplit (finSplit (finSplit (finOne lookupValid047) (finOne lookupValid048)) (finSplit (finOne lookupValid049) (finSplit (finOne lookupValid050) (finOne lookupValid051)))) (finSplit (finSplit (finOne lookupValid052) (finOne lookupValid053)) (finSplit (finOne lookupValid054) (finSplit (finOne lookupValid055) (finOne lookupValid056)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid057) (finOne lookupValid058)) (finSplit (finOne lookupValid059) (finSplit (finOne lookupValid060) (finOne lookupValid061)))) (finSplit (finSplit (finOne lookupValid062) (finOne lookupValid063)) (finSplit (finOne lookupValid064) (finSplit (finOne lookupValid065) (finOne lookupValid066))))) (finSplit (finSplit (finSplit (finOne lookupValid067) (finOne lookupValid068)) (finSplit (finOne lookupValid069) (finSplit (finOne lookupValid070) (finOne lookupValid071)))) (finSplit (finSplit (finOne lookupValid072) (finOne lookupValid073)) (finSplit (finOne lookupValid074) (finSplit (finOne lookupValid075) (finOne lookupValid076)))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid077) (finOne lookupValid078)) (finSplit (finOne lookupValid079) (finOne lookupValid080))) (finSplit (finSplit (finOne lookupValid081) (finOne lookupValid082)) (finSplit (finOne lookupValid083) (finSplit (finOne lookupValid084) (finOne lookupValid085))))) (finSplit (finSplit (finSplit (finOne lookupValid086) (finOne lookupValid087)) (finSplit (finOne lookupValid088) (finSplit (finOne lookupValid089) (finOne lookupValid090)))) (finSplit (finSplit (finOne lookupValid091) (finOne lookupValid092)) (finSplit (finOne lookupValid093) (finSplit (finOne lookupValid094) (finOne lookupValid095)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid096) (finOne lookupValid097)) (finSplit (finOne lookupValid098) (finSplit (finOne lookupValid099) (finOne lookupValid100)))) (finSplit (finSplit (finOne lookupValid101) (finOne lookupValid102)) (finSplit (finOne lookupValid103) (finSplit (finOne lookupValid104) (finOne lookupValid105))))) (finSplit (finSplit (finSplit (finOne lookupValid106) (finOne lookupValid107)) (finSplit (finOne lookupValid108) (finSplit (finOne lookupValid109) (finOne lookupValid110)))) (finSplit (finSplit (finOne lookupValid111) (finOne lookupValid112)) (finSplit (finOne lookupValid113) (finSplit (finOne lookupValid114) (finOne lookupValid115))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid116) (finOne lookupValid117)) (finSplit (finOne lookupValid118) (finOne lookupValid119))) (finSplit (finSplit (finOne lookupValid120) (finOne lookupValid121)) (finSplit (finOne lookupValid122) (finSplit (finOne lookupValid123) (finOne lookupValid124))))) (finSplit (finSplit (finSplit (finOne lookupValid125) (finOne lookupValid126)) (finSplit (finOne lookupValid127) (finSplit (finOne lookupValid128) (finOne lookupValid129)))) (finSplit (finSplit (finOne lookupValid130) (finOne lookupValid131)) (finSplit (finOne lookupValid132) (finSplit (finOne lookupValid133) (finOne lookupValid134)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid135) (finOne lookupValid136)) (finSplit (finOne lookupValid137) (finSplit (finOne lookupValid138) (finOne lookupValid139)))) (finSplit (finSplit (finOne lookupValid140) (finOne lookupValid141)) (finSplit (finOne lookupValid142) (finSplit (finOne lookupValid143) (finOne lookupValid144))))) (finSplit (finSplit (finSplit (finOne lookupValid145) (finOne lookupValid146)) (finSplit (finOne lookupValid147) (finSplit (finOne lookupValid148) (finOne lookupValid149)))) (finSplit (finSplit (finOne lookupValid150) (finOne lookupValid151)) (finSplit (finOne lookupValid152) (finSplit (finOne lookupValid153) (finOne lookupValid154))))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid155) (finOne lookupValid156)) (finSplit (finOne lookupValid157) (finOne lookupValid158))) (finSplit (finSplit (finOne lookupValid159) (finOne lookupValid160)) (finSplit (finOne lookupValid161) (finSplit (finOne lookupValid162) (finOne lookupValid163))))) (finSplit (finSplit (finSplit (finOne lookupValid164) (finOne lookupValid165)) (finSplit (finOne lookupValid166) (finSplit (finOne lookupValid167) (finOne lookupValid168)))) (finSplit (finSplit (finOne lookupValid169) (finOne lookupValid170)) (finSplit (finOne lookupValid171) (finSplit (finOne lookupValid172) (finOne lookupValid173)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid174) (finOne lookupValid175)) (finSplit (finOne lookupValid176) (finOne lookupValid177))) (finSplit (finSplit (finOne lookupValid178) (finOne lookupValid179)) (finSplit (finOne lookupValid180) (finSplit (finOne lookupValid181) (finOne lookupValid182))))) (finSplit (finSplit (finSplit (finOne lookupValid183) (finOne lookupValid184)) (finSplit (finOne lookupValid185) (finSplit (finOne lookupValid186) (finOne lookupValid187)))) (finSplit (finSplit (finOne lookupValid188) (finOne lookupValid189)) (finSplit (finOne lookupValid190) (finSplit (finOne lookupValid191) (finOne lookupValid192))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid193) (finOne lookupValid194)) (finSplit (finOne lookupValid195) (finOne lookupValid196))) (finSplit (finSplit (finOne lookupValid197) (finOne lookupValid198)) (finSplit (finOne lookupValid199) (finSplit (finOne lookupValid200) (finOne lookupValid201))))) (finSplit (finSplit (finSplit (finOne lookupValid202) (finOne lookupValid203)) (finSplit (finOne lookupValid204) (finSplit (finOne lookupValid205) (finOne lookupValid206)))) (finSplit (finSplit (finOne lookupValid207) (finOne lookupValid208)) (finSplit (finOne lookupValid209) (finSplit (finOne lookupValid210) (finOne lookupValid211)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid212) (finOne lookupValid213)) (finSplit (finOne lookupValid214) (finSplit (finOne lookupValid215) (finOne lookupValid216)))) (finSplit (finSplit (finOne lookupValid217) (finOne lookupValid218)) (finSplit (finOne lookupValid219) (finSplit (finOne lookupValid220) (finOne lookupValid221))))) (finSplit (finSplit (finSplit (finOne lookupValid222) (finOne lookupValid223)) (finSplit (finOne lookupValid224) (finSplit (finOne lookupValid225) (finOne lookupValid226)))) (finSplit (finSplit (finOne lookupValid227) (finOne lookupValid228)) (finSplit (finOne lookupValid229) (finSplit (finOne lookupValid230) (finOne lookupValid231)))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid232) (finOne lookupValid233)) (finSplit (finOne lookupValid234) (finOne lookupValid235))) (finSplit (finSplit (finOne lookupValid236) (finOne lookupValid237)) (finSplit (finOne lookupValid238) (finSplit (finOne lookupValid239) (finOne lookupValid240))))) (finSplit (finSplit (finSplit (finOne lookupValid241) (finOne lookupValid242)) (finSplit (finOne lookupValid243) (finSplit (finOne lookupValid244) (finOne lookupValid245)))) (finSplit (finSplit (finOne lookupValid246) (finOne lookupValid247)) (finSplit (finOne lookupValid248) (finSplit (finOne lookupValid249) (finOne lookupValid250)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid251) (finOne lookupValid252)) (finSplit (finOne lookupValid253) (finSplit (finOne lookupValid254) (finOne lookupValid255)))) (finSplit (finSplit (finOne lookupValid256) (finOne lookupValid257)) (finSplit (finOne lookupValid258) (finSplit (finOne lookupValid259) (finOne lookupValid260))))) (finSplit (finSplit (finSplit (finOne lookupValid261) (finOne lookupValid262)) (finSplit (finOne lookupValid263) (finSplit (finOne lookupValid264) (finOne lookupValid265)))) (finSplit (finSplit (finOne lookupValid266) (finOne lookupValid267)) (finSplit (finOne lookupValid268) (finSplit (finOne lookupValid269) (finOne lookupValid270))))))) (finSplit (finSplit (finSplit (finSplit (finSplit (finOne lookupValid271) (finOne lookupValid272)) (finSplit (finOne lookupValid273) (finOne lookupValid274))) (finSplit (finSplit (finOne lookupValid275) (finOne lookupValid276)) (finSplit (finOne lookupValid277) (finSplit (finOne lookupValid278) (finOne lookupValid279))))) (finSplit (finSplit (finSplit (finOne lookupValid280) (finOne lookupValid281)) (finSplit (finOne lookupValid282) (finSplit (finOne lookupValid283) (finOne lookupValid284)))) (finSplit (finSplit (finOne lookupValid285) (finOne lookupValid286)) (finSplit (finOne lookupValid287) (finSplit (finOne lookupValid288) (finOne lookupValid289)))))) (finSplit (finSplit (finSplit (finSplit (finOne lookupValid290) (finOne lookupValid291)) (finSplit (finOne lookupValid292) (finSplit (finOne lookupValid293) (finOne lookupValid294)))) (finSplit (finSplit (finOne lookupValid295) (finOne lookupValid296)) (finSplit (finOne lookupValid297) (finSplit (finOne lookupValid298) (finOne lookupValid299))))) (finSplit (finSplit (finSplit (finOne lookupValid300) (finOne lookupValid301)) (finSplit (finOne lookupValid302) (finSplit (finOne lookupValid303) (finOne lookupValid304)))) (finSplit (finSplit (finOne lookupValid305) (finOne lookupValid306)) (finSplit (finOne lookupValid307) (finSplit (finOne lookupValid308) (finOne lookupValid309))))))))))

private theorem normalLookup_valid (i : Fin 310) (j : Fin 10) :
    NormalLookupValid (c := 2) (m := 8) normalExponent (quarticExponent i) j (normalLookup i j) :=
  (lookupValid i).1 j

private theorem traceLookup_valid (i : Fin 310) (j : Fin 2) :
    TraceLookupValid (c := 2) (m := 8) traceExponent (quarticExponent i) j (traceLookup i j) :=
  (lookupValid i).2 j

/-- The natural variable-major order used to export the middle coefficient matrix. -/
def naturalColumn : Fin 310 ≃ MiddleColumn 2 8 (Fin 25) (Fin 30) :=
  (finSumFinEquiv (m := 250) (n := 60)).symm.trans
    (Equiv.sumCongr (finProdFinEquiv (m := 10) (n := 25)).symm
      (finProdFinEquiv (m := 2) (n := 30)).symm)

def permutedColumnIndex (j : Fin 310) : Fin 310 :=
  Fin.ofNat 310 (middlePermutationEntry j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem permutedColumnIndex_injective : Function.Injective permutedColumnIndex := by
  have hbound : ∀ j : Fin 310, middleColumnPermutation[j.val]! < 310 := by decide +kernel
  have he : ∀ j : Fin 310, middlePermutationEntry j = middleColumnPermutation[j.val]! := by
    decide +kernel
  intro i j hij
  apply arrayGet_injective middleColumnPermutation 310 (by decide) (by decide +kernel)
  have hval := congrArg Fin.val hij
  change middlePermutationEntry i % 310 = middlePermutationEntry j % 310 at hval
  rw [he i, he j] at hval
  simpa only [Nat.mod_eq_of_lt (hbound i), Nat.mod_eq_of_lt (hbound j)] using hval

def permutedColumn : Fin 310 ≃ MiddleColumn 2 8 (Fin 25) (Fin 30) :=
  (Equiv.ofBijective permutedColumnIndex
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨permutedColumnIndex_injective, rfl⟩)).trans
    naturalColumn

def lookupMiddleEntry {R : Type*} [Zero R]
    (Kn : Matrix (Fin 100) (Fin 25) R) (Kt : Matrix (Fin 120) (Fin 30) R)
    (i j : Fin 310) : R :=
  Sum.elim (fun k => ((normalLookup i k.1).map (fun a => Kn a k.2)).getD 0)
    (fun k => ((traceLookup i k.1).map (fun a => Kt a k.2)).getD 0)
    (naturalColumn (permutedColumnIndex j))

theorem middleMatrix_eq_lookup {R : Type*} [CommSemiring R]
    (Kn : Matrix (Fin 100) (Fin 25) R) (Kt : Matrix (Fin 120) (Fin 30) R) (i j : Fin 310) :
    middleMatrix normalExponent traceExponent quarticExponent Kn Kt i (permutedColumn j) =
      lookupMiddleEntry Kn Kt i j := by
  change middleMatrix normalExponent traceExponent quarticExponent Kn Kt i
    (naturalColumn (permutedColumnIndex j)) = _
  unfold lookupMiddleEntry
  cases naturalColumn (permutedColumnIndex j) with
  | inl k =>
    exact middleMatrix_apply_inl_of_lookup _ _ _ _ _ _ _ _ _
      (normalLookup_iff_of_valid (c := 2) (m := 8) normalExponent normalExponent_injective normalExponent_positive
        _ _ _ (normalLookup_valid i k.1))
  | inr k =>
    exact middleMatrix_apply_inr_of_lookup _ _ _ _ _ _ _ _ _
      (traceLookup_iff_of_valid (c := 2) (m := 8) traceExponent traceExponent_injective
        _ _ _ (traceLookup_valid i k.1))

end IdealGeneration.CubicTen
