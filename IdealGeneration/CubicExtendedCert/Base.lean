module

public import IdealGeneration.CubicInitialResidueEvaluation
public import Mathlib.Data.List.FinRange

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicExtended

noncomputable section

open MvPolynomial Matrix ConeParameterSpace ConeMonomialChart CertifiedRank

private noncomputable def supportData (i : Fin 78) : Nat × Nat × Nat :=
  if i.val < 39 then
    if i.val < 19 then
      if i.val < 9 then
        if i.val < 4 then
          if i.val < 2 then
            if i.val < 1 then
              (0, 12, 0)
            else
              (1, 12, 0)
          else
            if i.val < 3 then
              (2, 12, 0)
            else
              (3, 12, 0)
        else
          if i.val < 6 then
            if i.val < 5 then
              (4, 12, 0)
            else
              (5, 12, 0)
          else
            if i.val < 7 then
              (6, 12, 0)
            else
              if i.val < 8 then
                (7, 12, 0)
              else
                (8, 12, 0)
      else
        if i.val < 14 then
          if i.val < 11 then
            if i.val < 10 then
              (9, 12, 0)
            else
              (0, 1, 779)
          else
            if i.val < 12 then
              (0, 2, 930)
            else
              if i.val < 13 then
                (0, 3, 620)
              else
                (0, 4, 764)
        else
          if i.val < 16 then
            if i.val < 15 then
              (0, 5, 650)
            else
              (0, 6, 866)
          else
            if i.val < 17 then
              (0, 7, 418)
            else
              if i.val < 18 then
                (0, 8, 740)
              else
                (0, 9, 302)
    else
      if i.val < 29 then
        if i.val < 24 then
          if i.val < 21 then
            if i.val < 20 then
              (1, 2, 533)
            else
              (1, 3, 862)
          else
            if i.val < 22 then
              (1, 4, 326)
            else
              if i.val < 23 then
                (1, 5, 522)
              else
                (1, 6, 246)
        else
          if i.val < 26 then
            if i.val < 25 then
              (1, 7, 380)
            else
              (1, 8, 304)
          else
            if i.val < 27 then
              (1, 9, 566)
            else
              if i.val < 28 then
                (2, 3, 699)
              else
                (2, 4, 144)
      else
        if i.val < 34 then
          if i.val < 31 then
            if i.val < 30 then
              (2, 5, 813)
            else
              (2, 6, 91)
          else
            if i.val < 32 then
              (2, 7, 1001)
            else
              if i.val < 33 then
                (2, 8, 198)
              else
                (2, 9, 843)
        else
          if i.val < 36 then
            if i.val < 35 then
              (3, 4, 705)
            else
              (3, 5, 501)
          else
            if i.val < 37 then
              (3, 6, 645)
            else
              if i.val < 38 then
                (3, 7, 602)
              else
                (3, 8, 828)
  else
    if i.val < 58 then
      if i.val < 48 then
        if i.val < 43 then
          if i.val < 41 then
            if i.val < 40 then
              (3, 9, 641)
            else
              (4, 5, 954)
          else
            if i.val < 42 then
              (4, 6, 613)
            else
              (4, 7, 807)
        else
          if i.val < 45 then
            if i.val < 44 then
              (4, 8, 68)
            else
              (4, 9, 558)
          else
            if i.val < 46 then
              (5, 6, 295)
            else
              if i.val < 47 then
                (5, 7, 607)
              else
                (5, 8, 64)
      else
        if i.val < 53 then
          if i.val < 50 then
            if i.val < 49 then
              (5, 9, 107)
            else
              (6, 7, 865)
          else
            if i.val < 51 then
              (6, 8, 126)
            else
              if i.val < 52 then
                (6, 9, 919)
              else
                (7, 8, 157)
        else
          if i.val < 55 then
            if i.val < 54 then
              (7, 9, 659)
            else
              (8, 9, 963)
          else
            if i.val < 56 then
              (10, 12, 0)
            else
              if i.val < 57 then
                (11, 12, 0)
              else
                (0, 10, 194)
    else
      if i.val < 68 then
        if i.val < 63 then
          if i.val < 60 then
            if i.val < 59 then
              (0, 11, 902)
            else
              (1, 10, 768)
          else
            if i.val < 61 then
              (1, 11, 309)
            else
              if i.val < 62 then
                (2, 10, 368)
              else
                (2, 11, 755)
        else
          if i.val < 65 then
            if i.val < 64 then
              (3, 10, 837)
            else
              (3, 11, 155)
          else
            if i.val < 66 then
              (4, 10, 296)
            else
              if i.val < 67 then
                (4, 11, 406)
              else
                (5, 10, 185)
      else
        if i.val < 73 then
          if i.val < 70 then
            if i.val < 69 then
              (5, 11, 263)
            else
              (6, 10, 883)
          else
            if i.val < 71 then
              (6, 11, 613)
            else
              if i.val < 72 then
                (7, 10, 357)
              else
                (7, 11, 406)
        else
          if i.val < 75 then
            if i.val < 74 then
              (8, 10, 296)
            else
              (8, 11, 245)
          else
            if i.val < 76 then
              (9, 10, 790)
            else
              if i.val < 77 then
                (9, 11, 479)
              else
                (10, 11, 998)

private noncomputable def coneData (i : Fin 147) : Fin 78 × Nat × Nat :=
  if i.val < 73 then
    if i.val < 36 then
      if i.val < 18 then
        if i.val < 9 then
          if i.val < 4 then
            if i.val < 2 then
              if i.val < 1 then
                (0, 235, 818)
              else
                (0, 654, 355)
            else
              if i.val < 3 then
                (1, 82, 999)
              else
                (1, 503, 873)
          else
            if i.val < 6 then
              if i.val < 5 then
                (2, 704, 373)
              else
                (2, 288, 793)
            else
              if i.val < 7 then
                (3, 391, 857)
              else
                if i.val < 8 then
                  (3, 385, 894)
                else
                  (4, 549, 334)
        else
          if i.val < 13 then
            if i.val < 11 then
              if i.val < 10 then
                (4, 511, 158)
              else
                (5, 923, 18)
            else
              if i.val < 12 then
                (5, 267, 169)
              else
                (6, 751, 542)
          else
            if i.val < 15 then
              if i.val < 14 then
                (6, 546, 949)
              else
                (7, 66, 763)
            else
              if i.val < 16 then
                (7, 27, 741)
              else
                if i.val < 17 then
                  (8, 720, 350)
                else
                  (8, 311, 211)
      else
        if i.val < 27 then
          if i.val < 22 then
            if i.val < 20 then
              if i.val < 19 then
                (9, 346, 942)
              else
                (9, 605, 40)
            else
              if i.val < 21 then
                (10, 243, 737)
              else
                (10, 858, 511)
          else
            if i.val < 24 then
              if i.val < 23 then
                (11, 961, 223)
              else
                (11, 8, 442)
            else
              if i.val < 25 then
                (12, 1, 68)
              else
                if i.val < 26 then
                  (12, 133, 1001)
                else
                  (13, 904, 49)
        else
          if i.val < 31 then
            if i.val < 29 then
              if i.val < 28 then
                (13, 519, 229)
              else
                (14, 371, 659)
            else
              if i.val < 30 then
                (14, 748, 166)
              else
                (15, 670, 831)
          else
            if i.val < 33 then
              if i.val < 32 then
                (15, 925, 577)
              else
                (16, 1002, 496)
            else
              if i.val < 34 then
                (16, 112, 924)
              else
                if i.val < 35 then
                  (17, 90, 353)
                else
                  (17, 284, 330)
    else
      if i.val < 54 then
        if i.val < 45 then
          if i.val < 40 then
            if i.val < 38 then
              if i.val < 37 then
                (18, 880, 719)
              else
                (18, 157, 170)
            else
              if i.val < 39 then
                (19, 612, 551)
              else
                (19, 189, 957)
          else
            if i.val < 42 then
              if i.val < 41 then
                (20, 747, 948)
              else
                (20, 737, 471)
            else
              if i.val < 43 then
                (21, 519, 165)
              else
                if i.val < 44 then
                  (21, 52, 695)
                else
                  (22, 368, 940)
        else
          if i.val < 49 then
            if i.val < 47 then
              if i.val < 46 then
                (22, 843, 24)
              else
                (23, 198, 880)
            else
              if i.val < 48 then
                (23, 245, 70)
              else
                (24, 997, 399)
          else
            if i.val < 51 then
              if i.val < 50 then
                (25, 113, 189)
              else
                (25, 14, 822)
            else
              if i.val < 52 then
                (26, 588, 54)
              else
                if i.val < 53 then
                  (26, 360, 790)
                else
                  (27, 382, 414)
      else
        if i.val < 63 then
          if i.val < 58 then
            if i.val < 56 then
              if i.val < 55 then
                (27, 915, 255)
              else
                (28, 350, 144)
            else
              if i.val < 57 then
                (28, 721, 108)
              else
                (29, 143, 13)
          else
            if i.val < 60 then
              if i.val < 59 then
                (29, 135, 220)
              else
                (30, 357, 704)
            else
              if i.val < 61 then
                (30, 1001, 715)
              else
                if i.val < 62 then
                  (31, 922, 101)
                else
                  (31, 792, 502)
        else
          if i.val < 68 then
            if i.val < 65 then
              if i.val < 64 then
                (32, 462, 162)
              else
                (33, 223, 282)
            else
              if i.val < 66 then
                (33, 465, 97)
              else
                if i.val < 67 then
                  (34, 390, 451)
                else
                  (34, 755, 731)
          else
            if i.val < 70 then
              if i.val < 69 then
                (35, 671, 567)
              else
                (35, 184, 64)
            else
              if i.val < 71 then
                (36, 139, 216)
              else
                if i.val < 72 then
                  (36, 465, 876)
                else
                  (37, 466, 540)
  else
    if i.val < 110 then
      if i.val < 91 then
        if i.val < 82 then
          if i.val < 77 then
            if i.val < 75 then
              if i.val < 74 then
                (37, 6, 251)
              else
                (38, 507, 899)
            else
              if i.val < 76 then
                (38, 128, 477)
              else
                (39, 492, 538)
          else
            if i.val < 79 then
              if i.val < 78 then
                (39, 216, 104)
              else
                (40, 130, 792)
            else
              if i.val < 80 then
                (40, 173, 62)
              else
                if i.val < 81 then
                  (41, 988, 995)
                else
                  (41, 362, 58)
        else
          if i.val < 86 then
            if i.val < 84 then
              if i.val < 83 then
                (42, 197, 291)
              else
                (42, 721, 795)
            else
              if i.val < 85 then
                (43, 404, 943)
              else
                (43, 146, 919)
          else
            if i.val < 88 then
              if i.val < 87 then
                (44, 250, 286)
              else
                (44, 184, 1003)
            else
              if i.val < 89 then
                (45, 575, 265)
              else
                if i.val < 90 then
                  (45, 968, 504)
                else
                  (46, 562, 481)
      else
        if i.val < 100 then
          if i.val < 95 then
            if i.val < 93 then
              if i.val < 92 then
                (46, 74, 837)
              else
                (47, 856, 634)
            else
              if i.val < 94 then
                (47, 332, 403)
              else
                (48, 894, 596)
          else
            if i.val < 97 then
              if i.val < 96 then
                (48, 35, 204)
              else
                (49, 454, 287)
            else
              if i.val < 98 then
                (49, 495, 20)
              else
                if i.val < 99 then
                  (50, 953, 513)
                else
                  (50, 923, 480)
        else
          if i.val < 105 then
            if i.val < 102 then
              if i.val < 101 then
                (51, 284, 622)
              else
                (51, 578, 433)
            else
              if i.val < 103 then
                (52, 259, 312)
              else
                if i.val < 104 then
                  (52, 347, 163)
                else
                  (53, 376, 455)
          else
            if i.val < 107 then
              if i.val < 106 then
                (53, 941, 953)
              else
                (54, 326, 849)
            else
              if i.val < 108 then
                (54, 579, 517)
              else
                if i.val < 109 then
                  (55, 771, 957)
                else
                  (55, 585, 475)
    else
      if i.val < 128 then
        if i.val < 119 then
          if i.val < 114 then
            if i.val < 112 then
              if i.val < 111 then
                (56, 357, 830)
              else
                (56, 40, 475)
            else
              if i.val < 113 then
                (57, 677, 212)
              else
                (57, 781, 32)
          else
            if i.val < 116 then
              if i.val < 115 then
                (58, 60, 816)
              else
                (58, 442, 233)
            else
              if i.val < 117 then
                (59, 817, 294)
              else
                if i.val < 118 then
                  (60, 970, 285)
                else
                  (60, 555, 128)
        else
          if i.val < 123 then
            if i.val < 121 then
              if i.val < 120 then
                (61, 200, 359)
              else
                (62, 650, 665)
            else
              if i.val < 122 then
                (62, 318, 793)
              else
                (63, 888, 771)
          else
            if i.val < 125 then
              if i.val < 124 then
                (64, 324, 918)
              else
                (64, 477, 628)
            else
              if i.val < 126 then
                (65, 264, 890)
              else
                if i.val < 127 then
                  (66, 346, 43)
                else
                  (66, 544, 813)
      else
        if i.val < 137 then
          if i.val < 132 then
            if i.val < 130 then
              if i.val < 129 then
                (67, 864, 125)
              else
                (67, 687, 422)
            else
              if i.val < 131 then
                (68, 633, 848)
              else
                (68, 117, 805)
          else
            if i.val < 134 then
              if i.val < 133 then
                (69, 115, 102)
              else
                (69, 399, 404)
            else
              if i.val < 135 then
                (70, 555, 123)
              else
                if i.val < 136 then
                  (70, 143, 823)
                else
                  (71, 945, 972)
        else
          if i.val < 142 then
            if i.val < 139 then
              if i.val < 138 then
                (71, 421, 388)
              else
                (72, 41, 933)
            else
              if i.val < 140 then
                (73, 675, 602)
              else
                if i.val < 141 then
                  (73, 705, 660)
                else
                  (74, 260, 823)
          else
            if i.val < 144 then
              if i.val < 143 then
                (75, 906, 790)
              else
                (75, 723, 750)
            else
              if i.val < 145 then
                (76, 418, 302)
              else
                if i.val < 146 then
                  (77, 166, 25)
                else
                  (77, 332, 336)

noncomputable def normalCode (i : Fin 196) : Nat :=
  if i.val < 98 then
    if i.val < 49 then
      if i.val < 24 then
        if i.val < 12 then
          if i.val < 6 then
            if i.val < 3 then
              if i.val < 1 then
                3
              else
                if i.val < 2 then
                  7
                else
                  27
            else
              if i.val < 4 then
                127
              else
                if i.val < 5 then
                  627
                else
                  3127
          else
            if i.val < 9 then
              if i.val < 7 then
                15627
              else
                if i.val < 8 then
                  78127
                else
                  390627
            else
              if i.val < 10 then
                1953127
              else
                if i.val < 11 then
                  9765627
                else
                  48828127
        else
          if i.val < 18 then
            if i.val < 15 then
              if i.val < 13 then
                244140627
              else
                if i.val < 14 then
                  1220703127
                else
                  11
            else
              if i.val < 16 then
                31
              else
                if i.val < 17 then
                  131
                else
                  631
          else
            if i.val < 21 then
              if i.val < 19 then
                3131
              else
                if i.val < 20 then
                  15631
                else
                  78131
            else
              if i.val < 22 then
                390631
              else
                if i.val < 23 then
                  1953131
                else
                  9765631
      else
        if i.val < 36 then
          if i.val < 30 then
            if i.val < 27 then
              if i.val < 25 then
                48828131
              else
                if i.val < 26 then
                  244140631
                else
                  1220703131
            else
              if i.val < 28 then
                51
              else
                if i.val < 29 then
                  151
                else
                  651
          else
            if i.val < 33 then
              if i.val < 31 then
                3151
              else
                if i.val < 32 then
                  15651
                else
                  78151
            else
              if i.val < 34 then
                390651
              else
                if i.val < 35 then
                  1953151
                else
                  9765651
        else
          if i.val < 42 then
            if i.val < 39 then
              if i.val < 37 then
                48828151
              else
                if i.val < 38 then
                  244140651
                else
                  1220703151
            else
              if i.val < 40 then
                251
              else
                if i.val < 41 then
                  751
                else
                  3251
          else
            if i.val < 45 then
              if i.val < 43 then
                15751
              else
                if i.val < 44 then
                  78251
                else
                  390751
            else
              if i.val < 47 then
                if i.val < 46 then
                  1953251
                else
                  9765751
              else
                if i.val < 48 then
                  48828251
                else
                  244140751
    else
      if i.val < 73 then
        if i.val < 61 then
          if i.val < 55 then
            if i.val < 52 then
              if i.val < 50 then
                1220703251
              else
                if i.val < 51 then
                  1251
                else
                  3751
            else
              if i.val < 53 then
                16251
              else
                if i.val < 54 then
                  78751
                else
                  391251
          else
            if i.val < 58 then
              if i.val < 56 then
                1953751
              else
                if i.val < 57 then
                  9766251
                else
                  48828751
            else
              if i.val < 59 then
                244141251
              else
                if i.val < 60 then
                  1220703751
                else
                  6251
        else
          if i.val < 67 then
            if i.val < 64 then
              if i.val < 62 then
                18751
              else
                if i.val < 63 then
                  81251
                else
                  393751
            else
              if i.val < 65 then
                1956251
              else
                if i.val < 66 then
                  9768751
                else
                  48831251
          else
            if i.val < 70 then
              if i.val < 68 then
                244143751
              else
                if i.val < 69 then
                  1220706251
                else
                  31251
            else
              if i.val < 71 then
                93751
              else
                if i.val < 72 then
                  406251
                else
                  1968751
      else
        if i.val < 85 then
          if i.val < 79 then
            if i.val < 76 then
              if i.val < 74 then
                9781251
              else
                if i.val < 75 then
                  48843751
                else
                  244156251
            else
              if i.val < 77 then
                1220718751
              else
                if i.val < 78 then
                  156251
                else
                  468751
          else
            if i.val < 82 then
              if i.val < 80 then
                2031251
              else
                if i.val < 81 then
                  9843751
                else
                  48906251
            else
              if i.val < 83 then
                244218751
              else
                if i.val < 84 then
                  1220781251
                else
                  781251
        else
          if i.val < 91 then
            if i.val < 88 then
              if i.val < 86 then
                2343751
              else
                if i.val < 87 then
                  10156251
                else
                  49218751
            else
              if i.val < 89 then
                244531251
              else
                if i.val < 90 then
                  1221093751
                else
                  3906251
          else
            if i.val < 94 then
              if i.val < 92 then
                11718751
              else
                if i.val < 93 then
                  50781251
                else
                  246093751
            else
              if i.val < 96 then
                if i.val < 95 then
                  1222656251
                else
                  19531251
              else
                if i.val < 97 then
                  58593751
                else
                  253906251
  else
    if i.val < 147 then
      if i.val < 122 then
        if i.val < 110 then
          if i.val < 104 then
            if i.val < 101 then
              if i.val < 99 then
                1230468751
              else
                if i.val < 100 then
                  97656251
                else
                  292968751
            else
              if i.val < 102 then
                1269531251
              else
                if i.val < 103 then
                  488281251
                else
                  1464843751
          else
            if i.val < 107 then
              if i.val < 105 then
                2441406251
              else
                if i.val < 106 then
                  15
                else
                  35
            else
              if i.val < 108 then
                135
              else
                if i.val < 109 then
                  635
                else
                  3135
        else
          if i.val < 116 then
            if i.val < 113 then
              if i.val < 111 then
                15635
              else
                if i.val < 112 then
                  78135
                else
                  390635
            else
              if i.val < 114 then
                1953135
              else
                if i.val < 115 then
                  9765635
                else
                  48828135
          else
            if i.val < 119 then
              if i.val < 117 then
                244140635
              else
                if i.val < 118 then
                  1220703135
                else
                  55
            else
              if i.val < 120 then
                155
              else
                if i.val < 121 then
                  655
                else
                  3155
      else
        if i.val < 134 then
          if i.val < 128 then
            if i.val < 125 then
              if i.val < 123 then
                15655
              else
                if i.val < 124 then
                  78155
                else
                  390655
            else
              if i.val < 126 then
                1953155
              else
                if i.val < 127 then
                  9765655
                else
                  48828155
          else
            if i.val < 131 then
              if i.val < 129 then
                244140655
              else
                if i.val < 130 then
                  1220703155
                else
                  255
            else
              if i.val < 132 then
                755
              else
                if i.val < 133 then
                  3255
                else
                  15755
        else
          if i.val < 140 then
            if i.val < 137 then
              if i.val < 135 then
                78255
              else
                if i.val < 136 then
                  390755
                else
                  1953255
            else
              if i.val < 138 then
                9765755
              else
                if i.val < 139 then
                  48828255
                else
                  244140755
          else
            if i.val < 143 then
              if i.val < 141 then
                1220703255
              else
                if i.val < 142 then
                  1255
                else
                  3755
            else
              if i.val < 145 then
                if i.val < 144 then
                  16255
                else
                  78755
              else
                if i.val < 146 then
                  391255
                else
                  1953755
    else
      if i.val < 171 then
        if i.val < 159 then
          if i.val < 153 then
            if i.val < 150 then
              if i.val < 148 then
                9766255
              else
                if i.val < 149 then
                  48828755
                else
                  244141255
            else
              if i.val < 151 then
                1220703755
              else
                if i.val < 152 then
                  6255
                else
                  18755
          else
            if i.val < 156 then
              if i.val < 154 then
                81255
              else
                if i.val < 155 then
                  393755
                else
                  1956255
            else
              if i.val < 157 then
                9768755
              else
                if i.val < 158 then
                  48831255
                else
                  244143755
        else
          if i.val < 165 then
            if i.val < 162 then
              if i.val < 160 then
                1220706255
              else
                if i.val < 161 then
                  31255
                else
                  93755
            else
              if i.val < 163 then
                406255
              else
                if i.val < 164 then
                  1968755
                else
                  9781255
          else
            if i.val < 168 then
              if i.val < 166 then
                48843755
              else
                if i.val < 167 then
                  244156255
                else
                  1220718755
            else
              if i.val < 169 then
                156255
              else
                if i.val < 170 then
                  468755
                else
                  2031255
      else
        if i.val < 183 then
          if i.val < 177 then
            if i.val < 174 then
              if i.val < 172 then
                9843755
              else
                if i.val < 173 then
                  48906255
                else
                  244218755
            else
              if i.val < 175 then
                1220781255
              else
                if i.val < 176 then
                  781255
                else
                  2343755
          else
            if i.val < 180 then
              if i.val < 178 then
                10156255
              else
                if i.val < 179 then
                  49218755
                else
                  244531255
            else
              if i.val < 181 then
                1221093755
              else
                if i.val < 182 then
                  3906255
                else
                  11718755
        else
          if i.val < 189 then
            if i.val < 186 then
              if i.val < 184 then
                50781255
              else
                if i.val < 185 then
                  246093755
                else
                  1222656255
            else
              if i.val < 187 then
                19531255
              else
                if i.val < 188 then
                  58593755
                else
                  253906255
          else
            if i.val < 192 then
              if i.val < 190 then
                1230468755
              else
                if i.val < 191 then
                  97656255
                else
                  292968755
            else
              if i.val < 194 then
                if i.val < 193 then
                  1269531255
                else
                  488281255
              else
                if i.val < 195 then
                  1464843755
                else
                  2441406255

/-- Each trace support is a coordinate vertex or a scaled coordinate edge. -/
def traceCoordinate (a : Fin 78) (j : Fin 12) : ℕ :=
  let s := supportData a
  (if j.val = s.1 then 1 else 0) + (if j.val = s.2.1 then s.2.2 else 0)

def support (i : Fin 147) : Fin 78 := (coneData i).1

def normalCoordinate (i : Fin 147) (j : Fin 2) : ℕ :=
  if j = 0 then 1 else (coneData i).2.1

def height (i : Fin 147) : ℕ := (coneData i).2.2

/-- The marked parameters of the extended C2 cone over the supported trace points. -/
def parameters (R : Type*) [Semiring R] : Parameters R 2 12 147 78 :=
  assemble (fun ij => traceCoordinate ij.1 ij.2)
    (fun ij => normalCoordinate ij.1 ij.2) (fun i => height i)

def pointCoordinate (i : Fin 147) (j : Fin 14) : ℕ :=
  Fin.addCases (normalCoordinate i) (fun k => height i * traceCoordinate (support i) k) j

noncomputable def normalExponent (i : Fin 196) : Fin 14 →₀ ℕ :=
  CubicInitial.exponent (normalCode i)

/-- `E′P` as evaluation of the ordered positive-normal-degree cubic monomials. -/
noncomputable def normalEvaluationMatrix (R : Type*) [CommSemiring R] :
    Matrix (Fin 147) (Fin 196) R :=
  evaluationMatrix (fun i j => pointCoordinate i j) normalExponent


end
end IdealGeneration.CubicExtended
