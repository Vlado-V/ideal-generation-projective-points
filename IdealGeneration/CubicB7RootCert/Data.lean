module

public import IdealGeneration.CertifiedSparseRow

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.B7RootCertificate

open CertifiedRank Matrix

private noncomputable def index0_000 : Fin 86 := 0
private noncomputable def index0_001 : Fin 86 := 1
private noncomputable def index0_002 : Fin 86 := 2
private noncomputable def index0_003 : Fin 86 := 3
private noncomputable def index0_004 : Fin 86 := 4
private noncomputable def index0_005 : Fin 86 := 5
private noncomputable def index0_006 : Fin 86 := 6
private noncomputable def index0_007 : Fin 86 := 7
private noncomputable def index0_008 : Fin 86 := 8
private noncomputable def index0_009 : Fin 86 := 9
private noncomputable def index0_010 : Fin 86 := 10
private noncomputable def index0_011 : Fin 86 := 11
private noncomputable def index0_012 : Fin 86 := 12
private noncomputable def index0_013 : Fin 86 := 13
private noncomputable def index0_014 : Fin 86 := 14
private noncomputable def index0_015 : Fin 86 := 15
private noncomputable def index0_016 : Fin 86 := 16
private noncomputable def index0_017 : Fin 86 := 17
private noncomputable def index0_018 : Fin 86 := 18
private noncomputable def index0_019 : Fin 86 := 19
private noncomputable def index0_020 : Fin 86 := 20
private noncomputable def index0_021 : Fin 86 := 21
private noncomputable def index0_022 : Fin 86 := 22
private noncomputable def index0_023 : Fin 86 := 23
private noncomputable def index0_024 : Fin 86 := 24
private noncomputable def index0_025 : Fin 86 := 25
private noncomputable def index0_026 : Fin 86 := 26
private noncomputable def index0_027 : Fin 86 := 27
private noncomputable def index0_028 : Fin 86 := 28
private noncomputable def index0_029 : Fin 86 := 29
private noncomputable def index0_030 : Fin 86 := 30
private noncomputable def index0_031 : Fin 86 := 31
private noncomputable def index0_032 : Fin 86 := 32
private noncomputable def index0_033 : Fin 86 := 33
private noncomputable def index0_034 : Fin 86 := 34
private noncomputable def index0_035 : Fin 86 := 35
private noncomputable def index0_036 : Fin 86 := 36
private noncomputable def index0_037 : Fin 86 := 37
private noncomputable def index0_038 : Fin 86 := 38
private noncomputable def index0_039 : Fin 86 := 39
private noncomputable def index0_040 : Fin 86 := 40
private noncomputable def index0_041 : Fin 86 := 41
private noncomputable def index0_042 : Fin 86 := 42
private noncomputable def index0_043 : Fin 86 := 43
private noncomputable def index0_044 : Fin 86 := 44
private noncomputable def index0_045 : Fin 86 := 45
private noncomputable def index0_046 : Fin 86 := 46
private noncomputable def index0_047 : Fin 86 := 47
private noncomputable def index0_048 : Fin 86 := 48
private noncomputable def index0_049 : Fin 86 := 49
private noncomputable def index0_050 : Fin 86 := 50
private noncomputable def index0_051 : Fin 86 := 51
private noncomputable def index0_052 : Fin 86 := 52
private noncomputable def index0_053 : Fin 86 := 53
private noncomputable def index0_054 : Fin 86 := 54
private noncomputable def index0_055 : Fin 86 := 55
private noncomputable def index0_056 : Fin 86 := 56
private noncomputable def index0_057 : Fin 86 := 57
private noncomputable def index0_058 : Fin 86 := 58
private noncomputable def index0_059 : Fin 86 := 59
private noncomputable def index0_060 : Fin 86 := 60
private noncomputable def index0_061 : Fin 86 := 61
private noncomputable def index0_062 : Fin 86 := 62
private noncomputable def index0_063 : Fin 86 := 63
private noncomputable def index0_064 : Fin 86 := 64
private noncomputable def index0_065 : Fin 86 := 65
private noncomputable def index0_066 : Fin 86 := 66
private noncomputable def index0_067 : Fin 86 := 67
private noncomputable def index0_068 : Fin 86 := 68
private noncomputable def index0_069 : Fin 86 := 69
private noncomputable def index0_070 : Fin 86 := 70
private noncomputable def index0_071 : Fin 86 := 71
private noncomputable def index0_072 : Fin 86 := 72
private noncomputable def index0_073 : Fin 86 := 73
private noncomputable def index0_074 : Fin 86 := 74
private noncomputable def index0_075 : Fin 86 := 75
private noncomputable def index0_076 : Fin 86 := 76
private noncomputable def index0_077 : Fin 86 := 77
private noncomputable def index0_078 : Fin 86 := 78
private noncomputable def index0_079 : Fin 86 := 79
private noncomputable def index0_080 : Fin 86 := 80
private noncomputable def index0_081 : Fin 86 := 81
private noncomputable def index0_082 : Fin 86 := 82
private noncomputable def index0_083 : Fin 86 := 83
private noncomputable def index0_084 : Fin 86 := 84
private noncomputable def index0_085 : Fin 86 := 85

private noncomputable def block0Rows000 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_045, 579), (index0_046, 397), (index0_047, 479), (index0_072, 302), (index0_073, 37), (index0_080, 9), (index0_081, 659), (index0_082, 377), (index0_083, 659), (index0_084, 223), (index0_085, 899)]

private noncomputable def block0Rows001 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_045, 932), (index0_046, 519), (index0_047, 525), (index0_080, 747), (index0_081, 282), (index0_082, 565), (index0_083, 282), (index0_084, 565), (index0_085, 962)]

private noncomputable def block0Rows002 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_048, 865), (index0_049, 610), (index0_050, 344), (index0_074, 218), (index0_075, 441), (index0_080, 197), (index0_081, 666), (index0_082, 813), (index0_083, 666), (index0_084, 984), (index0_085, 430)]

private noncomputable def block0Rows003 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_048, 315), (index0_049, 121), (index0_050, 763), (index0_080, 677), (index0_081, 114), (index0_082, 327), (index0_083, 114), (index0_084, 327), (index0_085, 939)]

private noncomputable def block0Rows004 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_051, 436), (index0_052, 784), (index0_053, 187), (index0_076, 401), (index0_077, 714), (index0_080, 964), (index0_081, 253), (index0_082, 55), (index0_083, 253), (index0_084, 563), (index0_085, 406)]

private noncomputable def block0Rows005 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_051, 666), (index0_052, 821), (index0_053, 365), (index0_080, 479), (index0_081, 297), (index0_082, 322), (index0_083, 297), (index0_084, 322), (index0_085, 544)]

private noncomputable def block0Rows006 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_054, 537), (index0_055, 580), (index0_056, 788), (index0_078, 715), (index0_079, 405), (index0_080, 880), (index0_081, 390), (index0_082, 382), (index0_083, 390), (index0_084, 305), (index0_085, 147)]

private noncomputable def block0Rows007 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_054, 552), (index0_055, 993), (index0_056, 958), (index0_080, 806), (index0_081, 235), (index0_082, 325), (index0_083, 235), (index0_084, 325), (index0_085, 817)]

private noncomputable def block0Rows008 : SparseRow 86 Nat :=
  [(index0_002, 369), (index0_003, 221), (index0_042, 819), (index0_043, 360), (index0_044, 981), (index0_045, 629), (index0_046, 482), (index0_047, 181), (index0_072, 181), (index0_073, 814), (index0_080, 482), (index0_081, 894), (index0_082, 217), (index0_083, 286), (index0_084, 649), (index0_085, 776)]

private noncomputable def block0Rows009 : SparseRow 86 Nat :=
  [(index0_002, 333), (index0_003, 101), (index0_042, 668), (index0_043, 566), (index0_044, 416), (index0_045, 682), (index0_046, 576), (index0_047, 391), (index0_072, 317), (index0_073, 587), (index0_080, 79), (index0_081, 945), (index0_082, 190), (index0_084, 798), (index0_085, 257)]

private noncomputable def block0Rows010 : SparseRow 86 Nat :=
  [(index0_012, 475), (index0_014, 1002), (index0_042, 492), (index0_043, 673), (index0_044, 227), (index0_048, 109), (index0_049, 251), (index0_050, 853), (index0_074, 176), (index0_075, 803), (index0_080, 483), (index0_081, 64), (index0_082, 907), (index0_083, 623), (index0_084, 191), (index0_085, 206)]

private noncomputable def block0Rows011 : SparseRow 86 Nat :=
  [(index0_012, 376), (index0_014, 893), (index0_042, 587), (index0_043, 1000), (index0_044, 197), (index0_048, 269), (index0_049, 118), (index0_050, 120), (index0_074, 754), (index0_075, 31), (index0_080, 938), (index0_081, 493), (index0_082, 589), (index0_083, 465), (index0_084, 30), (index0_085, 118)]

private noncomputable def block0Rows012 : SparseRow 86 Nat :=
  [(index0_022, 606), (index0_025, 509), (index0_042, 77), (index0_043, 110), (index0_044, 96), (index0_051, 568), (index0_052, 450), (index0_053, 182), (index0_076, 872), (index0_077, 130), (index0_080, 875), (index0_081, 809), (index0_082, 104), (index0_083, 486), (index0_084, 534), (index0_085, 765)]

private noncomputable def block0Rows013 : SparseRow 86 Nat :=
  [(index0_022, 497), (index0_025, 196), (index0_042, 705), (index0_043, 291), (index0_044, 375), (index0_051, 856), (index0_052, 235), (index0_053, 167), (index0_076, 849), (index0_077, 291), (index0_080, 847), (index0_081, 180), (index0_082, 8), (index0_083, 779), (index0_084, 331), (index0_085, 927)]

private noncomputable def block0Rows014 : SparseRow 86 Nat :=
  [(index0_032, 607), (index0_036, 658), (index0_042, 747), (index0_043, 6), (index0_044, 869), (index0_054, 32), (index0_055, 431), (index0_056, 493), (index0_078, 573), (index0_079, 566), (index0_080, 570), (index0_081, 368), (index0_082, 501), (index0_083, 160), (index0_084, 875), (index0_085, 545)]

private noncomputable def block0Rows015 : SparseRow 86 Nat :=
  [(index0_032, 850), (index0_036, 953), (index0_042, 668), (index0_043, 268), (index0_044, 90), (index0_054, 770), (index0_055, 860), (index0_056, 747), (index0_078, 340), (index0_079, 42), (index0_080, 750), (index0_081, 317), (index0_082, 1), (index0_083, 398), (index0_084, 209), (index0_085, 381)]

private noncomputable def block0Rows016 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_004, 754), (index0_013, 644), (index0_014, 540), (index0_045, 259), (index0_046, 541), (index0_047, 178), (index0_048, 586), (index0_049, 531), (index0_050, 464), (index0_072, 877), (index0_073, 739), (index0_074, 201), (index0_075, 747), (index0_080, 573), (index0_081, 147), (index0_082, 234), (index0_083, 147), (index0_084, 895), (index0_085, 195)]

private noncomputable def block0Rows017 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_004, 582), (index0_013, 582), (index0_014, 300), (index0_045, 598), (index0_046, 529), (index0_047, 842), (index0_048, 629), (index0_049, 68), (index0_050, 772), (index0_080, 602), (index0_081, 115), (index0_082, 536), (index0_083, 115), (index0_084, 536), (index0_085, 307)]

private noncomputable def block0Rows018 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_005, 218), (index0_023, 253), (index0_025, 480), (index0_045, 93), (index0_046, 578), (index0_047, 726), (index0_051, 735), (index0_052, 301), (index0_053, 876), (index0_072, 797), (index0_073, 930), (index0_076, 670), (index0_077, 561), (index0_080, 658), (index0_081, 872), (index0_082, 757), (index0_083, 872), (index0_084, 250), (index0_085, 251)]

private noncomputable def block0Rows019 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_005, 369), (index0_023, 369), (index0_025, 54), (index0_045, 615), (index0_046, 720), (index0_047, 150), (index0_051, 95), (index0_052, 705), (index0_053, 6), (index0_080, 607), (index0_081, 814), (index0_082, 600), (index0_083, 814), (index0_084, 600), (index0_085, 308)]

private noncomputable def block0Rows020 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_006, 486), (index0_033, 593), (index0_036, 44), (index0_045, 632), (index0_046, 373), (index0_047, 755), (index0_054, 847), (index0_055, 681), (index0_056, 439), (index0_072, 818), (index0_073, 298), (index0_078, 172), (index0_079, 89), (index0_080, 599), (index0_081, 401), (index0_082, 165), (index0_083, 401), (index0_084, 520), (index0_085, 792)]

private noncomputable def block0Rows021 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_006, 980), (index0_033, 980), (index0_036, 168), (index0_045, 396), (index0_046, 127), (index0_047, 743), (index0_054, 647), (index0_055, 851), (index0_056, 876), (index0_080, 681), (index0_081, 406), (index0_082, 340), (index0_083, 406), (index0_084, 340), (index0_085, 751)]

private noncomputable def block0Rows022 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_007, 176), (index0_045, 680), (index0_046, 806), (index0_047, 823), (index0_057, 338), (index0_058, 881), (index0_059, 708), (index0_072, 666), (index0_073, 474), (index0_080, 1000), (index0_081, 990), (index0_082, 643), (index0_083, 224), (index0_084, 692), (index0_085, 396)]

private noncomputable def block0Rows023 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_007, 85), (index0_045, 210), (index0_046, 7), (index0_047, 787), (index0_057, 842), (index0_058, 167), (index0_059, 848), (index0_072, 890), (index0_073, 1000), (index0_080, 897), (index0_081, 268), (index0_082, 927), (index0_083, 939), (index0_084, 684), (index0_085, 159)]

private noncomputable def block0Rows024 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_008, 173), (index0_045, 674), (index0_046, 192), (index0_047, 697), (index0_060, 105), (index0_061, 623), (index0_062, 620), (index0_072, 348), (index0_073, 411), (index0_080, 916), (index0_081, 364), (index0_082, 833), (index0_083, 585), (index0_084, 493), (index0_085, 805)]

private noncomputable def block0Rows025 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_008, 353), (index0_045, 537), (index0_046, 782), (index0_047, 117), (index0_060, 487), (index0_061, 752), (index0_062, 755), (index0_072, 992), (index0_073, 343), (index0_080, 622), (index0_081, 903), (index0_082, 547), (index0_083, 518), (index0_084, 326), (index0_085, 664)]

private noncomputable def block0Rows026 : SparseRow 86 Nat :=
  [(index0_000, 991), (index0_003, 817), (index0_009, 721), (index0_045, 355), (index0_046, 43), (index0_047, 778), (index0_063, 718), (index0_064, 625), (index0_065, 943), (index0_072, 102), (index0_073, 136), (index0_080, 733), (index0_081, 419), (index0_082, 148), (index0_083, 765), (index0_084, 439), (index0_085, 207)]

private noncomputable def block0Rows027 : SparseRow 86 Nat :=
  [(index0_000, 503), (index0_003, 1008), (index0_009, 503), (index0_045, 357), (index0_046, 55), (index0_047, 238), (index0_063, 905), (index0_064, 68), (index0_065, 909), (index0_072, 883), (index0_073, 583), (index0_080, 779), (index0_081, 899), (index0_082, 537), (index0_083, 404), (index0_084, 191), (index0_085, 710)]

private noncomputable def block0Rows028 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_010, 265), (index0_045, 603), (index0_046, 128), (index0_047, 493), (index0_066, 557), (index0_067, 794), (index0_068, 192), (index0_072, 247), (index0_073, 642), (index0_080, 850), (index0_081, 534), (index0_082, 959), (index0_083, 498), (index0_084, 284), (index0_085, 261)]

private noncomputable def block0Rows029 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_010, 879), (index0_045, 672), (index0_046, 185), (index0_047, 942), (index0_066, 337), (index0_067, 797), (index0_068, 368), (index0_072, 661), (index0_073, 678), (index0_080, 500), (index0_081, 852), (index0_082, 738), (index0_083, 858), (index0_084, 774), (index0_085, 719)]

private noncomputable def block0Rows030 : SparseRow 86 Nat :=
  [(index0_003, 817), (index0_011, 435), (index0_045, 966), (index0_046, 675), (index0_047, 20), (index0_069, 413), (index0_070, 451), (index0_071, 73), (index0_072, 732), (index0_073, 1007), (index0_080, 103), (index0_081, 463), (index0_082, 181), (index0_083, 658), (index0_084, 664), (index0_085, 155)]

private noncomputable def block0Rows031 : SparseRow 86 Nat :=
  [(index0_003, 1008), (index0_011, 491), (index0_045, 518), (index0_046, 990), (index0_047, 353), (index0_069, 932), (index0_070, 383), (index0_071, 685), (index0_072, 873), (index0_073, 498), (index0_080, 101), (index0_081, 201), (index0_082, 472), (index0_083, 262), (index0_084, 277), (index0_085, 422)]

private noncomputable def block0Rows032 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_015, 548), (index0_024, 738), (index0_025, 327), (index0_048, 175), (index0_049, 886), (index0_050, 61), (index0_051, 131), (index0_052, 873), (index0_053, 310), (index0_074, 782), (index0_075, 921), (index0_076, 811), (index0_077, 228), (index0_080, 886), (index0_081, 519), (index0_082, 290), (index0_083, 519), (index0_084, 601), (index0_085, 584)]

private noncomputable def block0Rows033 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_015, 865), (index0_024, 865), (index0_025, 453), (index0_048, 1002), (index0_049, 823), (index0_050, 754), (index0_051, 941), (index0_052, 536), (index0_053, 53), (index0_080, 306), (index0_081, 884), (index0_082, 923), (index0_083, 884), (index0_084, 923), (index0_085, 976)]

private noncomputable def block0Rows034 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_016, 747), (index0_034, 421), (index0_036, 851), (index0_048, 850), (index0_049, 627), (index0_050, 869), (index0_054, 856), (index0_055, 680), (index0_056, 57), (index0_074, 503), (index0_075, 90), (index0_078, 613), (index0_079, 621), (index0_080, 459), (index0_081, 333), (index0_082, 618), (index0_083, 333), (index0_084, 42), (index0_085, 105)]

private noncomputable def block0Rows035 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_016, 415), (index0_034, 415), (index0_036, 314), (index0_048, 353), (index0_049, 876), (index0_050, 282), (index0_054, 366), (index0_055, 334), (index0_056, 837), (index0_080, 491), (index0_081, 128), (index0_082, 418), (index0_083, 128), (index0_084, 418), (index0_085, 670)]

private noncomputable def block0Rows036 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_017, 1003), (index0_048, 175), (index0_049, 278), (index0_050, 710), (index0_057, 931), (index0_058, 88), (index0_059, 220), (index0_074, 501), (index0_075, 105), (index0_080, 83), (index0_081, 46), (index0_082, 709), (index0_083, 1006), (index0_084, 964), (index0_085, 505)]

private noncomputable def block0Rows037 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_017, 333), (index0_048, 799), (index0_049, 254), (index0_050, 192), (index0_057, 1002), (index0_058, 572), (index0_059, 173), (index0_074, 587), (index0_075, 657), (index0_080, 49), (index0_081, 393), (index0_082, 732), (index0_083, 682), (index0_084, 781), (index0_085, 855)]

private noncomputable def block0Rows038 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_018, 369), (index0_048, 819), (index0_049, 21), (index0_050, 826), (index0_060, 132), (index0_061, 369), (index0_062, 275), (index0_074, 390), (index0_075, 319), (index0_080, 93), (index0_081, 482), (index0_082, 785), (index0_083, 685), (index0_084, 713), (index0_085, 76)]

private noncomputable def block0Rows039 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_018, 205), (index0_048, 461), (index0_049, 55), (index0_050, 875), (index0_060, 246), (index0_061, 396), (index0_062, 476), (index0_074, 331), (index0_075, 548), (index0_080, 684), (index0_081, 46), (index0_082, 957), (index0_083, 585), (index0_084, 754), (index0_085, 711)]

private noncomputable def block0Rows040 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_019, 967), (index0_048, 373), (index0_049, 10), (index0_050, 372), (index0_063, 632), (index0_064, 945), (index0_065, 931), (index0_074, 878), (index0_075, 831), (index0_080, 246), (index0_081, 768), (index0_082, 636), (index0_083, 167), (index0_084, 108), (index0_085, 473)]

private noncomputable def block0Rows041 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_019, 313), (index0_048, 490), (index0_049, 335), (index0_050, 30), (index0_063, 97), (index0_064, 760), (index0_065, 977), (index0_074, 335), (index0_075, 864), (index0_080, 746), (index0_081, 594), (index0_082, 913), (index0_083, 494), (index0_084, 505), (index0_085, 688)]

private noncomputable def block0Rows042 : SparseRow 86 Nat :=
  [(index0_001, 356), (index0_014, 200), (index0_020, 224), (index0_048, 753), (index0_049, 316), (index0_050, 452), (index0_066, 873), (index0_067, 278), (index0_068, 515), (index0_074, 860), (index0_075, 791), (index0_080, 98), (index0_081, 256), (index0_082, 408), (index0_083, 617), (index0_084, 165), (index0_085, 381)]

private noncomputable def block0Rows043 : SparseRow 86 Nat :=
  [(index0_001, 685), (index0_014, 1008), (index0_020, 685), (index0_048, 695), (index0_049, 459), (index0_050, 290), (index0_066, 900), (index0_067, 851), (index0_068, 776), (index0_074, 996), (index0_075, 470), (index0_080, 595), (index0_081, 902), (index0_082, 162), (index0_083, 632), (index0_084, 810), (index0_085, 744)]

private noncomputable def block0Rows044 : SparseRow 86 Nat :=
  [(index0_014, 200), (index0_021, 73), (index0_048, 750), (index0_049, 787), (index0_050, 336), (index0_069, 497), (index0_070, 66), (index0_071, 728), (index0_074, 703), (index0_075, 96), (index0_080, 459), (index0_081, 750), (index0_082, 857), (index0_083, 728), (index0_084, 820), (index0_085, 759)]

private noncomputable def block0Rows045 : SparseRow 86 Nat :=
  [(index0_014, 1008), (index0_021, 489), (index0_048, 373), (index0_049, 302), (index0_050, 849), (index0_069, 101), (index0_070, 709), (index0_071, 860), (index0_074, 317), (index0_075, 460), (index0_080, 258), (index0_081, 121), (index0_082, 851), (index0_083, 940), (index0_084, 873), (index0_085, 170)]

private noncomputable def block0Rows046 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_026, 34), (index0_035, 201), (index0_036, 669), (index0_051, 507), (index0_052, 533), (index0_053, 919), (index0_054, 255), (index0_055, 495), (index0_056, 649), (index0_076, 591), (index0_077, 925), (index0_078, 535), (index0_079, 736), (index0_080, 523), (index0_081, 497), (index0_082, 898), (index0_083, 497), (index0_084, 6), (index0_085, 3)]

private noncomputable def block0Rows047 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_026, 584), (index0_035, 584), (index0_036, 995), (index0_051, 713), (index0_052, 628), (index0_053, 581), (index0_054, 286), (index0_055, 987), (index0_056, 534), (index0_080, 901), (index0_081, 932), (index0_082, 749), (index0_083, 932), (index0_084, 749), (index0_085, 505)]

private noncomputable def block0Rows048 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_027, 927), (index0_051, 979), (index0_052, 932), (index0_053, 448), (index0_057, 975), (index0_058, 535), (index0_059, 527), (index0_076, 182), (index0_077, 400), (index0_080, 993), (index0_081, 378), (index0_082, 310), (index0_083, 850), (index0_084, 615), (index0_085, 249)]

private noncomputable def block0Rows049 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_027, 16), (index0_051, 445), (index0_052, 576), (index0_053, 29), (index0_057, 460), (index0_058, 760), (index0_059, 742), (index0_076, 295), (index0_077, 262), (index0_080, 970), (index0_081, 406), (index0_082, 95), (index0_083, 616), (index0_084, 632), (index0_085, 135)]

private noncomputable def block0Rows050 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_028, 693), (index0_051, 744), (index0_052, 75), (index0_053, 571), (index0_060, 498), (index0_061, 896), (index0_062, 341), (index0_076, 109), (index0_077, 499), (index0_080, 970), (index0_081, 333), (index0_082, 973), (index0_083, 770), (index0_084, 413), (index0_085, 391)]

private noncomputable def block0Rows051 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_028, 923), (index0_051, 822), (index0_052, 46), (index0_053, 725), (index0_060, 744), (index0_061, 698), (index0_062, 326), (index0_076, 918), (index0_077, 728), (index0_080, 79), (index0_081, 686), (index0_082, 853), (index0_083, 487), (index0_084, 416), (index0_085, 738)]

private noncomputable def block0Rows052 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_029, 700), (index0_051, 489), (index0_052, 588), (index0_053, 280), (index0_063, 526), (index0_064, 496), (index0_065, 906), (index0_076, 906), (index0_077, 130), (index0_080, 245), (index0_081, 120), (index0_082, 784), (index0_083, 221), (index0_084, 585), (index0_085, 192)]

private noncomputable def block0Rows053 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_029, 331), (index0_051, 334), (index0_052, 716), (index0_053, 60), (index0_063, 617), (index0_064, 767), (index0_065, 926), (index0_076, 253), (index0_077, 301), (index0_080, 246), (index0_081, 23), (index0_082, 654), (index0_083, 111), (index0_084, 553), (index0_085, 881)]

private noncomputable def block0Rows054 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_030, 934), (index0_051, 95), (index0_052, 783), (index0_053, 850), (index0_066, 679), (index0_067, 387), (index0_068, 546), (index0_076, 273), (index0_077, 269), (index0_080, 1008), (index0_081, 638), (index0_082, 445), (index0_083, 94), (index0_084, 982), (index0_085, 362)]

private noncomputable def block0Rows055 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_030, 433), (index0_051, 535), (index0_052, 667), (index0_053, 223), (index0_066, 913), (index0_067, 948), (index0_068, 208), (index0_076, 507), (index0_077, 445), (index0_080, 67), (index0_081, 732), (index0_082, 640), (index0_083, 186), (index0_084, 175), (index0_085, 230)]

private noncomputable def block0Rows056 : SparseRow 86 Nat :=
  [(index0_025, 888), (index0_031, 137), (index0_051, 405), (index0_052, 722), (index0_053, 604), (index0_069, 735), (index0_070, 80), (index0_071, 63), (index0_076, 472), (index0_077, 567), (index0_080, 386), (index0_081, 517), (index0_082, 424), (index0_083, 287), (index0_084, 789), (index0_085, 276)]

private noncomputable def block0Rows057 : SparseRow 86 Nat :=
  [(index0_025, 1008), (index0_031, 810), (index0_051, 866), (index0_052, 424), (index0_053, 63), (index0_069, 397), (index0_070, 804), (index0_071, 500), (index0_076, 178), (index0_077, 69), (index0_080, 52), (index0_081, 736), (index0_082, 1006), (index0_083, 897), (index0_084, 227), (index0_085, 555)]

private noncomputable def block0Rows058 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_037, 308), (index0_054, 31), (index0_055, 462), (index0_056, 695), (index0_057, 885), (index0_058, 530), (index0_059, 885), (index0_078, 22), (index0_079, 207), (index0_080, 583), (index0_081, 274), (index0_082, 237), (index0_083, 903), (index0_084, 192), (index0_085, 590)]

private noncomputable def block0Rows059 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_037, 167), (index0_054, 483), (index0_055, 752), (index0_056, 3), (index0_057, 608), (index0_058, 998), (index0_059, 885), (index0_078, 515), (index0_079, 206), (index0_080, 273), (index0_081, 338), (index0_082, 901), (index0_083, 546), (index0_084, 272), (index0_085, 152)]

private noncomputable def block0Rows060 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_038, 526), (index0_054, 949), (index0_055, 647), (index0_056, 495), (index0_060, 513), (index0_061, 314), (index0_062, 475), (index0_078, 605), (index0_079, 280), (index0_080, 375), (index0_081, 935), (index0_082, 540), (index0_083, 796), (index0_084, 199), (index0_085, 853)]

private noncomputable def block0Rows061 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_038, 449), (index0_054, 138), (index0_055, 797), (index0_056, 419), (index0_060, 884), (index0_061, 173), (index0_062, 456), (index0_078, 733), (index0_079, 46), (index0_080, 815), (index0_081, 633), (index0_082, 32), (index0_083, 196), (index0_084, 171), (index0_085, 277)]

private noncomputable def block0Rows062 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_039, 547), (index0_054, 146), (index0_055, 83), (index0_056, 643), (index0_063, 353), (index0_064, 65), (index0_065, 870), (index0_078, 5), (index0_079, 848), (index0_080, 861), (index0_081, 451), (index0_082, 902), (index0_083, 746), (index0_084, 927), (index0_085, 540)]

private noncomputable def block0Rows063 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_039, 254), (index0_054, 805), (index0_055, 477), (index0_056, 119), (index0_063, 450), (index0_064, 841), (index0_065, 243), (index0_078, 320), (index0_079, 140), (index0_080, 970), (index0_081, 812), (index0_082, 481), (index0_083, 677), (index0_084, 186), (index0_085, 393)]

private noncomputable def block0Rows064 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_040, 394), (index0_054, 649), (index0_055, 150), (index0_056, 618), (index0_066, 563), (index0_067, 716), (index0_068, 602), (index0_078, 522), (index0_079, 279), (index0_080, 174), (index0_081, 369), (index0_082, 238), (index0_083, 939), (index0_084, 64), (index0_085, 386)]

private noncomputable def block0Rows065 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_040, 954), (index0_054, 57), (index0_055, 349), (index0_056, 322), (index0_066, 288), (index0_067, 278), (index0_068, 616), (index0_078, 685), (index0_079, 619), (index0_080, 249), (index0_081, 370), (index0_082, 687), (index0_083, 518), (index0_084, 117), (index0_085, 906)]

private noncomputable def block0Rows066 : SparseRow 86 Nat :=
  [(index0_036, 264), (index0_041, 796), (index0_054, 817), (index0_055, 668), (index0_056, 349), (index0_069, 455), (index0_070, 34), (index0_071, 265), (index0_078, 812), (index0_079, 77), (index0_080, 10), (index0_081, 721), (index0_082, 87), (index0_083, 593), (index0_084, 748), (index0_085, 404)]

private noncomputable def block0Rows067 : SparseRow 86 Nat :=
  [(index0_036, 1008), (index0_041, 104), (index0_054, 473), (index0_055, 817), (index0_056, 446), (index0_069, 814), (index0_070, 825), (index0_071, 872), (index0_078, 644), (index0_079, 755), (index0_080, 568), (index0_081, 55), (index0_082, 383), (index0_083, 374), (index0_084, 511), (index0_085, 792)]

private noncomputable def block0Rows068 : SparseRow 86 Nat :=
  [(index0_057, 637), (index0_058, 406), (index0_059, 60), (index0_080, 976), (index0_081, 299), (index0_082, 547), (index0_083, 557), (index0_084, 737), (index0_085, 977)]

private noncomputable def block0Rows069 : SparseRow 86 Nat :=
  [(index0_057, 140), (index0_058, 436), (index0_059, 360), (index0_080, 341), (index0_081, 133), (index0_082, 271), (index0_083, 424), (index0_084, 13), (index0_085, 233)]

private noncomputable def block0Rows070 : SparseRow 86 Nat :=
  [(index0_060, 238), (index0_061, 976), (index0_062, 214), (index0_080, 381), (index0_081, 129), (index0_082, 785), (index0_083, 304), (index0_084, 350), (index0_085, 766)]

private noncomputable def block0Rows071 : SparseRow 86 Nat :=
  [(index0_060, 260), (index0_061, 922), (index0_062, 392), (index0_081, 10), (index0_082, 495), (index0_083, 631), (index0_084, 320), (index0_085, 508)]

private noncomputable def block0Rows072 : SparseRow 86 Nat :=
  [(index0_063, 657), (index0_064, 594), (index0_065, 479), (index0_080, 645), (index0_081, 355), (index0_082, 644), (index0_083, 595), (index0_084, 379), (index0_085, 199)]

private noncomputable def block0Rows073 : SparseRow 86 Nat :=
  [(index0_063, 178), (index0_064, 815), (index0_065, 404), (index0_080, 842), (index0_081, 157), (index0_082, 258), (index0_083, 342), (index0_084, 18), (index0_085, 162)]

private noncomputable def block0Rows074 : SparseRow 86 Nat :=
  [(index0_066, 761), (index0_067, 467), (index0_068, 951), (index0_080, 72), (index0_081, 56), (index0_082, 440), (index0_083, 30), (index0_084, 511), (index0_085, 584)]

private noncomputable def block0Rows075 : SparseRow 86 Nat :=
  [(index0_066, 527), (index0_067, 551), (index0_068, 423), (index0_080, 365), (index0_081, 532), (index0_082, 322), (index0_083, 533), (index0_084, 348), (index0_085, 100)]

private noncomputable def block0Rows076 : SparseRow 86 Nat :=
  [(index0_069, 453), (index0_070, 860), (index0_071, 108), (index0_080, 778), (index0_081, 789), (index0_082, 164), (index0_083, 744), (index0_084, 999), (index0_085, 639)]

private noncomputable def block0Rows077 : SparseRow 86 Nat :=
  [(index0_069, 519), (index0_070, 357), (index0_071, 217), (index0_080, 168), (index0_081, 776), (index0_082, 446), (index0_083, 297), (index0_084, 491), (index0_085, 972)]

private noncomputable def block0Rows078 : SparseRow 86 Nat :=
  [(index0_042, 418), (index0_043, 820), (index0_044, 567), (index0_080, 574), (index0_081, 891), (index0_082, 983), (index0_083, 679), (index0_084, 647), (index0_085, 505)]

private noncomputable def block0Rows079 : SparseRow 86 Nat :=
  [(index0_042, 427), (index0_043, 341), (index0_044, 21), (index0_080, 877), (index0_081, 53), (index0_082, 644), (index0_083, 774), (index0_084, 856), (index0_085, 759)]

private noncomputable def block0Rows080 : SparseRow 86 Nat :=
  [(index0_063, 184), (index0_064, 119), (index0_065, 59), (index0_066, 247), (index0_067, 968), (index0_068, 459), (index0_080, 229), (index0_081, 733), (index0_082, 11), (index0_083, 823), (index0_084, 696), (index0_085, 900)]

private noncomputable def block0Rows081 : SparseRow 86 Nat :=
  [(index0_063, 663), (index0_064, 931), (index0_065, 548), (index0_066, 36), (index0_067, 753), (index0_068, 774), (index0_080, 605), (index0_081, 706), (index0_082, 407), (index0_083, 133), (index0_084, 317), (index0_085, 798)]

private noncomputable def block0Rows082 : SparseRow 86 Nat :=
  [(index0_063, 369), (index0_064, 845), (index0_065, 777), (index0_069, 65), (index0_070, 382), (index0_071, 167), (index0_080, 327), (index0_081, 534), (index0_082, 613), (index0_083, 420), (index0_084, 491), (index0_085, 1004)]

private noncomputable def block0Rows083 : SparseRow 86 Nat :=
  [(index0_063, 214), (index0_064, 310), (index0_065, 231), (index0_069, 428), (index0_070, 251), (index0_071, 452), (index0_080, 312), (index0_081, 484), (index0_082, 747), (index0_083, 644), (index0_084, 861), (index0_085, 45)]

private noncomputable def block0Rows084 : SparseRow 86 Nat :=
  [(index0_066, 362), (index0_067, 196), (index0_068, 885), (index0_069, 811), (index0_070, 523), (index0_071, 949), (index0_080, 21), (index0_081, 133), (index0_082, 801), (index0_083, 932), (index0_084, 550), (index0_085, 665)]

private noncomputable def block0Rows085 : SparseRow 86 Nat :=
  [(index0_066, 134), (index0_067, 914), (index0_068, 957), (index0_069, 905), (index0_070, 811), (index0_071, 411), (index0_080, 606), (index0_081, 383), (index0_082, 513), (index0_083, 857), (index0_084, 723), (index0_085, 937)]

noncomputable def block0Rows (i : Fin 86) : SparseRow 86 Nat :=
  if i.val < 43 then
    if i.val < 21 then
      if i.val < 10 then
        if i.val < 5 then
          if i.val < 2 then
            if i.val < 1 then
              block0Rows000
            else
              block0Rows001
          else
            if i.val < 3 then
              block0Rows002
            else
              if i.val < 4 then
                block0Rows003
              else
                block0Rows004
        else
          if i.val < 7 then
            if i.val < 6 then
              block0Rows005
            else
              block0Rows006
          else
            if i.val < 8 then
              block0Rows007
            else
              if i.val < 9 then
                block0Rows008
              else
                block0Rows009
      else
        if i.val < 15 then
          if i.val < 12 then
            if i.val < 11 then
              block0Rows010
            else
              block0Rows011
          else
            if i.val < 13 then
              block0Rows012
            else
              if i.val < 14 then
                block0Rows013
              else
                block0Rows014
        else
          if i.val < 18 then
            if i.val < 16 then
              block0Rows015
            else
              if i.val < 17 then
                block0Rows016
              else
                block0Rows017
          else
            if i.val < 19 then
              block0Rows018
            else
              if i.val < 20 then
                block0Rows019
              else
                block0Rows020
    else
      if i.val < 32 then
        if i.val < 26 then
          if i.val < 23 then
            if i.val < 22 then
              block0Rows021
            else
              block0Rows022
          else
            if i.val < 24 then
              block0Rows023
            else
              if i.val < 25 then
                block0Rows024
              else
                block0Rows025
        else
          if i.val < 29 then
            if i.val < 27 then
              block0Rows026
            else
              if i.val < 28 then
                block0Rows027
              else
                block0Rows028
          else
            if i.val < 30 then
              block0Rows029
            else
              if i.val < 31 then
                block0Rows030
              else
                block0Rows031
      else
        if i.val < 37 then
          if i.val < 34 then
            if i.val < 33 then
              block0Rows032
            else
              block0Rows033
          else
            if i.val < 35 then
              block0Rows034
            else
              if i.val < 36 then
                block0Rows035
              else
                block0Rows036
        else
          if i.val < 40 then
            if i.val < 38 then
              block0Rows037
            else
              if i.val < 39 then
                block0Rows038
              else
                block0Rows039
          else
            if i.val < 41 then
              block0Rows040
            else
              if i.val < 42 then
                block0Rows041
              else
                block0Rows042
  else
    if i.val < 64 then
      if i.val < 53 then
        if i.val < 48 then
          if i.val < 45 then
            if i.val < 44 then
              block0Rows043
            else
              block0Rows044
          else
            if i.val < 46 then
              block0Rows045
            else
              if i.val < 47 then
                block0Rows046
              else
                block0Rows047
        else
          if i.val < 50 then
            if i.val < 49 then
              block0Rows048
            else
              block0Rows049
          else
            if i.val < 51 then
              block0Rows050
            else
              if i.val < 52 then
                block0Rows051
              else
                block0Rows052
      else
        if i.val < 58 then
          if i.val < 55 then
            if i.val < 54 then
              block0Rows053
            else
              block0Rows054
          else
            if i.val < 56 then
              block0Rows055
            else
              if i.val < 57 then
                block0Rows056
              else
                block0Rows057
        else
          if i.val < 61 then
            if i.val < 59 then
              block0Rows058
            else
              if i.val < 60 then
                block0Rows059
              else
                block0Rows060
          else
            if i.val < 62 then
              block0Rows061
            else
              if i.val < 63 then
                block0Rows062
              else
                block0Rows063
    else
      if i.val < 75 then
        if i.val < 69 then
          if i.val < 66 then
            if i.val < 65 then
              block0Rows064
            else
              block0Rows065
          else
            if i.val < 67 then
              block0Rows066
            else
              if i.val < 68 then
                block0Rows067
              else
                block0Rows068
        else
          if i.val < 72 then
            if i.val < 70 then
              block0Rows069
            else
              if i.val < 71 then
                block0Rows070
              else
                block0Rows071
          else
            if i.val < 73 then
              block0Rows072
            else
              if i.val < 74 then
                block0Rows073
              else
                block0Rows074
      else
        if i.val < 80 then
          if i.val < 77 then
            if i.val < 76 then
              block0Rows075
            else
              block0Rows076
          else
            if i.val < 78 then
              block0Rows077
            else
              if i.val < 79 then
                block0Rows078
              else
                block0Rows079
        else
          if i.val < 83 then
            if i.val < 81 then
              block0Rows080
            else
              if i.val < 82 then
                block0Rows081
              else
                block0Rows082
          else
            if i.val < 84 then
              block0Rows083
            else
              if i.val < 85 then
                block0Rows084
              else
                block0Rows085

/-- The natural residue entry of the listed B.7 root block. -/
noncomputable def block0Entry (i j : Fin 86) : ℕ := rowValue (block0Rows i) j

/-- The listed B.7 root block in point-major normal component order. -/
noncomputable def block0 : Matrix (Fin 86) (Fin 86) (ZMod 1009) :=
  residueMatrix 1009 block0Rows

@[simp] theorem block0_apply (i j : Fin 86) :
    block0 i j = (block0Entry i j : ZMod 1009) := rfl

private noncomputable def index1_000 : Fin 74 := 0
private noncomputable def index1_001 : Fin 74 := 1
private noncomputable def index1_002 : Fin 74 := 2
private noncomputable def index1_003 : Fin 74 := 3
private noncomputable def index1_004 : Fin 74 := 4
private noncomputable def index1_005 : Fin 74 := 5
private noncomputable def index1_006 : Fin 74 := 6
private noncomputable def index1_007 : Fin 74 := 7
private noncomputable def index1_008 : Fin 74 := 8
private noncomputable def index1_009 : Fin 74 := 9
private noncomputable def index1_010 : Fin 74 := 10
private noncomputable def index1_011 : Fin 74 := 11
private noncomputable def index1_012 : Fin 74 := 12
private noncomputable def index1_013 : Fin 74 := 13
private noncomputable def index1_014 : Fin 74 := 14
private noncomputable def index1_015 : Fin 74 := 15
private noncomputable def index1_016 : Fin 74 := 16
private noncomputable def index1_017 : Fin 74 := 17
private noncomputable def index1_018 : Fin 74 := 18
private noncomputable def index1_019 : Fin 74 := 19
private noncomputable def index1_020 : Fin 74 := 20
private noncomputable def index1_021 : Fin 74 := 21
private noncomputable def index1_022 : Fin 74 := 22
private noncomputable def index1_023 : Fin 74 := 23
private noncomputable def index1_024 : Fin 74 := 24
private noncomputable def index1_025 : Fin 74 := 25
private noncomputable def index1_026 : Fin 74 := 26
private noncomputable def index1_027 : Fin 74 := 27
private noncomputable def index1_028 : Fin 74 := 28
private noncomputable def index1_029 : Fin 74 := 29
private noncomputable def index1_030 : Fin 74 := 30
private noncomputable def index1_031 : Fin 74 := 31
private noncomputable def index1_032 : Fin 74 := 32
private noncomputable def index1_033 : Fin 74 := 33
private noncomputable def index1_034 : Fin 74 := 34
private noncomputable def index1_035 : Fin 74 := 35
private noncomputable def index1_036 : Fin 74 := 36
private noncomputable def index1_037 : Fin 74 := 37
private noncomputable def index1_038 : Fin 74 := 38
private noncomputable def index1_039 : Fin 74 := 39
private noncomputable def index1_040 : Fin 74 := 40
private noncomputable def index1_041 : Fin 74 := 41
private noncomputable def index1_042 : Fin 74 := 42
private noncomputable def index1_043 : Fin 74 := 43
private noncomputable def index1_044 : Fin 74 := 44
private noncomputable def index1_045 : Fin 74 := 45
private noncomputable def index1_046 : Fin 74 := 46
private noncomputable def index1_047 : Fin 74 := 47
private noncomputable def index1_048 : Fin 74 := 48
private noncomputable def index1_049 : Fin 74 := 49
private noncomputable def index1_050 : Fin 74 := 50
private noncomputable def index1_051 : Fin 74 := 51
private noncomputable def index1_052 : Fin 74 := 52
private noncomputable def index1_053 : Fin 74 := 53
private noncomputable def index1_054 : Fin 74 := 54
private noncomputable def index1_055 : Fin 74 := 55
private noncomputable def index1_056 : Fin 74 := 56
private noncomputable def index1_057 : Fin 74 := 57
private noncomputable def index1_058 : Fin 74 := 58
private noncomputable def index1_059 : Fin 74 := 59
private noncomputable def index1_060 : Fin 74 := 60
private noncomputable def index1_061 : Fin 74 := 61
private noncomputable def index1_062 : Fin 74 := 62
private noncomputable def index1_063 : Fin 74 := 63
private noncomputable def index1_064 : Fin 74 := 64
private noncomputable def index1_065 : Fin 74 := 65
private noncomputable def index1_066 : Fin 74 := 66
private noncomputable def index1_067 : Fin 74 := 67
private noncomputable def index1_068 : Fin 74 := 68
private noncomputable def index1_069 : Fin 74 := 69
private noncomputable def index1_070 : Fin 74 := 70
private noncomputable def index1_071 : Fin 74 := 71
private noncomputable def index1_072 : Fin 74 := 72
private noncomputable def index1_073 : Fin 74 := 73

private noncomputable def block1Rows000 : SparseRow 74 Nat :=
  [(index1_009, 41), (index1_053, 103), (index1_054, 576), (index1_055, 699), (index1_062, 498), (index1_063, 344), (index1_068, 811), (index1_069, 164), (index1_070, 493), (index1_071, 164), (index1_072, 589), (index1_073, 9)]

private noncomputable def block1Rows001 : SparseRow 74 Nat :=
  [(index1_009, 1008), (index1_053, 225), (index1_054, 788), (index1_055, 259), (index1_068, 699), (index1_069, 669), (index1_070, 156), (index1_071, 669), (index1_072, 156), (index1_073, 862)]

private noncomputable def block1Rows002 : SparseRow 74 Nat :=
  [(index1_020, 260), (index1_056, 414), (index1_057, 700), (index1_058, 444), (index1_064, 720), (index1_065, 315), (index1_068, 980), (index1_069, 155), (index1_070, 476), (index1_071, 155), (index1_072, 893), (index1_073, 419)]

private noncomputable def block1Rows003 : SparseRow 74 Nat :=
  [(index1_020, 1008), (index1_056, 476), (index1_057, 33), (index1_058, 521), (index1_068, 75), (index1_069, 636), (index1_070, 671), (index1_071, 636), (index1_072, 671), (index1_073, 803)]

private noncomputable def block1Rows004 : SparseRow 74 Nat :=
  [(index1_031, 418), (index1_059, 598), (index1_060, 881), (index1_061, 316), (index1_066, 750), (index1_067, 202), (index1_068, 484), (index1_069, 239), (index1_070, 787), (index1_071, 239), (index1_072, 181), (index1_073, 801)]

private noncomputable def block1Rows005 : SparseRow 74 Nat :=
  [(index1_031, 1008), (index1_059, 489), (index1_060, 464), (index1_061, 2), (index1_068, 954), (index1_069, 71), (index1_070, 378), (index1_071, 71), (index1_072, 378), (index1_073, 414)]

private noncomputable def block1Rows006 : SparseRow 74 Nat :=
  [(index1_002, 469), (index1_009, 566), (index1_032, 393), (index1_033, 341), (index1_034, 257), (index1_053, 211), (index1_054, 622), (index1_055, 329), (index1_062, 359), (index1_063, 703), (index1_068, 825), (index1_069, 600), (index1_070, 317), (index1_071, 202), (index1_072, 382), (index1_073, 735)]

private noncomputable def block1Rows007 : SparseRow 74 Nat :=
  [(index1_002, 87), (index1_009, 503), (index1_032, 350), (index1_033, 403), (index1_034, 183), (index1_053, 514), (index1_054, 905), (index1_055, 691), (index1_062, 942), (index1_063, 495), (index1_068, 15), (index1_069, 360), (index1_070, 599), (index1_071, 216), (index1_072, 997), (index1_073, 997)]

private noncomputable def block1Rows008 : SparseRow 74 Nat :=
  [(index1_012, 645), (index1_020, 106), (index1_032, 890), (index1_033, 800), (index1_034, 474), (index1_056, 535), (index1_057, 533), (index1_058, 675), (index1_064, 364), (index1_065, 100), (index1_068, 1008), (index1_069, 632), (index1_070, 60), (index1_071, 339), (index1_072, 514), (index1_073, 351)]

private noncomputable def block1Rows009 : SparseRow 74 Nat :=
  [(index1_012, 405), (index1_020, 442), (index1_032, 603), (index1_033, 919), (index1_034, 574), (index1_056, 925), (index1_057, 144), (index1_058, 26), (index1_064, 402), (index1_065, 58), (index1_068, 346), (index1_069, 934), (index1_070, 37), (index1_071, 510), (index1_072, 330), (index1_073, 134)]

private noncomputable def block1Rows010 : SparseRow 74 Nat :=
  [(index1_022, 788), (index1_031, 631), (index1_032, 415), (index1_033, 241), (index1_034, 492), (index1_059, 791), (index1_060, 575), (index1_061, 768), (index1_066, 992), (index1_067, 64), (index1_068, 990), (index1_069, 218), (index1_070, 577), (index1_071, 552), (index1_072, 559), (index1_073, 813)]

private noncomputable def block1Rows011 : SparseRow 74 Nat :=
  [(index1_022, 674), (index1_031, 783), (index1_032, 920), (index1_033, 318), (index1_034, 355), (index1_059, 305), (index1_060, 718), (index1_061, 500), (index1_066, 58), (index1_067, 445), (index1_068, 31), (index1_069, 683), (index1_070, 880), (index1_071, 714), (index1_072, 546), (index1_073, 883)]

private noncomputable def block1Rows012 : SparseRow 74 Nat :=
  [(index1_000, 917), (index1_003, 987), (index1_009, 504), (index1_035, 138), (index1_036, 323), (index1_037, 36), (index1_053, 347), (index1_054, 522), (index1_055, 787), (index1_062, 129), (index1_063, 877), (index1_068, 302), (index1_069, 848), (index1_070, 769), (index1_071, 214), (index1_072, 733), (index1_073, 600)]

private noncomputable def block1Rows013 : SparseRow 74 Nat :=
  [(index1_000, 665), (index1_003, 665), (index1_009, 726), (index1_035, 710), (index1_036, 710), (index1_037, 778), (index1_053, 424), (index1_054, 134), (index1_055, 907), (index1_062, 729), (index1_063, 585), (index1_068, 119), (index1_069, 211), (index1_070, 906), (index1_071, 643), (index1_072, 531), (index1_073, 726)]

private noncomputable def block1Rows014 : SparseRow 74 Nat :=
  [(index1_013, 201), (index1_020, 819), (index1_035, 902), (index1_036, 994), (index1_037, 41), (index1_056, 273), (index1_057, 5), (index1_058, 884), (index1_064, 545), (index1_065, 388), (index1_068, 692), (index1_069, 623), (index1_070, 265), (index1_071, 333), (index1_072, 436), (index1_073, 461)]

private noncomputable def block1Rows015 : SparseRow 74 Nat :=
  [(index1_013, 267), (index1_020, 350), (index1_035, 735), (index1_036, 134), (index1_037, 463), (index1_056, 893), (index1_057, 791), (index1_058, 831), (index1_064, 321), (index1_065, 1006), (index1_068, 1000), (index1_069, 289), (index1_070, 237), (index1_071, 981), (index1_072, 527), (index1_073, 922)]

private noncomputable def block1Rows016 : SparseRow 74 Nat :=
  [(index1_023, 613), (index1_031, 800), (index1_035, 362), (index1_036, 921), (index1_037, 1005), (index1_059, 598), (index1_060, 565), (index1_061, 559), (index1_066, 945), (index1_067, 253), (index1_068, 684), (index1_069, 35), (index1_070, 299), (index1_071, 932), (index1_072, 230), (index1_073, 603)]

private noncomputable def block1Rows017 : SparseRow 74 Nat :=
  [(index1_023, 532), (index1_031, 505), (index1_035, 24), (index1_036, 788), (index1_037, 445), (index1_059, 493), (index1_060, 922), (index1_061, 858), (index1_066, 841), (index1_067, 438), (index1_068, 958), (index1_069, 909), (index1_070, 478), (index1_071, 625), (index1_072, 590), (index1_073, 143)]

private noncomputable def block1Rows018 : SparseRow 74 Nat :=
  [(index1_004, 325), (index1_009, 509), (index1_038, 874), (index1_039, 539), (index1_040, 964), (index1_053, 118), (index1_054, 133), (index1_055, 466), (index1_062, 217), (index1_063, 60), (index1_068, 184), (index1_069, 113), (index1_070, 782), (index1_071, 159), (index1_072, 669), (index1_073, 172)]

private noncomputable def block1Rows019 : SparseRow 74 Nat :=
  [(index1_004, 312), (index1_009, 529), (index1_038, 861), (index1_039, 573), (index1_040, 29), (index1_053, 103), (index1_054, 362), (index1_055, 875), (index1_062, 881), (index1_063, 9), (index1_068, 610), (index1_069, 324), (index1_070, 54), (index1_071, 58), (index1_072, 8), (index1_073, 668)]

private noncomputable def block1Rows020 : SparseRow 74 Nat :=
  [(index1_001, 97), (index1_014, 653), (index1_020, 860), (index1_038, 160), (index1_039, 154), (index1_040, 394), (index1_056, 678), (index1_057, 72), (index1_058, 354), (index1_064, 697), (index1_065, 267), (index1_068, 673), (index1_069, 339), (index1_070, 877), (index1_071, 736), (index1_072, 328), (index1_073, 381)]

private noncomputable def block1Rows021 : SparseRow 74 Nat :=
  [(index1_001, 762), (index1_014, 762), (index1_020, 540), (index1_038, 712), (index1_039, 978), (index1_040, 944), (index1_056, 441), (index1_057, 131), (index1_058, 482), (index1_064, 139), (index1_065, 324), (index1_068, 153), (index1_069, 948), (index1_070, 40), (index1_071, 751), (index1_072, 652), (index1_073, 425)]

private noncomputable def block1Rows022 : SparseRow 74 Nat :=
  [(index1_024, 422), (index1_031, 315), (index1_038, 545), (index1_039, 918), (index1_040, 386), (index1_059, 471), (index1_060, 740), (index1_061, 947), (index1_066, 801), (index1_067, 418), (index1_068, 485), (index1_069, 134), (index1_070, 813), (index1_071, 472), (index1_072, 506), (index1_073, 620)]

private noncomputable def block1Rows023 : SparseRow 74 Nat :=
  [(index1_024, 279), (index1_031, 861), (index1_038, 975), (index1_039, 155), (index1_040, 859), (index1_059, 46), (index1_060, 17), (index1_061, 453), (index1_066, 10), (index1_067, 481), (index1_068, 665), (index1_069, 172), (index1_070, 567), (index1_071, 862), (index1_072, 229), (index1_073, 950)]

private noncomputable def block1Rows024 : SparseRow 74 Nat :=
  [(index1_005, 394), (index1_009, 144), (index1_041, 170), (index1_042, 914), (index1_043, 599), (index1_053, 184), (index1_054, 690), (index1_055, 823), (index1_062, 619), (index1_063, 955), (index1_068, 679), (index1_069, 682), (index1_070, 839), (index1_071, 254), (index1_072, 115), (index1_073, 778)]

private noncomputable def block1Rows025 : SparseRow 74 Nat :=
  [(index1_005, 15), (index1_009, 784), (index1_041, 532), (index1_042, 847), (index1_043, 344), (index1_053, 22), (index1_054, 730), (index1_055, 799), (index1_062, 519), (index1_063, 610), (index1_068, 156), (index1_069, 709), (index1_070, 447), (index1_071, 518), (index1_072, 875), (index1_073, 54)]

private noncomputable def block1Rows026 : SparseRow 74 Nat :=
  [(index1_015, 806), (index1_020, 77), (index1_041, 767), (index1_042, 543), (index1_043, 720), (index1_056, 2), (index1_057, 984), (index1_058, 493), (index1_064, 853), (index1_065, 700), (index1_068, 948), (index1_069, 649), (index1_070, 157), (index1_071, 436), (index1_072, 758), (index1_073, 432)]

private noncomputable def block1Rows027 : SparseRow 74 Nat :=
  [(index1_015, 905), (index1_020, 283), (index1_041, 427), (index1_042, 852), (index1_043, 870), (index1_056, 608), (index1_057, 55), (index1_058, 725), (index1_064, 741), (index1_065, 495), (index1_068, 555), (index1_069, 455), (index1_070, 417), (index1_071, 278), (index1_072, 630), (index1_073, 575)]

private noncomputable def block1Rows028 : SparseRow 74 Nat :=
  [(index1_025, 741), (index1_031, 167), (index1_041, 809), (index1_042, 487), (index1_043, 864), (index1_059, 366), (index1_060, 720), (index1_061, 623), (index1_066, 457), (index1_067, 506), (index1_068, 359), (index1_069, 519), (index1_070, 131), (index1_071, 397), (index1_072, 518), (index1_073, 698)]

private noncomputable def block1Rows029 : SparseRow 74 Nat :=
  [(index1_025, 411), (index1_031, 591), (index1_041, 225), (index1_042, 48), (index1_043, 77), (index1_059, 784), (index1_060, 941), (index1_061, 603), (index1_066, 118), (index1_067, 373), (index1_068, 852), (index1_069, 71), (index1_070, 390), (index1_071, 675), (index1_072, 512), (index1_073, 592)]

private noncomputable def block1Rows030 : SparseRow 74 Nat :=
  [(index1_006, 268), (index1_009, 226), (index1_044, 733), (index1_045, 753), (index1_046, 311), (index1_053, 671), (index1_054, 736), (index1_055, 434), (index1_062, 143), (index1_063, 58), (index1_068, 444), (index1_069, 861), (index1_070, 61), (index1_071, 642), (index1_072, 893), (index1_073, 105)]

private noncomputable def block1Rows031 : SparseRow 74 Nat :=
  [(index1_006, 338), (index1_009, 782), (index1_044, 902), (index1_045, 273), (index1_046, 713), (index1_053, 118), (index1_054, 352), (index1_055, 357), (index1_062, 177), (index1_063, 364), (index1_068, 863), (index1_069, 814), (index1_070, 588), (index1_071, 972), (index1_072, 807), (index1_073, 711)]

private noncomputable def block1Rows032 : SparseRow 74 Nat :=
  [(index1_016, 304), (index1_020, 728), (index1_044, 132), (index1_045, 103), (index1_046, 310), (index1_056, 86), (index1_057, 1003), (index1_058, 537), (index1_064, 340), (index1_065, 983), (index1_068, 759), (index1_069, 410), (index1_070, 859), (index1_071, 233), (index1_072, 774), (index1_073, 192)]

private noncomputable def block1Rows033 : SparseRow 74 Nat :=
  [(index1_016, 449), (index1_020, 199), (index1_044, 52), (index1_045, 938), (index1_046, 308), (index1_056, 330), (index1_057, 222), (index1_058, 314), (index1_064, 484), (index1_065, 253), (index1_068, 21), (index1_069, 759), (index1_070, 361), (index1_071, 486), (index1_072, 538), (index1_073, 828)]

private noncomputable def block1Rows034 : SparseRow 74 Nat :=
  [(index1_026, 467), (index1_031, 949), (index1_044, 905), (index1_045, 54), (index1_046, 14), (index1_059, 664), (index1_060, 486), (index1_061, 987), (index1_066, 902), (index1_067, 672), (index1_068, 746), (index1_069, 43), (index1_070, 384), (index1_071, 193), (index1_072, 285), (index1_073, 264)]

private noncomputable def block1Rows035 : SparseRow 74 Nat :=
  [(index1_026, 402), (index1_031, 845), (index1_044, 836), (index1_045, 523), (index1_046, 969), (index1_059, 164), (index1_060, 829), (index1_061, 869), (index1_066, 546), (index1_067, 558), (index1_068, 901), (index1_069, 562), (index1_070, 82), (index1_071, 917), (index1_072, 941), (index1_073, 565)]

private noncomputable def block1Rows036 : SparseRow 74 Nat :=
  [(index1_007, 125), (index1_009, 135), (index1_047, 78), (index1_048, 241), (index1_049, 193), (index1_053, 531), (index1_054, 565), (index1_055, 703), (index1_062, 397), (index1_063, 693), (index1_068, 440), (index1_069, 875), (index1_070, 961), (index1_071, 634), (index1_072, 545), (index1_073, 228)]

private noncomputable def block1Rows037 : SparseRow 74 Nat :=
  [(index1_007, 120), (index1_009, 735), (index1_047, 527), (index1_048, 566), (index1_049, 148), (index1_053, 950), (index1_054, 874), (index1_055, 228), (index1_062, 692), (index1_063, 578), (index1_068, 85), (index1_069, 77), (index1_070, 767), (index1_071, 246), (index1_072, 1008), (index1_073, 385)]

private noncomputable def block1Rows038 : SparseRow 74 Nat :=
  [(index1_017, 91), (index1_020, 385), (index1_047, 43), (index1_048, 507), (index1_049, 77), (index1_056, 727), (index1_057, 223), (index1_058, 274), (index1_064, 112), (index1_065, 770), (index1_068, 684), (index1_069, 414), (index1_070, 889), (index1_071, 381), (index1_072, 603), (index1_073, 758)]

private noncomputable def block1Rows039 : SparseRow 74 Nat :=
  [(index1_017, 151), (index1_020, 406), (index1_047, 283), (index1_048, 67), (index1_049, 368), (index1_056, 537), (index1_057, 963), (index1_058, 849), (index1_064, 612), (index1_065, 26), (index1_068, 44), (index1_069, 822), (index1_070, 815), (index1_071, 44), (index1_072, 848), (index1_073, 239)]

private noncomputable def block1Rows040 : SparseRow 74 Nat :=
  [(index1_027, 128), (index1_031, 353), (index1_047, 681), (index1_048, 168), (index1_049, 988), (index1_059, 626), (index1_060, 181), (index1_061, 14), (index1_066, 770), (index1_067, 512), (index1_068, 630), (index1_069, 238), (index1_070, 632), (index1_071, 63), (index1_072, 714), (index1_073, 963)]

private noncomputable def block1Rows041 : SparseRow 74 Nat :=
  [(index1_027, 888), (index1_031, 494), (index1_047, 446), (index1_048, 481), (index1_049, 327), (index1_059, 984), (index1_060, 42), (index1_061, 901), (index1_066, 820), (index1_067, 966), (index1_068, 297), (index1_069, 726), (index1_070, 110), (index1_071, 977), (index1_072, 285), (index1_073, 624)]

private noncomputable def block1Rows042 : SparseRow 74 Nat :=
  [(index1_008, 478), (index1_009, 577), (index1_050, 52), (index1_051, 500), (index1_052, 931), (index1_053, 273), (index1_054, 506), (index1_055, 105), (index1_062, 777), (index1_063, 74), (index1_068, 377), (index1_069, 886), (index1_070, 166), (index1_071, 522), (index1_072, 405), (index1_073, 959)]

private noncomputable def block1Rows043 : SparseRow 74 Nat :=
  [(index1_008, 136), (index1_009, 675), (index1_050, 178), (index1_051, 922), (index1_052, 469), (index1_053, 30), (index1_054, 414), (index1_055, 966), (index1_062, 431), (index1_063, 344), (index1_068, 907), (index1_069, 886), (index1_070, 388), (index1_071, 274), (index1_072, 752), (index1_073, 170)]

private noncomputable def block1Rows044 : SparseRow 74 Nat :=
  [(index1_018, 421), (index1_020, 802), (index1_050, 100), (index1_051, 492), (index1_052, 639), (index1_056, 357), (index1_057, 612), (index1_058, 800), (index1_064, 147), (index1_065, 561), (index1_068, 457), (index1_069, 172), (index1_070, 189), (index1_071, 814), (index1_072, 142), (index1_073, 686)]

private noncomputable def block1Rows045 : SparseRow 74 Nat :=
  [(index1_018, 499), (index1_020, 222), (index1_050, 668), (index1_051, 98), (index1_052, 312), (index1_056, 142), (index1_057, 474), (index1_058, 639), (index1_064, 458), (index1_065, 816), (index1_068, 592), (index1_069, 9), (index1_070, 435), (index1_071, 768), (index1_072, 802), (index1_073, 126)]

private noncomputable def block1Rows046 : SparseRow 74 Nat :=
  [(index1_028, 628), (index1_031, 369), (index1_050, 245), (index1_051, 652), (index1_052, 978), (index1_059, 270), (index1_060, 123), (index1_061, 351), (index1_066, 193), (index1_067, 913), (index1_068, 422), (index1_069, 402), (index1_070, 19), (index1_071, 899), (index1_072, 93), (index1_073, 70)]

private noncomputable def block1Rows047 : SparseRow 74 Nat :=
  [(index1_028, 573), (index1_031, 605), (index1_050, 558), (index1_051, 375), (index1_052, 40), (index1_059, 994), (index1_060, 968), (index1_061, 914), (index1_066, 467), (index1_067, 715), (index1_068, 240), (index1_069, 701), (index1_070, 977), (index1_071, 839), (index1_072, 480), (index1_073, 187)]

private noncomputable def block1Rows048 : SparseRow 74 Nat :=
  [(index1_009, 41), (index1_010, 608), (index1_019, 804), (index1_020, 996), (index1_053, 16), (index1_054, 471), (index1_055, 700), (index1_056, 399), (index1_057, 212), (index1_058, 149), (index1_062, 180), (index1_063, 125), (index1_064, 504), (index1_065, 748), (index1_068, 140), (index1_069, 119), (index1_070, 37), (index1_071, 119), (index1_072, 907), (index1_073, 736)]

private noncomputable def block1Rows049 : SparseRow 74 Nat :=
  [(index1_009, 1008), (index1_010, 59), (index1_019, 59), (index1_020, 555), (index1_053, 202), (index1_054, 49), (index1_055, 956), (index1_056, 303), (index1_057, 742), (index1_058, 715), (index1_068, 110), (index1_069, 846), (index1_070, 201), (index1_071, 846), (index1_072, 201), (index1_073, 594)]

private noncomputable def block1Rows050 : SparseRow 74 Nat :=
  [(index1_009, 41), (index1_011, 626), (index1_029, 968), (index1_031, 383), (index1_053, 557), (index1_054, 758), (index1_055, 739), (index1_059, 119), (index1_060, 177), (index1_061, 658), (index1_062, 665), (index1_063, 788), (index1_066, 708), (index1_067, 180), (index1_068, 13), (index1_069, 123), (index1_070, 525), (index1_071, 123), (index1_072, 815), (index1_073, 19)]

private noncomputable def block1Rows051 : SparseRow 74 Nat :=
  [(index1_009, 1008), (index1_011, 157), (index1_029, 157), (index1_031, 576), (index1_053, 393), (index1_054, 112), (index1_055, 514), (index1_059, 697), (index1_060, 627), (index1_061, 186), (index1_068, 906), (index1_069, 196), (index1_070, 432), (index1_071, 196), (index1_072, 432), (index1_073, 841)]

private noncomputable def block1Rows052 : SparseRow 74 Nat :=
  [(index1_020, 260), (index1_021, 568), (index1_030, 463), (index1_031, 18), (index1_056, 457), (index1_057, 775), (index1_058, 131), (index1_059, 183), (index1_060, 719), (index1_061, 406), (index1_064, 532), (index1_065, 812), (index1_066, 981), (index1_067, 490), (index1_068, 151), (index1_069, 66), (index1_070, 68), (index1_071, 66), (index1_072, 951), (index1_073, 550)]

private noncomputable def block1Rows053 : SparseRow 74 Nat :=
  [(index1_020, 1008), (index1_021, 122), (index1_030, 122), (index1_031, 251), (index1_056, 603), (index1_057, 987), (index1_058, 727), (index1_059, 224), (index1_060, 354), (index1_061, 1001), (index1_068, 368), (index1_069, 62), (index1_070, 98), (index1_071, 62), (index1_072, 98), (index1_073, 728)]

private noncomputable def block1Rows054 : SparseRow 74 Nat :=
  [(index1_032, 81), (index1_033, 974), (index1_034, 559), (index1_068, 320), (index1_069, 1), (index1_070, 934), (index1_071, 824), (index1_072, 327), (index1_073, 988)]

private noncomputable def block1Rows055 : SparseRow 74 Nat :=
  [(index1_032, 375), (index1_033, 54), (index1_034, 591), (index1_068, 948), (index1_069, 698), (index1_070, 185), (index1_071, 158), (index1_072, 371), (index1_073, 329)]

private noncomputable def block1Rows056 : SparseRow 74 Nat :=
  [(index1_035, 261), (index1_036, 925), (index1_037, 745), (index1_068, 169), (index1_069, 928), (index1_070, 123), (index1_071, 490), (index1_072, 94), (index1_073, 32)]

private noncomputable def block1Rows057 : SparseRow 74 Nat :=
  [(index1_035, 710), (index1_036, 710), (index1_037, 778), (index1_068, 277), (index1_069, 110), (index1_070, 951), (index1_071, 931), (index1_072, 380), (index1_073, 310)]

private noncomputable def block1Rows058 : SparseRow 74 Nat :=
  [(index1_038, 588), (index1_039, 882), (index1_040, 761), (index1_068, 429), (index1_069, 647), (index1_070, 32), (index1_071, 433), (index1_072, 137), (index1_073, 264)]

private noncomputable def block1Rows059 : SparseRow 74 Nat :=
  [(index1_038, 712), (index1_039, 978), (index1_040, 944), (index1_068, 644), (index1_069, 492), (index1_070, 801), (index1_071, 684), (index1_072, 6), (index1_073, 759)]

private noncomputable def block1Rows060 : SparseRow 74 Nat :=
  [(index1_041, 18), (index1_042, 345), (index1_043, 566), (index1_068, 803), (index1_069, 548), (index1_070, 421), (index1_071, 18), (index1_072, 379), (index1_073, 73)]

private noncomputable def block1Rows061 : SparseRow 74 Nat :=
  [(index1_041, 51), (index1_042, 462), (index1_043, 149), (index1_068, 960), (index1_069, 49), (index1_070, 398), (index1_071, 655), (index1_072, 928), (index1_073, 56)]

private noncomputable def block1Rows062 : SparseRow 74 Nat :=
  [(index1_044, 134), (index1_045, 860), (index1_046, 47), (index1_068, 427), (index1_069, 686), (index1_070, 602), (index1_071, 564), (index1_072, 671), (index1_073, 665)]

private noncomputable def block1Rows063 : SparseRow 74 Nat :=
  [(index1_044, 355), (index1_045, 287), (index1_046, 886), (index1_068, 886), (index1_069, 681), (index1_070, 109), (index1_071, 308), (index1_072, 231), (index1_073, 288)]

private noncomputable def block1Rows064 : SparseRow 74 Nat :=
  [(index1_047, 247), (index1_048, 163), (index1_049, 772), (index1_068, 332), (index1_069, 835), (index1_070, 374), (index1_071, 573), (index1_072, 488), (index1_073, 751)]

private noncomputable def block1Rows065 : SparseRow 74 Nat :=
  [(index1_047, 483), (index1_048, 939), (index1_049, 206), (index1_068, 257), (index1_069, 716), (index1_070, 959), (index1_071, 868), (index1_072, 212), (index1_073, 972)]

private noncomputable def block1Rows066 : SparseRow 74 Nat :=
  [(index1_050, 726), (index1_051, 373), (index1_052, 719), (index1_068, 127), (index1_069, 122), (index1_070, 727), (index1_071, 387), (index1_072, 157), (index1_073, 122)]

private noncomputable def block1Rows067 : SparseRow 74 Nat :=
  [(index1_050, 763), (index1_051, 970), (index1_052, 652), (index1_068, 920), (index1_069, 465), (index1_070, 500), (index1_071, 453), (index1_072, 235), (index1_073, 656)]

private noncomputable def block1Rows068 : SparseRow 74 Nat :=
  [(index1_035, 511), (index1_036, 495), (index1_037, 876), (index1_038, 570), (index1_039, 16), (index1_040, 268), (index1_068, 820), (index1_069, 647), (index1_070, 50), (index1_071, 534), (index1_072, 329), (index1_073, 798)]

private noncomputable def block1Rows069 : SparseRow 74 Nat :=
  [(index1_035, 516), (index1_036, 401), (index1_037, 682), (index1_038, 54), (index1_039, 358), (index1_040, 53), (index1_068, 865), (index1_069, 218), (index1_070, 711), (index1_071, 369), (index1_072, 824), (index1_073, 331)]

private noncomputable def block1Rows070 : SparseRow 74 Nat :=
  [(index1_035, 771), (index1_036, 46), (index1_037, 394), (index1_041, 136), (index1_042, 188), (index1_043, 681), (index1_068, 277), (index1_069, 642), (index1_070, 114), (index1_071, 1002), (index1_072, 655), (index1_073, 716)]

private noncomputable def block1Rows071 : SparseRow 74 Nat :=
  [(index1_035, 45), (index1_036, 271), (index1_037, 848), (index1_041, 334), (index1_042, 956), (index1_043, 100), (index1_068, 659), (index1_069, 855), (index1_070, 697), (index1_071, 797), (index1_072, 337), (index1_073, 172)]

private noncomputable def block1Rows072 : SparseRow 74 Nat :=
  [(index1_038, 229), (index1_039, 363), (index1_040, 998), (index1_041, 76), (index1_042, 420), (index1_043, 327), (index1_068, 522), (index1_069, 183), (index1_070, 587), (index1_071, 310), (index1_072, 578), (index1_073, 586)]

private noncomputable def block1Rows073 : SparseRow 74 Nat :=
  [(index1_038, 352), (index1_039, 820), (index1_040, 599), (index1_041, 40), (index1_042, 29), (index1_043, 704), (index1_068, 740), (index1_069, 147), (index1_070, 830), (index1_071, 165), (index1_072, 703), (index1_073, 450)]

noncomputable def block1Rows (i : Fin 74) : SparseRow 74 Nat :=
  if i.val < 37 then
    if i.val < 18 then
      if i.val < 9 then
        if i.val < 4 then
          if i.val < 2 then
            if i.val < 1 then
              block1Rows000
            else
              block1Rows001
          else
            if i.val < 3 then
              block1Rows002
            else
              block1Rows003
        else
          if i.val < 6 then
            if i.val < 5 then
              block1Rows004
            else
              block1Rows005
          else
            if i.val < 7 then
              block1Rows006
            else
              if i.val < 8 then
                block1Rows007
              else
                block1Rows008
      else
        if i.val < 13 then
          if i.val < 11 then
            if i.val < 10 then
              block1Rows009
            else
              block1Rows010
          else
            if i.val < 12 then
              block1Rows011
            else
              block1Rows012
        else
          if i.val < 15 then
            if i.val < 14 then
              block1Rows013
            else
              block1Rows014
          else
            if i.val < 16 then
              block1Rows015
            else
              if i.val < 17 then
                block1Rows016
              else
                block1Rows017
    else
      if i.val < 27 then
        if i.val < 22 then
          if i.val < 20 then
            if i.val < 19 then
              block1Rows018
            else
              block1Rows019
          else
            if i.val < 21 then
              block1Rows020
            else
              block1Rows021
        else
          if i.val < 24 then
            if i.val < 23 then
              block1Rows022
            else
              block1Rows023
          else
            if i.val < 25 then
              block1Rows024
            else
              if i.val < 26 then
                block1Rows025
              else
                block1Rows026
      else
        if i.val < 32 then
          if i.val < 29 then
            if i.val < 28 then
              block1Rows027
            else
              block1Rows028
          else
            if i.val < 30 then
              block1Rows029
            else
              if i.val < 31 then
                block1Rows030
              else
                block1Rows031
        else
          if i.val < 34 then
            if i.val < 33 then
              block1Rows032
            else
              block1Rows033
          else
            if i.val < 35 then
              block1Rows034
            else
              if i.val < 36 then
                block1Rows035
              else
                block1Rows036
  else
    if i.val < 55 then
      if i.val < 46 then
        if i.val < 41 then
          if i.val < 39 then
            if i.val < 38 then
              block1Rows037
            else
              block1Rows038
          else
            if i.val < 40 then
              block1Rows039
            else
              block1Rows040
        else
          if i.val < 43 then
            if i.val < 42 then
              block1Rows041
            else
              block1Rows042
          else
            if i.val < 44 then
              block1Rows043
            else
              if i.val < 45 then
                block1Rows044
              else
                block1Rows045
      else
        if i.val < 50 then
          if i.val < 48 then
            if i.val < 47 then
              block1Rows046
            else
              block1Rows047
          else
            if i.val < 49 then
              block1Rows048
            else
              block1Rows049
        else
          if i.val < 52 then
            if i.val < 51 then
              block1Rows050
            else
              block1Rows051
          else
            if i.val < 53 then
              block1Rows052
            else
              if i.val < 54 then
                block1Rows053
              else
                block1Rows054
    else
      if i.val < 64 then
        if i.val < 59 then
          if i.val < 57 then
            if i.val < 56 then
              block1Rows055
            else
              block1Rows056
          else
            if i.val < 58 then
              block1Rows057
            else
              block1Rows058
        else
          if i.val < 61 then
            if i.val < 60 then
              block1Rows059
            else
              block1Rows060
          else
            if i.val < 62 then
              block1Rows061
            else
              if i.val < 63 then
                block1Rows062
              else
                block1Rows063
      else
        if i.val < 69 then
          if i.val < 66 then
            if i.val < 65 then
              block1Rows064
            else
              block1Rows065
          else
            if i.val < 67 then
              block1Rows066
            else
              if i.val < 68 then
                block1Rows067
              else
                block1Rows068
        else
          if i.val < 71 then
            if i.val < 70 then
              block1Rows069
            else
              block1Rows070
          else
            if i.val < 72 then
              block1Rows071
            else
              if i.val < 73 then
                block1Rows072
              else
                block1Rows073

/-- The natural residue entry of the listed B.7 root block. -/
noncomputable def block1Entry (i j : Fin 74) : ℕ := rowValue (block1Rows i) j

/-- The listed B.7 root block in point-major normal component order. -/
noncomputable def block1 : Matrix (Fin 74) (Fin 74) (ZMod 1009) :=
  residueMatrix 1009 block1Rows

@[simp] theorem block1_apply (i j : Fin 74) :
    block1 i j = (block1Entry i j : ZMod 1009) := rfl


end IdealGeneration.CubicSupported.B7RootCertificate
