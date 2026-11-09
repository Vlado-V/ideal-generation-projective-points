module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace IdealGeneration

private theorem prime1009 : Nat.Prime 1009 := by decide +kernel
local instance : Fact (Nat.Prime 1009) := ⟨prime1009⟩

/-- Evaluation matrix reconstructed from Appendix C.3, seed 851. -/
def pairEvaluationMatrix : Matrix (Fin 26) (Fin 26) (ZMod 1009) :=
  !![249, 983, 728, 620, 400, 306, 374, 787, 543, 48, 524, 807, 332, 171, 387, 633, 782, 964, 666, 303, 888, 459, 715, 218, 717, 400;
    297, 282, 976, 556, 655, 740, 841, 973, 743, 127, 966, 937, 458, 734, 918, 52, 280, 722, 189, 201, 389, 18, 582, 701, 681, 629;
    800, 244, 929, 937, 338, 636, 216, 947, 811, 136, 519, 667, 966, 984, 675, 898, 796, 208, 454, 336, 690, 979, 14, 850, 758, 54;
    654, 52, 186, 831, 929, 150, 985, 893, 359, 528, 175, 987, 664, 220, 108, 335, 736, 568, 644, 91, 241, 533, 693, 706, 188, 655;
    42, 619, 121, 6, 858, 155, 541, 367, 424, 336, 852, 341, 610, 611, 38, 323, 863, 28, 710, 597, 658, 658, 494, 155, 878, 606;
    637, 422, 361, 901, 903, 9, 454, 535, 281, 889, 993, 671, 647, 570, 830, 144, 390, 116, 928, 672, 835, 283, 237, 105, 74, 736;
    539, 59, 174, 706, 659, 431, 987, 893, 864, 115, 710, 947, 735, 919, 202, 470, 136, 460, 413, 1004, 718, 766, 438, 430, 403, 772;
    792, 442, 44, 769, 31, 173, 592, 918, 268, 31, 323, 887, 242, 90, 716, 198, 357, 253, 195, 752, 817, 584, 492, 96, 273, 881;
    937, 131, 298, 83, 32, 416, 430, 759, 446, 337, 964, 750, 824, 768, 122, 42, 354, 826, 362, 724, 697, 1001, 702, 540, 81, 202;
    96, 610, 782, 191, 472, 442, 65, 987, 129, 240, 953, 597, 1003, 339, 483, 637, 401, 603, 268, 211, 899, 613, 443, 496, 478, 918;
    853, 823, 631, 558, 840, 24, 511, 411, 138, 723, 467, 724, 989, 278, 227, 155, 158, 248, 387, 534, 195, 987, 942, 424, 599, 697;
    257, 572, 670, 678, 47, 115, 77, 63, 239, 967, 626, 318, 872, 631, 784, 667, 53, 118, 70, 812, 310, 929, 215, 808, 894, 700;
    961, 219, 247, 29, 208, 512, 784, 549, 112, 171, 521, 718, 170, 21, 704, 550, 392, 184, 268, 702, 65, 155, 904, 962, 462, 219;
    917, 486, 671, 880, 151, 272, 891, 205, 969, 11, 895, 176, 660, 762, 613, 763, 975, 307, 374, 772, 565, 105, 352, 196, 671, 246;
    841, 760, 555, 160, 35, 457, 421, 653, 618, 787, 531, 73, 407, 885, 433, 268, 746, 641, 100, 697, 1002, 143, 720, 217, 712, 915;
    248, 175, 889, 420, 771, 9, 847, 316, 500, 800, 459, 46, 215, 221, 89, 495, 442, 934, 620, 345, 168, 520, 325, 147, 938, 392;
    602, 433, 701, 677, 351, 804, 59, 936, 242, 401, 895, 609, 324, 421, 482, 735, 549, 700, 865, 805, 119, 797, 18, 717, 604, 883;
    394, 996, 837, 50, 159, 519, 57, 147, 346, 73, 329, 287, 605, 543, 851, 88, 604, 95, 434, 166, 257, 605, 891, 681, 637, 826;
    527, 986, 987, 864, 229, 444, 392, 531, 468, 463, 287, 886, 705, 752, 751, 117, 260, 400, 540, 624, 507, 305, 171, 784, 673, 277;
    603, 767, 694, 727, 730, 392, 478, 591, 986, 195, 402, 116, 541, 14, 192, 407, 617, 407, 486, 902, 1008, 467, 897, 466, 521, 90;
    649, 25, 564, 407, 454, 225, 458, 684, 626, 939, 868, 996, 506, 329, 954, 14, 718, 888, 199, 92, 684, 659, 103, 304, 944, 512;
    184, 746, 204, 375, 318, 376, 558, 90, 353, 25, 699, 365, 540, 890, 392, 599, 540, 457, 295, 83, 789, 837, 558, 922, 314, 119;
    0, 450, 856, 882, 690, 240, 397, 454, 756, 154, 636, 664, 486, 990, 18, 377, 606, 718, 19, 792, 188, 538, 990, 977, 341, 204;
    409, 802, 79, 211, 663, 50, 870, 983, 739, 954, 926, 916, 403, 911, 485, 282, 197, 986, 285, 736, 110, 397, 573, 434, 231, 8;
    882, 737, 588, 535, 658, 452, 407, 645, 840, 312, 65, 12, 77, 377, 730, 362, 838, 764, 947, 86, 956, 813, 947, 800, 691, 482;
    379, 522, 418, 276, 349, 377, 166, 640, 709, 321, 193, 284, 477, 648, 786, 518, 889, 10, 906, 830, 952, 388, 967, 249, 403, 652]

/-- A left inverse. All 676 entries of its product with the evaluation matrix
are verified by reduction in the Lean kernel below. -/
def pairEvaluationInverse : Matrix (Fin 26) (Fin 26) (ZMod 1009) :=
  !![333, 103, 728, 39, 867, 735, 992, 590, 727, 638, 383, 774, 100, 910, 423, 388, 398, 939, 119, 724, 417, 410, 637, 212, 648, 984;
    468, 197, 396, 354, 587, 229, 613, 858, 524, 624, 969, 969, 785, 926, 471, 209, 145, 513, 978, 1000, 990, 625, 605, 53, 297, 636;
    339, 468, 921, 810, 745, 913, 575, 322, 141, 48, 438, 311, 61, 789, 510, 726, 459, 43, 485, 597, 203, 9, 156, 330, 783, 895;
    743, 897, 449, 335, 235, 832, 88, 943, 714, 528, 700, 566, 492, 149, 177, 284, 273, 572, 801, 813, 251, 644, 151, 389, 338, 493;
    629, 472, 457, 356, 568, 538, 661, 752, 58, 629, 595, 400, 116, 821, 69, 830, 814, 573, 94, 938, 561, 184, 221, 480, 564, 701;
    418, 738, 968, 348, 462, 119, 579, 938, 72, 268, 665, 690, 803, 104, 585, 378, 868, 674, 846, 355, 299, 507, 287, 177, 927, 755;
    34, 981, 18, 928, 377, 690, 396, 567, 41, 514, 240, 591, 463, 181, 796, 250, 11, 762, 382, 550, 148, 806, 257, 340, 235, 449;
    627, 83, 690, 991, 661, 914, 722, 130, 656, 141, 706, 313, 455, 872, 195, 333, 576, 351, 618, 987, 610, 144, 674, 958, 697, 714;
    183, 121, 990, 572, 570, 777, 167, 823, 355, 263, 223, 656, 691, 763, 797, 739, 151, 975, 380, 462, 19, 959, 407, 938, 331, 352;
    769, 427, 448, 900, 185, 179, 703, 362, 57, 279, 22, 874, 27, 543, 653, 141, 120, 876, 167, 843, 955, 50, 417, 111, 705, 318;
    469, 261, 84, 94, 846, 768, 875, 231, 834, 634, 317, 601, 146, 552, 949, 115, 344, 470, 248, 912, 59, 491, 138, 479, 412, 397;
    764, 955, 948, 173, 778, 236, 717, 109, 591, 643, 231, 911, 96, 924, 887, 33, 607, 806, 791, 711, 162, 500, 649, 993, 418, 382;
    561, 316, 704, 913, 678, 742, 748, 441, 814, 766, 963, 507, 831, 893, 224, 599, 901, 537, 554, 702, 21, 644, 30, 251, 541, 515;
    375, 970, 836, 187, 566, 115, 195, 506, 517, 473, 796, 588, 351, 480, 421, 633, 557, 799, 371, 1000, 369, 282, 928, 413, 46, 121;
    541, 241, 927, 779, 571, 276, 486, 169, 833, 667, 780, 463, 325, 733, 56, 787, 482, 62, 588, 279, 203, 325, 448, 243, 654, 60;
    62, 896, 339, 375, 536, 217, 925, 827, 157, 602, 105, 761, 369, 826, 865, 273, 775, 309, 328, 339, 36, 222, 934, 249, 996, 398;
    865, 123, 77, 640, 224, 844, 218, 152, 530, 35, 897, 741, 479, 655, 693, 274, 41, 500, 505, 151, 809, 596, 459, 494, 804, 356;
    131, 286, 38, 721, 73, 969, 30, 129, 916, 287, 123, 213, 42, 4, 198, 0, 354, 633, 164, 163, 765, 665, 921, 228, 255, 623;
    452, 520, 538, 1001, 442, 876, 874, 131, 166, 781, 775, 785, 285, 546, 859, 126, 463, 17, 174, 36, 983, 162, 524, 195, 616, 743;
    369, 72, 338, 985, 213, 562, 877, 986, 180, 707, 545, 63, 776, 532, 669, 391, 801, 16, 202, 670, 642, 916, 707, 286, 678, 333;
    826, 408, 408, 636, 828, 54, 624, 267, 71, 621, 905, 331, 293, 885, 18, 864, 733, 227, 786, 95, 697, 864, 652, 960, 297, 335;
    596, 658, 478, 324, 664, 182, 466, 792, 208, 874, 909, 510, 52, 811, 631, 179, 14, 664, 293, 687, 468, 343, 433, 978, 875, 492;
    875, 533, 881, 275, 471, 858, 259, 811, 973, 624, 444, 209, 298, 145, 299, 77, 294, 654, 256, 479, 235, 56, 488, 299, 307, 408;
    811, 571, 158, 424, 448, 0, 803, 917, 355, 663, 644, 369, 380, 612, 545, 345, 359, 957, 90, 386, 678, 292, 239, 152, 823, 631;
    727, 425, 368, 327, 880, 943, 224, 547, 233, 678, 627, 968, 883, 144, 618, 164, 799, 602, 449, 196, 909, 620, 820, 329, 174, 419;
    926, 131, 719, 79, 975, 21, 616, 889, 299, 918, 766, 313, 892, 991, 209, 161, 164, 99, 899, 879, 544, 691, 578, 81, 330, 735]


private theorem pairEvaluation_inverse_row_0 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 0 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 0 j := by decide +kernel

private theorem pairEvaluation_inverse_row_1 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 1 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 1 j := by decide +kernel

private theorem pairEvaluation_inverse_row_2 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 2 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 2 j := by decide +kernel

private theorem pairEvaluation_inverse_row_3 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 3 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 3 j := by decide +kernel

private theorem pairEvaluation_inverse_row_4 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 4 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 4 j := by decide +kernel

private theorem pairEvaluation_inverse_row_5 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 5 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 5 j := by decide +kernel

private theorem pairEvaluation_inverse_row_6 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 6 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 6 j := by decide +kernel

private theorem pairEvaluation_inverse_row_7 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 7 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 7 j := by decide +kernel

private theorem pairEvaluation_inverse_row_8 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 8 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 8 j := by decide +kernel

private theorem pairEvaluation_inverse_row_9 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 9 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 9 j := by decide +kernel

private theorem pairEvaluation_inverse_row_10 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 10 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 10 j := by decide +kernel

private theorem pairEvaluation_inverse_row_11 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 11 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 11 j := by decide +kernel

private theorem pairEvaluation_inverse_row_12 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 12 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 12 j := by decide +kernel

private theorem pairEvaluation_inverse_row_13 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 13 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 13 j := by decide +kernel

private theorem pairEvaluation_inverse_row_14 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 14 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 14 j := by decide +kernel

private theorem pairEvaluation_inverse_row_15 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 15 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 15 j := by decide +kernel

private theorem pairEvaluation_inverse_row_16 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 16 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 16 j := by decide +kernel

private theorem pairEvaluation_inverse_row_17 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 17 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 17 j := by decide +kernel

private theorem pairEvaluation_inverse_row_18 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 18 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 18 j := by decide +kernel

private theorem pairEvaluation_inverse_row_19 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 19 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 19 j := by decide +kernel

private theorem pairEvaluation_inverse_row_20 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 20 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 20 j := by decide +kernel

private theorem pairEvaluation_inverse_row_21 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 21 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 21 j := by decide +kernel

private theorem pairEvaluation_inverse_row_22 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 22 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 22 j := by decide +kernel

private theorem pairEvaluation_inverse_row_23 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 23 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 23 j := by decide +kernel

private theorem pairEvaluation_inverse_row_24 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 24 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 24 j := by decide +kernel

private theorem pairEvaluation_inverse_row_25 :
    ∀ j, (pairEvaluationInverse * pairEvaluationMatrix) 25 j =
      (1 : Matrix (Fin 26) (Fin 26) (ZMod 1009)) 25 j := by decide +kernel

/-- The explicit inverse certificate, verified entirely by Lean's kernel. -/
theorem pairEvaluation_inverse_mul :
    pairEvaluationInverse * pairEvaluationMatrix = 1 := by
  ext i j
  fin_cases i
  · exact pairEvaluation_inverse_row_0 j
  · exact pairEvaluation_inverse_row_1 j
  · exact pairEvaluation_inverse_row_2 j
  · exact pairEvaluation_inverse_row_3 j
  · exact pairEvaluation_inverse_row_4 j
  · exact pairEvaluation_inverse_row_5 j
  · exact pairEvaluation_inverse_row_6 j
  · exact pairEvaluation_inverse_row_7 j
  · exact pairEvaluation_inverse_row_8 j
  · exact pairEvaluation_inverse_row_9 j
  · exact pairEvaluation_inverse_row_10 j
  · exact pairEvaluation_inverse_row_11 j
  · exact pairEvaluation_inverse_row_12 j
  · exact pairEvaluation_inverse_row_13 j
  · exact pairEvaluation_inverse_row_14 j
  · exact pairEvaluation_inverse_row_15 j
  · exact pairEvaluation_inverse_row_16 j
  · exact pairEvaluation_inverse_row_17 j
  · exact pairEvaluation_inverse_row_18 j
  · exact pairEvaluation_inverse_row_19 j
  · exact pairEvaluation_inverse_row_20 j
  · exact pairEvaluation_inverse_row_21 j
  · exact pairEvaluation_inverse_row_22 j
  · exact pairEvaluation_inverse_row_23 j
  · exact pairEvaluation_inverse_row_24 j
  · exact pairEvaluation_inverse_row_25 j

/-- A left matrix inverse makes the corresponding evaluation map injective. -/
theorem mulVec_injective_of_leftInverse
    {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n R} {B : Matrix n m R} (h : B * A = 1) :
    Function.Injective A.mulVec := by
  intro x y hxy
  have he := congrArg B.mulVec hxy
  simpa only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] using he

/-- The displayed C.3 matrix has independent columns over the chosen finite field. -/
theorem pairEvaluation_mulVec_injective :
    Function.Injective pairEvaluationMatrix.mulVec :=
  mulVec_injective_of_leftInverse pairEvaluation_inverse_mul

/-- Nonsingularity of the listed C.3 matrix. -/
theorem pairEvaluation_det_ne_zero : pairEvaluationMatrix.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det pairEvaluation_inverse_mul
  rw [Matrix.det_mul, Matrix.det_one, hzero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- The rank of the listed C.3 matrix is 26. -/
theorem pairEvaluation_rank : pairEvaluationMatrix.rank = 26 := by
  apply le_antisymm pairEvaluationMatrix.rank_le_width
  have h := Matrix.rank_mul_le_right pairEvaluationInverse pairEvaluationMatrix
  rw [pairEvaluation_inverse_mul, Matrix.rank_one, Fintype.card_fin] at h
  exact h

end IdealGeneration
