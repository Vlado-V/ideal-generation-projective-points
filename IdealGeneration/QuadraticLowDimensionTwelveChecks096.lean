module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 96–191 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_96 :
    twelvePackedRows 96 = packedMinorResidueRow twelveMinor 2 1024 96 := by rfl

theorem twelve_packed_product_96 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 96) twelvePackedRows =
      1024 ^ (96 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 96) := by rfl

theorem twelve_packed_row_97 :
    twelvePackedRows 97 = packedMinorResidueRow twelveMinor 2 1024 97 := by rfl

theorem twelve_packed_product_97 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 97) twelvePackedRows =
      1024 ^ (97 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 97) := by rfl

theorem twelve_packed_row_98 :
    twelvePackedRows 98 = packedMinorResidueRow twelveMinor 2 1024 98 := by rfl

theorem twelve_packed_product_98 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 98) twelvePackedRows =
      1024 ^ (98 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 98) := by rfl

theorem twelve_packed_row_99 :
    twelvePackedRows 99 = packedMinorResidueRow twelveMinor 2 1024 99 := by rfl

theorem twelve_packed_product_99 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 99) twelvePackedRows =
      1024 ^ (99 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 99) := by rfl

theorem twelve_packed_row_100 :
    twelvePackedRows 100 = packedMinorResidueRow twelveMinor 2 1024 100 := by rfl

theorem twelve_packed_product_100 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 100) twelvePackedRows =
      1024 ^ (100 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 100) := by rfl

theorem twelve_packed_row_101 :
    twelvePackedRows 101 = packedMinorResidueRow twelveMinor 2 1024 101 := by rfl

theorem twelve_packed_product_101 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 101) twelvePackedRows =
      1024 ^ (101 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 101) := by rfl

theorem twelve_packed_row_102 :
    twelvePackedRows 102 = packedMinorResidueRow twelveMinor 2 1024 102 := by rfl

theorem twelve_packed_product_102 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 102) twelvePackedRows =
      1024 ^ (102 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 102) := by rfl

theorem twelve_packed_row_103 :
    twelvePackedRows 103 = packedMinorResidueRow twelveMinor 2 1024 103 := by rfl

theorem twelve_packed_product_103 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 103) twelvePackedRows =
      1024 ^ (103 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 103) := by rfl

theorem twelve_packed_row_104 :
    twelvePackedRows 104 = packedMinorResidueRow twelveMinor 2 1024 104 := by rfl

theorem twelve_packed_product_104 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 104) twelvePackedRows =
      1024 ^ (104 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 104) := by rfl

theorem twelve_packed_row_105 :
    twelvePackedRows 105 = packedMinorResidueRow twelveMinor 2 1024 105 := by rfl

theorem twelve_packed_product_105 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 105) twelvePackedRows =
      1024 ^ (105 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 105) := by rfl

theorem twelve_packed_row_106 :
    twelvePackedRows 106 = packedMinorResidueRow twelveMinor 2 1024 106 := by rfl

theorem twelve_packed_product_106 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 106) twelvePackedRows =
      1024 ^ (106 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 106) := by rfl

theorem twelve_packed_row_107 :
    twelvePackedRows 107 = packedMinorResidueRow twelveMinor 2 1024 107 := by rfl

theorem twelve_packed_product_107 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 107) twelvePackedRows =
      1024 ^ (107 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 107) := by rfl

theorem twelve_packed_row_108 :
    twelvePackedRows 108 = packedMinorResidueRow twelveMinor 2 1024 108 := by rfl

theorem twelve_packed_product_108 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 108) twelvePackedRows =
      1024 ^ (108 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 108) := by rfl

theorem twelve_packed_row_109 :
    twelvePackedRows 109 = packedMinorResidueRow twelveMinor 2 1024 109 := by rfl

theorem twelve_packed_product_109 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 109) twelvePackedRows =
      1024 ^ (109 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 109) := by rfl

theorem twelve_packed_row_110 :
    twelvePackedRows 110 = packedMinorResidueRow twelveMinor 2 1024 110 := by rfl

theorem twelve_packed_product_110 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 110) twelvePackedRows =
      1024 ^ (110 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 110) := by rfl

theorem twelve_packed_row_111 :
    twelvePackedRows 111 = packedMinorResidueRow twelveMinor 2 1024 111 := by rfl

theorem twelve_packed_product_111 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 111) twelvePackedRows =
      1024 ^ (111 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 111) := by rfl

theorem twelve_packed_row_112 :
    twelvePackedRows 112 = packedMinorResidueRow twelveMinor 2 1024 112 := by rfl

theorem twelve_packed_product_112 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 112) twelvePackedRows =
      1024 ^ (112 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 112) := by rfl

theorem twelve_packed_row_113 :
    twelvePackedRows 113 = packedMinorResidueRow twelveMinor 2 1024 113 := by rfl

theorem twelve_packed_product_113 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 113) twelvePackedRows =
      1024 ^ (113 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 113) := by rfl

theorem twelve_packed_row_114 :
    twelvePackedRows 114 = packedMinorResidueRow twelveMinor 2 1024 114 := by rfl

theorem twelve_packed_product_114 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 114) twelvePackedRows =
      1024 ^ (114 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 114) := by rfl

theorem twelve_packed_row_115 :
    twelvePackedRows 115 = packedMinorResidueRow twelveMinor 2 1024 115 := by rfl

theorem twelve_packed_product_115 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 115) twelvePackedRows =
      1024 ^ (115 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 115) := by rfl

theorem twelve_packed_row_116 :
    twelvePackedRows 116 = packedMinorResidueRow twelveMinor 2 1024 116 := by rfl

theorem twelve_packed_product_116 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 116) twelvePackedRows =
      1024 ^ (116 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 116) := by rfl

theorem twelve_packed_row_117 :
    twelvePackedRows 117 = packedMinorResidueRow twelveMinor 2 1024 117 := by rfl

theorem twelve_packed_product_117 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 117) twelvePackedRows =
      1024 ^ (117 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 117) := by rfl

theorem twelve_packed_row_118 :
    twelvePackedRows 118 = packedMinorResidueRow twelveMinor 2 1024 118 := by rfl

theorem twelve_packed_product_118 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 118) twelvePackedRows =
      1024 ^ (118 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 118) := by rfl

theorem twelve_packed_row_119 :
    twelvePackedRows 119 = packedMinorResidueRow twelveMinor 2 1024 119 := by rfl

theorem twelve_packed_product_119 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 119) twelvePackedRows =
      1024 ^ (119 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 119) := by rfl

theorem twelve_packed_row_120 :
    twelvePackedRows 120 = packedMinorResidueRow twelveMinor 2 1024 120 := by rfl

theorem twelve_packed_product_120 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 120) twelvePackedRows =
      1024 ^ (120 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 120) := by rfl

theorem twelve_packed_row_121 :
    twelvePackedRows 121 = packedMinorResidueRow twelveMinor 2 1024 121 := by rfl

theorem twelve_packed_product_121 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 121) twelvePackedRows =
      1024 ^ (121 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 121) := by rfl

theorem twelve_packed_row_122 :
    twelvePackedRows 122 = packedMinorResidueRow twelveMinor 2 1024 122 := by rfl

theorem twelve_packed_product_122 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 122) twelvePackedRows =
      1024 ^ (122 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 122) := by rfl

theorem twelve_packed_row_123 :
    twelvePackedRows 123 = packedMinorResidueRow twelveMinor 2 1024 123 := by rfl

theorem twelve_packed_product_123 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 123) twelvePackedRows =
      1024 ^ (123 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 123) := by rfl

theorem twelve_packed_row_124 :
    twelvePackedRows 124 = packedMinorResidueRow twelveMinor 2 1024 124 := by rfl

theorem twelve_packed_product_124 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 124) twelvePackedRows =
      1024 ^ (124 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 124) := by rfl

theorem twelve_packed_row_125 :
    twelvePackedRows 125 = packedMinorResidueRow twelveMinor 2 1024 125 := by rfl

theorem twelve_packed_product_125 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 125) twelvePackedRows =
      1024 ^ (125 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 125) := by rfl

theorem twelve_packed_row_126 :
    twelvePackedRows 126 = packedMinorResidueRow twelveMinor 2 1024 126 := by rfl

theorem twelve_packed_product_126 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 126) twelvePackedRows =
      1024 ^ (126 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 126) := by rfl

theorem twelve_packed_row_127 :
    twelvePackedRows 127 = packedMinorResidueRow twelveMinor 2 1024 127 := by rfl

theorem twelve_packed_product_127 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 127) twelvePackedRows =
      1024 ^ (127 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 127) := by rfl

theorem twelve_packed_row_128 :
    twelvePackedRows 128 = packedMinorResidueRow twelveMinor 2 1024 128 := by rfl

theorem twelve_packed_product_128 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 128) twelvePackedRows =
      1024 ^ (128 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 128) := by rfl

theorem twelve_packed_row_129 :
    twelvePackedRows 129 = packedMinorResidueRow twelveMinor 2 1024 129 := by rfl

theorem twelve_packed_product_129 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 129) twelvePackedRows =
      1024 ^ (129 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 129) := by rfl

theorem twelve_packed_row_130 :
    twelvePackedRows 130 = packedMinorResidueRow twelveMinor 2 1024 130 := by rfl

theorem twelve_packed_product_130 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 130) twelvePackedRows =
      1024 ^ (130 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 130) := by rfl

theorem twelve_packed_row_131 :
    twelvePackedRows 131 = packedMinorResidueRow twelveMinor 2 1024 131 := by rfl

theorem twelve_packed_product_131 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 131) twelvePackedRows =
      1024 ^ (131 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 131) := by rfl

theorem twelve_packed_row_132 :
    twelvePackedRows 132 = packedMinorResidueRow twelveMinor 2 1024 132 := by rfl

theorem twelve_packed_product_132 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 132) twelvePackedRows =
      1024 ^ (132 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 132) := by rfl

theorem twelve_packed_row_133 :
    twelvePackedRows 133 = packedMinorResidueRow twelveMinor 2 1024 133 := by rfl

theorem twelve_packed_product_133 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 133) twelvePackedRows =
      1024 ^ (133 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 133) := by rfl

theorem twelve_packed_row_134 :
    twelvePackedRows 134 = packedMinorResidueRow twelveMinor 2 1024 134 := by rfl

theorem twelve_packed_product_134 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 134) twelvePackedRows =
      1024 ^ (134 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 134) := by rfl

theorem twelve_packed_row_135 :
    twelvePackedRows 135 = packedMinorResidueRow twelveMinor 2 1024 135 := by rfl

theorem twelve_packed_product_135 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 135) twelvePackedRows =
      1024 ^ (135 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 135) := by rfl

theorem twelve_packed_row_136 :
    twelvePackedRows 136 = packedMinorResidueRow twelveMinor 2 1024 136 := by rfl

theorem twelve_packed_product_136 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 136) twelvePackedRows =
      1024 ^ (136 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 136) := by rfl

theorem twelve_packed_row_137 :
    twelvePackedRows 137 = packedMinorResidueRow twelveMinor 2 1024 137 := by rfl

theorem twelve_packed_product_137 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 137) twelvePackedRows =
      1024 ^ (137 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 137) := by rfl

theorem twelve_packed_row_138 :
    twelvePackedRows 138 = packedMinorResidueRow twelveMinor 2 1024 138 := by rfl

theorem twelve_packed_product_138 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 138) twelvePackedRows =
      1024 ^ (138 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 138) := by rfl

theorem twelve_packed_row_139 :
    twelvePackedRows 139 = packedMinorResidueRow twelveMinor 2 1024 139 := by rfl

theorem twelve_packed_product_139 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 139) twelvePackedRows =
      1024 ^ (139 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 139) := by rfl

theorem twelve_packed_row_140 :
    twelvePackedRows 140 = packedMinorResidueRow twelveMinor 2 1024 140 := by rfl

theorem twelve_packed_product_140 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 140) twelvePackedRows =
      1024 ^ (140 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 140) := by rfl

theorem twelve_packed_row_141 :
    twelvePackedRows 141 = packedMinorResidueRow twelveMinor 2 1024 141 := by rfl

theorem twelve_packed_product_141 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 141) twelvePackedRows =
      1024 ^ (141 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 141) := by rfl

theorem twelve_packed_row_142 :
    twelvePackedRows 142 = packedMinorResidueRow twelveMinor 2 1024 142 := by rfl

theorem twelve_packed_product_142 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 142) twelvePackedRows =
      1024 ^ (142 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 142) := by rfl

theorem twelve_packed_row_143 :
    twelvePackedRows 143 = packedMinorResidueRow twelveMinor 2 1024 143 := by rfl

theorem twelve_packed_product_143 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 143) twelvePackedRows =
      1024 ^ (143 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 143) := by rfl

theorem twelve_packed_row_144 :
    twelvePackedRows 144 = packedMinorResidueRow twelveMinor 2 1024 144 := by rfl

theorem twelve_packed_product_144 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 144) twelvePackedRows =
      1024 ^ (144 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 144) := by rfl

theorem twelve_packed_row_145 :
    twelvePackedRows 145 = packedMinorResidueRow twelveMinor 2 1024 145 := by rfl

theorem twelve_packed_product_145 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 145) twelvePackedRows =
      1024 ^ (145 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 145) := by rfl

theorem twelve_packed_row_146 :
    twelvePackedRows 146 = packedMinorResidueRow twelveMinor 2 1024 146 := by rfl

theorem twelve_packed_product_146 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 146) twelvePackedRows =
      1024 ^ (146 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 146) := by rfl

theorem twelve_packed_row_147 :
    twelvePackedRows 147 = packedMinorResidueRow twelveMinor 2 1024 147 := by rfl

theorem twelve_packed_product_147 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 147) twelvePackedRows =
      1024 ^ (147 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 147) := by rfl

theorem twelve_packed_row_148 :
    twelvePackedRows 148 = packedMinorResidueRow twelveMinor 2 1024 148 := by rfl

theorem twelve_packed_product_148 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 148) twelvePackedRows =
      1024 ^ (148 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 148) := by rfl

theorem twelve_packed_row_149 :
    twelvePackedRows 149 = packedMinorResidueRow twelveMinor 2 1024 149 := by rfl

theorem twelve_packed_product_149 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 149) twelvePackedRows =
      1024 ^ (149 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 149) := by rfl

theorem twelve_packed_row_150 :
    twelvePackedRows 150 = packedMinorResidueRow twelveMinor 2 1024 150 := by rfl

theorem twelve_packed_product_150 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 150) twelvePackedRows =
      1024 ^ (150 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 150) := by rfl

theorem twelve_packed_row_151 :
    twelvePackedRows 151 = packedMinorResidueRow twelveMinor 2 1024 151 := by rfl

theorem twelve_packed_product_151 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 151) twelvePackedRows =
      1024 ^ (151 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 151) := by rfl

theorem twelve_packed_row_152 :
    twelvePackedRows 152 = packedMinorResidueRow twelveMinor 2 1024 152 := by rfl

theorem twelve_packed_product_152 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 152) twelvePackedRows =
      1024 ^ (152 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 152) := by rfl

theorem twelve_packed_row_153 :
    twelvePackedRows 153 = packedMinorResidueRow twelveMinor 2 1024 153 := by rfl

theorem twelve_packed_product_153 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 153) twelvePackedRows =
      1024 ^ (153 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 153) := by rfl

theorem twelve_packed_row_154 :
    twelvePackedRows 154 = packedMinorResidueRow twelveMinor 2 1024 154 := by rfl

theorem twelve_packed_product_154 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 154) twelvePackedRows =
      1024 ^ (154 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 154) := by rfl

theorem twelve_packed_row_155 :
    twelvePackedRows 155 = packedMinorResidueRow twelveMinor 2 1024 155 := by rfl

theorem twelve_packed_product_155 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 155) twelvePackedRows =
      1024 ^ (155 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 155) := by rfl

theorem twelve_packed_row_156 :
    twelvePackedRows 156 = packedMinorResidueRow twelveMinor 2 1024 156 := by rfl

theorem twelve_packed_product_156 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 156) twelvePackedRows =
      1024 ^ (156 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 156) := by rfl

theorem twelve_packed_row_157 :
    twelvePackedRows 157 = packedMinorResidueRow twelveMinor 2 1024 157 := by rfl

theorem twelve_packed_product_157 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 157) twelvePackedRows =
      1024 ^ (157 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 157) := by rfl

theorem twelve_packed_row_158 :
    twelvePackedRows 158 = packedMinorResidueRow twelveMinor 2 1024 158 := by rfl

theorem twelve_packed_product_158 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 158) twelvePackedRows =
      1024 ^ (158 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 158) := by rfl

theorem twelve_packed_row_159 :
    twelvePackedRows 159 = packedMinorResidueRow twelveMinor 2 1024 159 := by rfl

theorem twelve_packed_product_159 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 159) twelvePackedRows =
      1024 ^ (159 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 159) := by rfl

theorem twelve_packed_row_160 :
    twelvePackedRows 160 = packedMinorResidueRow twelveMinor 2 1024 160 := by rfl

theorem twelve_packed_product_160 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 160) twelvePackedRows =
      1024 ^ (160 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 160) := by rfl

theorem twelve_packed_row_161 :
    twelvePackedRows 161 = packedMinorResidueRow twelveMinor 2 1024 161 := by rfl

theorem twelve_packed_product_161 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 161) twelvePackedRows =
      1024 ^ (161 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 161) := by rfl

theorem twelve_packed_row_162 :
    twelvePackedRows 162 = packedMinorResidueRow twelveMinor 2 1024 162 := by rfl

theorem twelve_packed_product_162 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 162) twelvePackedRows =
      1024 ^ (162 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 162) := by rfl

theorem twelve_packed_row_163 :
    twelvePackedRows 163 = packedMinorResidueRow twelveMinor 2 1024 163 := by rfl

theorem twelve_packed_product_163 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 163) twelvePackedRows =
      1024 ^ (163 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 163) := by rfl

theorem twelve_packed_row_164 :
    twelvePackedRows 164 = packedMinorResidueRow twelveMinor 2 1024 164 := by rfl

theorem twelve_packed_product_164 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 164) twelvePackedRows =
      1024 ^ (164 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 164) := by rfl

theorem twelve_packed_row_165 :
    twelvePackedRows 165 = packedMinorResidueRow twelveMinor 2 1024 165 := by rfl

theorem twelve_packed_product_165 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 165) twelvePackedRows =
      1024 ^ (165 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 165) := by rfl

theorem twelve_packed_row_166 :
    twelvePackedRows 166 = packedMinorResidueRow twelveMinor 2 1024 166 := by rfl

theorem twelve_packed_product_166 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 166) twelvePackedRows =
      1024 ^ (166 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 166) := by rfl

theorem twelve_packed_row_167 :
    twelvePackedRows 167 = packedMinorResidueRow twelveMinor 2 1024 167 := by rfl

theorem twelve_packed_product_167 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 167) twelvePackedRows =
      1024 ^ (167 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 167) := by rfl

theorem twelve_packed_row_168 :
    twelvePackedRows 168 = packedMinorResidueRow twelveMinor 2 1024 168 := by rfl

theorem twelve_packed_product_168 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 168) twelvePackedRows =
      1024 ^ (168 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 168) := by rfl

theorem twelve_packed_row_169 :
    twelvePackedRows 169 = packedMinorResidueRow twelveMinor 2 1024 169 := by rfl

theorem twelve_packed_product_169 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 169) twelvePackedRows =
      1024 ^ (169 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 169) := by rfl

theorem twelve_packed_row_170 :
    twelvePackedRows 170 = packedMinorResidueRow twelveMinor 2 1024 170 := by rfl

theorem twelve_packed_product_170 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 170) twelvePackedRows =
      1024 ^ (170 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 170) := by rfl

theorem twelve_packed_row_171 :
    twelvePackedRows 171 = packedMinorResidueRow twelveMinor 2 1024 171 := by rfl

theorem twelve_packed_product_171 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 171) twelvePackedRows =
      1024 ^ (171 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 171) := by rfl

theorem twelve_packed_row_172 :
    twelvePackedRows 172 = packedMinorResidueRow twelveMinor 2 1024 172 := by rfl

theorem twelve_packed_product_172 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 172) twelvePackedRows =
      1024 ^ (172 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 172) := by rfl

theorem twelve_packed_row_173 :
    twelvePackedRows 173 = packedMinorResidueRow twelveMinor 2 1024 173 := by rfl

theorem twelve_packed_product_173 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 173) twelvePackedRows =
      1024 ^ (173 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 173) := by rfl

theorem twelve_packed_row_174 :
    twelvePackedRows 174 = packedMinorResidueRow twelveMinor 2 1024 174 := by rfl

theorem twelve_packed_product_174 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 174) twelvePackedRows =
      1024 ^ (174 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 174) := by rfl

theorem twelve_packed_row_175 :
    twelvePackedRows 175 = packedMinorResidueRow twelveMinor 2 1024 175 := by rfl

theorem twelve_packed_product_175 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 175) twelvePackedRows =
      1024 ^ (175 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 175) := by rfl

theorem twelve_packed_row_176 :
    twelvePackedRows 176 = packedMinorResidueRow twelveMinor 2 1024 176 := by rfl

theorem twelve_packed_product_176 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 176) twelvePackedRows =
      1024 ^ (176 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 176) := by rfl

theorem twelve_packed_row_177 :
    twelvePackedRows 177 = packedMinorResidueRow twelveMinor 2 1024 177 := by rfl

theorem twelve_packed_product_177 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 177) twelvePackedRows =
      1024 ^ (177 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 177) := by rfl

theorem twelve_packed_row_178 :
    twelvePackedRows 178 = packedMinorResidueRow twelveMinor 2 1024 178 := by rfl

theorem twelve_packed_product_178 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 178) twelvePackedRows =
      1024 ^ (178 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 178) := by rfl

theorem twelve_packed_row_179 :
    twelvePackedRows 179 = packedMinorResidueRow twelveMinor 2 1024 179 := by rfl

theorem twelve_packed_product_179 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 179) twelvePackedRows =
      1024 ^ (179 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 179) := by rfl

theorem twelve_packed_row_180 :
    twelvePackedRows 180 = packedMinorResidueRow twelveMinor 2 1024 180 := by rfl

theorem twelve_packed_product_180 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 180) twelvePackedRows =
      1024 ^ (180 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 180) := by rfl

theorem twelve_packed_row_181 :
    twelvePackedRows 181 = packedMinorResidueRow twelveMinor 2 1024 181 := by rfl

theorem twelve_packed_product_181 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 181) twelvePackedRows =
      1024 ^ (181 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 181) := by rfl

theorem twelve_packed_row_182 :
    twelvePackedRows 182 = packedMinorResidueRow twelveMinor 2 1024 182 := by rfl

theorem twelve_packed_product_182 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 182) twelvePackedRows =
      1024 ^ (182 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 182) := by rfl

theorem twelve_packed_row_183 :
    twelvePackedRows 183 = packedMinorResidueRow twelveMinor 2 1024 183 := by rfl

theorem twelve_packed_product_183 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 183) twelvePackedRows =
      1024 ^ (183 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 183) := by rfl

theorem twelve_packed_row_184 :
    twelvePackedRows 184 = packedMinorResidueRow twelveMinor 2 1024 184 := by rfl

theorem twelve_packed_product_184 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 184) twelvePackedRows =
      1024 ^ (184 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 184) := by rfl

theorem twelve_packed_row_185 :
    twelvePackedRows 185 = packedMinorResidueRow twelveMinor 2 1024 185 := by rfl

theorem twelve_packed_product_185 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 185) twelvePackedRows =
      1024 ^ (185 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 185) := by rfl

theorem twelve_packed_row_186 :
    twelvePackedRows 186 = packedMinorResidueRow twelveMinor 2 1024 186 := by rfl

theorem twelve_packed_product_186 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 186) twelvePackedRows =
      1024 ^ (186 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 186) := by rfl

theorem twelve_packed_row_187 :
    twelvePackedRows 187 = packedMinorResidueRow twelveMinor 2 1024 187 := by rfl

theorem twelve_packed_product_187 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 187) twelvePackedRows =
      1024 ^ (187 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 187) := by rfl

theorem twelve_packed_row_188 :
    twelvePackedRows 188 = packedMinorResidueRow twelveMinor 2 1024 188 := by rfl

theorem twelve_packed_product_188 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 188) twelvePackedRows =
      1024 ^ (188 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 188) := by rfl

theorem twelve_packed_row_189 :
    twelvePackedRows 189 = packedMinorResidueRow twelveMinor 2 1024 189 := by rfl

theorem twelve_packed_product_189 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 189) twelvePackedRows =
      1024 ^ (189 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 189) := by rfl

theorem twelve_packed_row_190 :
    twelvePackedRows 190 = packedMinorResidueRow twelveMinor 2 1024 190 := by rfl

theorem twelve_packed_product_190 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 190) twelvePackedRows =
      1024 ^ (190 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 190) := by rfl

theorem twelve_packed_row_191 :
    twelvePackedRows 191 = packedMinorResidueRow twelveMinor 2 1024 191 := by rfl

theorem twelve_packed_product_191 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 191) twelvePackedRows =
      1024 ^ (191 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 191) := by rfl

end IdealGeneration.QuadraticLowDimension
