module

public import IdealGeneration.CubicRootCert.PackedData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.C2RootCertificate

open CertifiedRank

theorem upper096 : packedUpper 96 =
    packSparse (2 ^ 40) (upperRows 96) := by rfl

theorem packed096 : packedProduct (lowerRows 96) packedUpper =
    packSparse (2 ^ 40) (targetRows 96) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 96) := by rfl

theorem rowFacts096 : PackedRowFacts 96 := by
  constructor <;> decide +kernel

theorem upper097 : packedUpper 97 =
    packSparse (2 ^ 40) (upperRows 97) := by rfl

theorem packed097 : packedProduct (lowerRows 97) packedUpper =
    packSparse (2 ^ 40) (targetRows 97) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 97) := by rfl

theorem rowFacts097 : PackedRowFacts 97 := by
  constructor <;> decide +kernel

theorem upper098 : packedUpper 98 =
    packSparse (2 ^ 40) (upperRows 98) := by rfl

theorem packed098 : packedProduct (lowerRows 98) packedUpper =
    packSparse (2 ^ 40) (targetRows 98) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 98) := by rfl

theorem rowFacts098 : PackedRowFacts 98 := by
  constructor <;> decide +kernel

theorem upper099 : packedUpper 99 =
    packSparse (2 ^ 40) (upperRows 99) := by rfl

theorem packed099 : packedProduct (lowerRows 99) packedUpper =
    packSparse (2 ^ 40) (targetRows 99) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 99) := by rfl

theorem rowFacts099 : PackedRowFacts 99 := by
  constructor <;> decide +kernel

theorem upper100 : packedUpper 100 =
    packSparse (2 ^ 40) (upperRows 100) := by rfl

theorem packed100 : packedProduct (lowerRows 100) packedUpper =
    packSparse (2 ^ 40) (targetRows 100) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 100) := by rfl

theorem rowFacts100 : PackedRowFacts 100 := by
  constructor <;> decide +kernel

theorem upper101 : packedUpper 101 =
    packSparse (2 ^ 40) (upperRows 101) := by rfl

theorem packed101 : packedProduct (lowerRows 101) packedUpper =
    packSparse (2 ^ 40) (targetRows 101) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 101) := by rfl

theorem rowFacts101 : PackedRowFacts 101 := by
  constructor <;> decide +kernel

theorem upper102 : packedUpper 102 =
    packSparse (2 ^ 40) (upperRows 102) := by rfl

theorem packed102 : packedProduct (lowerRows 102) packedUpper =
    packSparse (2 ^ 40) (targetRows 102) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 102) := by rfl

theorem rowFacts102 : PackedRowFacts 102 := by
  constructor <;> decide +kernel

theorem upper103 : packedUpper 103 =
    packSparse (2 ^ 40) (upperRows 103) := by rfl

theorem packed103 : packedProduct (lowerRows 103) packedUpper =
    packSparse (2 ^ 40) (targetRows 103) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 103) := by rfl

theorem rowFacts103 : PackedRowFacts 103 := by
  constructor <;> decide +kernel

theorem upper104 : packedUpper 104 =
    packSparse (2 ^ 40) (upperRows 104) := by rfl

theorem packed104 : packedProduct (lowerRows 104) packedUpper =
    packSparse (2 ^ 40) (targetRows 104) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 104) := by rfl

theorem rowFacts104 : PackedRowFacts 104 := by
  constructor <;> decide +kernel

theorem upper105 : packedUpper 105 =
    packSparse (2 ^ 40) (upperRows 105) := by rfl

theorem packed105 : packedProduct (lowerRows 105) packedUpper =
    packSparse (2 ^ 40) (targetRows 105) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 105) := by rfl

theorem rowFacts105 : PackedRowFacts 105 := by
  constructor <;> decide +kernel

theorem upper106 : packedUpper 106 =
    packSparse (2 ^ 40) (upperRows 106) := by rfl

theorem packed106 : packedProduct (lowerRows 106) packedUpper =
    packSparse (2 ^ 40) (targetRows 106) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 106) := by rfl

theorem rowFacts106 : PackedRowFacts 106 := by
  constructor <;> decide +kernel

theorem upper107 : packedUpper 107 =
    packSparse (2 ^ 40) (upperRows 107) := by rfl

theorem packed107 : packedProduct (lowerRows 107) packedUpper =
    packSparse (2 ^ 40) (targetRows 107) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 107) := by rfl

theorem rowFacts107 : PackedRowFacts 107 := by
  constructor <;> decide +kernel

theorem upper108 : packedUpper 108 =
    packSparse (2 ^ 40) (upperRows 108) := by rfl

theorem packed108 : packedProduct (lowerRows 108) packedUpper =
    packSparse (2 ^ 40) (targetRows 108) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 108) := by rfl

theorem rowFacts108 : PackedRowFacts 108 := by
  constructor <;> decide +kernel

theorem upper109 : packedUpper 109 =
    packSparse (2 ^ 40) (upperRows 109) := by rfl

theorem packed109 : packedProduct (lowerRows 109) packedUpper =
    packSparse (2 ^ 40) (targetRows 109) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 109) := by rfl

theorem rowFacts109 : PackedRowFacts 109 := by
  constructor <;> decide +kernel

theorem upper110 : packedUpper 110 =
    packSparse (2 ^ 40) (upperRows 110) := by rfl

theorem packed110 : packedProduct (lowerRows 110) packedUpper =
    packSparse (2 ^ 40) (targetRows 110) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 110) := by rfl

theorem rowFacts110 : PackedRowFacts 110 := by
  constructor <;> decide +kernel

theorem upper111 : packedUpper 111 =
    packSparse (2 ^ 40) (upperRows 111) := by rfl

theorem packed111 : packedProduct (lowerRows 111) packedUpper =
    packSparse (2 ^ 40) (targetRows 111) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 111) := by rfl

theorem rowFacts111 : PackedRowFacts 111 := by
  constructor <;> decide +kernel

theorem upper112 : packedUpper 112 =
    packSparse (2 ^ 40) (upperRows 112) := by rfl

theorem packed112 : packedProduct (lowerRows 112) packedUpper =
    packSparse (2 ^ 40) (targetRows 112) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 112) := by rfl

theorem rowFacts112 : PackedRowFacts 112 := by
  constructor <;> decide +kernel

theorem upper113 : packedUpper 113 =
    packSparse (2 ^ 40) (upperRows 113) := by rfl

theorem packed113 : packedProduct (lowerRows 113) packedUpper =
    packSparse (2 ^ 40) (targetRows 113) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 113) := by rfl

theorem rowFacts113 : PackedRowFacts 113 := by
  constructor <;> decide +kernel

theorem upper114 : packedUpper 114 =
    packSparse (2 ^ 40) (upperRows 114) := by rfl

theorem packed114 : packedProduct (lowerRows 114) packedUpper =
    packSparse (2 ^ 40) (targetRows 114) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 114) := by rfl

theorem rowFacts114 : PackedRowFacts 114 := by
  constructor <;> decide +kernel

theorem upper115 : packedUpper 115 =
    packSparse (2 ^ 40) (upperRows 115) := by rfl

theorem packed115 : packedProduct (lowerRows 115) packedUpper =
    packSparse (2 ^ 40) (targetRows 115) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 115) := by rfl

theorem rowFacts115 : PackedRowFacts 115 := by
  constructor <;> decide +kernel

theorem upper116 : packedUpper 116 =
    packSparse (2 ^ 40) (upperRows 116) := by rfl

theorem packed116 : packedProduct (lowerRows 116) packedUpper =
    packSparse (2 ^ 40) (targetRows 116) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 116) := by rfl

theorem rowFacts116 : PackedRowFacts 116 := by
  constructor <;> decide +kernel

theorem upper117 : packedUpper 117 =
    packSparse (2 ^ 40) (upperRows 117) := by rfl

theorem packed117 : packedProduct (lowerRows 117) packedUpper =
    packSparse (2 ^ 40) (targetRows 117) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 117) := by rfl

theorem rowFacts117 : PackedRowFacts 117 := by
  constructor <;> decide +kernel

theorem upper118 : packedUpper 118 =
    packSparse (2 ^ 40) (upperRows 118) := by rfl

theorem packed118 : packedProduct (lowerRows 118) packedUpper =
    packSparse (2 ^ 40) (targetRows 118) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 118) := by rfl

theorem rowFacts118 : PackedRowFacts 118 := by
  constructor <;> decide +kernel

theorem upper119 : packedUpper 119 =
    packSparse (2 ^ 40) (upperRows 119) := by rfl

theorem packed119 : packedProduct (lowerRows 119) packedUpper =
    packSparse (2 ^ 40) (targetRows 119) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 119) := by rfl

theorem rowFacts119 : PackedRowFacts 119 := by
  constructor <;> decide +kernel

theorem upper120 : packedUpper 120 =
    packSparse (2 ^ 40) (upperRows 120) := by rfl

theorem packed120 : packedProduct (lowerRows 120) packedUpper =
    packSparse (2 ^ 40) (targetRows 120) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 120) := by rfl

theorem rowFacts120 : PackedRowFacts 120 := by
  constructor <;> decide +kernel

theorem upper121 : packedUpper 121 =
    packSparse (2 ^ 40) (upperRows 121) := by rfl

theorem packed121 : packedProduct (lowerRows 121) packedUpper =
    packSparse (2 ^ 40) (targetRows 121) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 121) := by rfl

theorem rowFacts121 : PackedRowFacts 121 := by
  constructor <;> decide +kernel

theorem upper122 : packedUpper 122 =
    packSparse (2 ^ 40) (upperRows 122) := by rfl

theorem packed122 : packedProduct (lowerRows 122) packedUpper =
    packSparse (2 ^ 40) (targetRows 122) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 122) := by rfl

theorem rowFacts122 : PackedRowFacts 122 := by
  constructor <;> decide +kernel

theorem upper123 : packedUpper 123 =
    packSparse (2 ^ 40) (upperRows 123) := by rfl

theorem packed123 : packedProduct (lowerRows 123) packedUpper =
    packSparse (2 ^ 40) (targetRows 123) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 123) := by rfl

theorem rowFacts123 : PackedRowFacts 123 := by
  constructor <;> decide +kernel

theorem upper124 : packedUpper 124 =
    packSparse (2 ^ 40) (upperRows 124) := by rfl

theorem packed124 : packedProduct (lowerRows 124) packedUpper =
    packSparse (2 ^ 40) (targetRows 124) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 124) := by rfl

theorem rowFacts124 : PackedRowFacts 124 := by
  constructor <;> decide +kernel

theorem upper125 : packedUpper 125 =
    packSparse (2 ^ 40) (upperRows 125) := by rfl

theorem packed125 : packedProduct (lowerRows 125) packedUpper =
    packSparse (2 ^ 40) (targetRows 125) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 125) := by rfl

theorem rowFacts125 : PackedRowFacts 125 := by
  constructor <;> decide +kernel

theorem upper126 : packedUpper 126 =
    packSparse (2 ^ 40) (upperRows 126) := by rfl

theorem packed126 : packedProduct (lowerRows 126) packedUpper =
    packSparse (2 ^ 40) (targetRows 126) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 126) := by rfl

theorem rowFacts126 : PackedRowFacts 126 := by
  constructor <;> decide +kernel

theorem upper127 : packedUpper 127 =
    packSparse (2 ^ 40) (upperRows 127) := by rfl

theorem packed127 : packedProduct (lowerRows 127) packedUpper =
    packSparse (2 ^ 40) (targetRows 127) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 127) := by rfl

theorem rowFacts127 : PackedRowFacts 127 := by
  constructor <;> decide +kernel


end IdealGeneration.CubicSupported.C2RootCertificate
