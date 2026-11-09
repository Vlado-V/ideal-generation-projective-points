module

public import IdealGeneration.CubicInitialCert.CheckDefinitions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedRank.C2.PackedCertificate

theorem upper064 : packedUpper 64 =
    packSparse (2 ^ 40) (upperRows 64) := by decide +kernel

theorem packed064 : packedProduct (lowerRows 64) packedUpper =
    packSparse (2 ^ 40) (targetRows 64) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 64) := by decide +kernel

theorem rowFacts064 : PackedRowFacts 64 := by
  constructor <;> decide +kernel

theorem upper065 : packedUpper 65 =
    packSparse (2 ^ 40) (upperRows 65) := by decide +kernel

theorem packed065 : packedProduct (lowerRows 65) packedUpper =
    packSparse (2 ^ 40) (targetRows 65) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 65) := by decide +kernel

theorem rowFacts065 : PackedRowFacts 65 := by
  constructor <;> decide +kernel

theorem upper066 : packedUpper 66 =
    packSparse (2 ^ 40) (upperRows 66) := by decide +kernel

theorem packed066 : packedProduct (lowerRows 66) packedUpper =
    packSparse (2 ^ 40) (targetRows 66) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 66) := by decide +kernel

theorem rowFacts066 : PackedRowFacts 66 := by
  constructor <;> decide +kernel

theorem upper067 : packedUpper 67 =
    packSparse (2 ^ 40) (upperRows 67) := by decide +kernel

theorem packed067 : packedProduct (lowerRows 67) packedUpper =
    packSparse (2 ^ 40) (targetRows 67) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 67) := by decide +kernel

theorem rowFacts067 : PackedRowFacts 67 := by
  constructor <;> decide +kernel

theorem upper068 : packedUpper 68 =
    packSparse (2 ^ 40) (upperRows 68) := by decide +kernel

theorem packed068 : packedProduct (lowerRows 68) packedUpper =
    packSparse (2 ^ 40) (targetRows 68) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 68) := by decide +kernel

theorem rowFacts068 : PackedRowFacts 68 := by
  constructor <;> decide +kernel

theorem upper069 : packedUpper 69 =
    packSparse (2 ^ 40) (upperRows 69) := by decide +kernel

theorem packed069 : packedProduct (lowerRows 69) packedUpper =
    packSparse (2 ^ 40) (targetRows 69) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 69) := by decide +kernel

theorem rowFacts069 : PackedRowFacts 69 := by
  constructor <;> decide +kernel

theorem upper070 : packedUpper 70 =
    packSparse (2 ^ 40) (upperRows 70) := by decide +kernel

theorem packed070 : packedProduct (lowerRows 70) packedUpper =
    packSparse (2 ^ 40) (targetRows 70) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 70) := by decide +kernel

theorem rowFacts070 : PackedRowFacts 70 := by
  constructor <;> decide +kernel

theorem upper071 : packedUpper 71 =
    packSparse (2 ^ 40) (upperRows 71) := by decide +kernel

theorem packed071 : packedProduct (lowerRows 71) packedUpper =
    packSparse (2 ^ 40) (targetRows 71) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 71) := by decide +kernel

theorem rowFacts071 : PackedRowFacts 71 := by
  constructor <;> decide +kernel

theorem upper072 : packedUpper 72 =
    packSparse (2 ^ 40) (upperRows 72) := by decide +kernel

theorem packed072 : packedProduct (lowerRows 72) packedUpper =
    packSparse (2 ^ 40) (targetRows 72) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 72) := by decide +kernel

theorem rowFacts072 : PackedRowFacts 72 := by
  constructor <;> decide +kernel

theorem upper073 : packedUpper 73 =
    packSparse (2 ^ 40) (upperRows 73) := by decide +kernel

theorem packed073 : packedProduct (lowerRows 73) packedUpper =
    packSparse (2 ^ 40) (targetRows 73) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 73) := by decide +kernel

theorem rowFacts073 : PackedRowFacts 73 := by
  constructor <;> decide +kernel

theorem upper074 : packedUpper 74 =
    packSparse (2 ^ 40) (upperRows 74) := by decide +kernel

theorem packed074 : packedProduct (lowerRows 74) packedUpper =
    packSparse (2 ^ 40) (targetRows 74) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 74) := by decide +kernel

theorem rowFacts074 : PackedRowFacts 74 := by
  constructor <;> decide +kernel

theorem upper075 : packedUpper 75 =
    packSparse (2 ^ 40) (upperRows 75) := by decide +kernel

theorem packed075 : packedProduct (lowerRows 75) packedUpper =
    packSparse (2 ^ 40) (targetRows 75) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 75) := by decide +kernel

theorem rowFacts075 : PackedRowFacts 75 := by
  constructor <;> decide +kernel

theorem upper076 : packedUpper 76 =
    packSparse (2 ^ 40) (upperRows 76) := by decide +kernel

theorem packed076 : packedProduct (lowerRows 76) packedUpper =
    packSparse (2 ^ 40) (targetRows 76) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 76) := by decide +kernel

theorem rowFacts076 : PackedRowFacts 76 := by
  constructor <;> decide +kernel

theorem upper077 : packedUpper 77 =
    packSparse (2 ^ 40) (upperRows 77) := by decide +kernel

theorem packed077 : packedProduct (lowerRows 77) packedUpper =
    packSparse (2 ^ 40) (targetRows 77) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 77) := by decide +kernel

theorem rowFacts077 : PackedRowFacts 77 := by
  constructor <;> decide +kernel

theorem upper078 : packedUpper 78 =
    packSparse (2 ^ 40) (upperRows 78) := by decide +kernel

theorem packed078 : packedProduct (lowerRows 78) packedUpper =
    packSparse (2 ^ 40) (targetRows 78) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 78) := by decide +kernel

theorem rowFacts078 : PackedRowFacts 78 := by
  constructor <;> decide +kernel

theorem upper079 : packedUpper 79 =
    packSparse (2 ^ 40) (upperRows 79) := by decide +kernel

theorem packed079 : packedProduct (lowerRows 79) packedUpper =
    packSparse (2 ^ 40) (targetRows 79) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 79) := by decide +kernel

theorem rowFacts079 : PackedRowFacts 79 := by
  constructor <;> decide +kernel

theorem upper080 : packedUpper 80 =
    packSparse (2 ^ 40) (upperRows 80) := by decide +kernel

theorem packed080 : packedProduct (lowerRows 80) packedUpper =
    packSparse (2 ^ 40) (targetRows 80) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 80) := by decide +kernel

theorem rowFacts080 : PackedRowFacts 80 := by
  constructor <;> decide +kernel

theorem upper081 : packedUpper 81 =
    packSparse (2 ^ 40) (upperRows 81) := by decide +kernel

theorem packed081 : packedProduct (lowerRows 81) packedUpper =
    packSparse (2 ^ 40) (targetRows 81) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 81) := by decide +kernel

theorem rowFacts081 : PackedRowFacts 81 := by
  constructor <;> decide +kernel

theorem upper082 : packedUpper 82 =
    packSparse (2 ^ 40) (upperRows 82) := by decide +kernel

theorem packed082 : packedProduct (lowerRows 82) packedUpper =
    packSparse (2 ^ 40) (targetRows 82) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 82) := by decide +kernel

theorem rowFacts082 : PackedRowFacts 82 := by
  constructor <;> decide +kernel

theorem upper083 : packedUpper 83 =
    packSparse (2 ^ 40) (upperRows 83) := by decide +kernel

theorem packed083 : packedProduct (lowerRows 83) packedUpper =
    packSparse (2 ^ 40) (targetRows 83) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 83) := by decide +kernel

theorem rowFacts083 : PackedRowFacts 83 := by
  constructor <;> decide +kernel

theorem upper084 : packedUpper 84 =
    packSparse (2 ^ 40) (upperRows 84) := by decide +kernel

theorem packed084 : packedProduct (lowerRows 84) packedUpper =
    packSparse (2 ^ 40) (targetRows 84) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 84) := by decide +kernel

theorem rowFacts084 : PackedRowFacts 84 := by
  constructor <;> decide +kernel

theorem upper085 : packedUpper 85 =
    packSparse (2 ^ 40) (upperRows 85) := by decide +kernel

theorem packed085 : packedProduct (lowerRows 85) packedUpper =
    packSparse (2 ^ 40) (targetRows 85) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 85) := by decide +kernel

theorem rowFacts085 : PackedRowFacts 85 := by
  constructor <;> decide +kernel

theorem upper086 : packedUpper 86 =
    packSparse (2 ^ 40) (upperRows 86) := by decide +kernel

theorem packed086 : packedProduct (lowerRows 86) packedUpper =
    packSparse (2 ^ 40) (targetRows 86) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 86) := by decide +kernel

theorem rowFacts086 : PackedRowFacts 86 := by
  constructor <;> decide +kernel

theorem upper087 : packedUpper 87 =
    packSparse (2 ^ 40) (upperRows 87) := by decide +kernel

theorem packed087 : packedProduct (lowerRows 87) packedUpper =
    packSparse (2 ^ 40) (targetRows 87) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 87) := by decide +kernel

theorem rowFacts087 : PackedRowFacts 87 := by
  constructor <;> decide +kernel

theorem upper088 : packedUpper 88 =
    packSparse (2 ^ 40) (upperRows 88) := by decide +kernel

theorem packed088 : packedProduct (lowerRows 88) packedUpper =
    packSparse (2 ^ 40) (targetRows 88) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 88) := by decide +kernel

theorem rowFacts088 : PackedRowFacts 88 := by
  constructor <;> decide +kernel

theorem upper089 : packedUpper 89 =
    packSparse (2 ^ 40) (upperRows 89) := by decide +kernel

theorem packed089 : packedProduct (lowerRows 89) packedUpper =
    packSparse (2 ^ 40) (targetRows 89) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 89) := by decide +kernel

theorem rowFacts089 : PackedRowFacts 89 := by
  constructor <;> decide +kernel

theorem upper090 : packedUpper 90 =
    packSparse (2 ^ 40) (upperRows 90) := by decide +kernel

theorem packed090 : packedProduct (lowerRows 90) packedUpper =
    packSparse (2 ^ 40) (targetRows 90) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 90) := by decide +kernel

theorem rowFacts090 : PackedRowFacts 90 := by
  constructor <;> decide +kernel

theorem upper091 : packedUpper 91 =
    packSparse (2 ^ 40) (upperRows 91) := by decide +kernel

theorem packed091 : packedProduct (lowerRows 91) packedUpper =
    packSparse (2 ^ 40) (targetRows 91) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 91) := by decide +kernel

theorem rowFacts091 : PackedRowFacts 91 := by
  constructor <;> decide +kernel

theorem upper092 : packedUpper 92 =
    packSparse (2 ^ 40) (upperRows 92) := by decide +kernel

theorem packed092 : packedProduct (lowerRows 92) packedUpper =
    packSparse (2 ^ 40) (targetRows 92) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 92) := by decide +kernel

theorem rowFacts092 : PackedRowFacts 92 := by
  constructor <;> decide +kernel

theorem upper093 : packedUpper 93 =
    packSparse (2 ^ 40) (upperRows 93) := by decide +kernel

theorem packed093 : packedProduct (lowerRows 93) packedUpper =
    packSparse (2 ^ 40) (targetRows 93) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 93) := by decide +kernel

theorem rowFacts093 : PackedRowFacts 93 := by
  constructor <;> decide +kernel

theorem upper094 : packedUpper 94 =
    packSparse (2 ^ 40) (upperRows 94) := by decide +kernel

theorem packed094 : packedProduct (lowerRows 94) packedUpper =
    packSparse (2 ^ 40) (targetRows 94) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 94) := by decide +kernel

theorem rowFacts094 : PackedRowFacts 94 := by
  constructor <;> decide +kernel

theorem upper095 : packedUpper 95 =
    packSparse (2 ^ 40) (upperRows 95) := by decide +kernel

theorem packed095 : packedProduct (lowerRows 95) packedUpper =
    packSparse (2 ^ 40) (targetRows 95) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 95) := by decide +kernel

theorem rowFacts095 : PackedRowFacts 95 := by
  constructor <;> decide +kernel

#print axioms packed095

end CertifiedRank.C2.PackedCertificate
