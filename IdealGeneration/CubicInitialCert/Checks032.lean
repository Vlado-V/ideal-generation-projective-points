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

theorem upper032 : packedUpper 32 =
    packSparse (2 ^ 40) (upperRows 32) := by decide +kernel

theorem packed032 : packedProduct (lowerRows 32) packedUpper =
    packSparse (2 ^ 40) (targetRows 32) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 32) := by decide +kernel

theorem rowFacts032 : PackedRowFacts 32 := by
  constructor <;> decide +kernel

theorem upper033 : packedUpper 33 =
    packSparse (2 ^ 40) (upperRows 33) := by decide +kernel

theorem packed033 : packedProduct (lowerRows 33) packedUpper =
    packSparse (2 ^ 40) (targetRows 33) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 33) := by decide +kernel

theorem rowFacts033 : PackedRowFacts 33 := by
  constructor <;> decide +kernel

theorem upper034 : packedUpper 34 =
    packSparse (2 ^ 40) (upperRows 34) := by decide +kernel

theorem packed034 : packedProduct (lowerRows 34) packedUpper =
    packSparse (2 ^ 40) (targetRows 34) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 34) := by decide +kernel

theorem rowFacts034 : PackedRowFacts 34 := by
  constructor <;> decide +kernel

theorem upper035 : packedUpper 35 =
    packSparse (2 ^ 40) (upperRows 35) := by decide +kernel

theorem packed035 : packedProduct (lowerRows 35) packedUpper =
    packSparse (2 ^ 40) (targetRows 35) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 35) := by decide +kernel

theorem rowFacts035 : PackedRowFacts 35 := by
  constructor <;> decide +kernel

theorem upper036 : packedUpper 36 =
    packSparse (2 ^ 40) (upperRows 36) := by decide +kernel

theorem packed036 : packedProduct (lowerRows 36) packedUpper =
    packSparse (2 ^ 40) (targetRows 36) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 36) := by decide +kernel

theorem rowFacts036 : PackedRowFacts 36 := by
  constructor <;> decide +kernel

theorem upper037 : packedUpper 37 =
    packSparse (2 ^ 40) (upperRows 37) := by decide +kernel

theorem packed037 : packedProduct (lowerRows 37) packedUpper =
    packSparse (2 ^ 40) (targetRows 37) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 37) := by decide +kernel

theorem rowFacts037 : PackedRowFacts 37 := by
  constructor <;> decide +kernel

theorem upper038 : packedUpper 38 =
    packSparse (2 ^ 40) (upperRows 38) := by decide +kernel

theorem packed038 : packedProduct (lowerRows 38) packedUpper =
    packSparse (2 ^ 40) (targetRows 38) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 38) := by decide +kernel

theorem rowFacts038 : PackedRowFacts 38 := by
  constructor <;> decide +kernel

theorem upper039 : packedUpper 39 =
    packSparse (2 ^ 40) (upperRows 39) := by decide +kernel

theorem packed039 : packedProduct (lowerRows 39) packedUpper =
    packSparse (2 ^ 40) (targetRows 39) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 39) := by decide +kernel

theorem rowFacts039 : PackedRowFacts 39 := by
  constructor <;> decide +kernel

theorem upper040 : packedUpper 40 =
    packSparse (2 ^ 40) (upperRows 40) := by decide +kernel

theorem packed040 : packedProduct (lowerRows 40) packedUpper =
    packSparse (2 ^ 40) (targetRows 40) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 40) := by decide +kernel

theorem rowFacts040 : PackedRowFacts 40 := by
  constructor <;> decide +kernel

theorem upper041 : packedUpper 41 =
    packSparse (2 ^ 40) (upperRows 41) := by decide +kernel

theorem packed041 : packedProduct (lowerRows 41) packedUpper =
    packSparse (2 ^ 40) (targetRows 41) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 41) := by decide +kernel

theorem rowFacts041 : PackedRowFacts 41 := by
  constructor <;> decide +kernel

theorem upper042 : packedUpper 42 =
    packSparse (2 ^ 40) (upperRows 42) := by decide +kernel

theorem packed042 : packedProduct (lowerRows 42) packedUpper =
    packSparse (2 ^ 40) (targetRows 42) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 42) := by decide +kernel

theorem rowFacts042 : PackedRowFacts 42 := by
  constructor <;> decide +kernel

theorem upper043 : packedUpper 43 =
    packSparse (2 ^ 40) (upperRows 43) := by decide +kernel

theorem packed043 : packedProduct (lowerRows 43) packedUpper =
    packSparse (2 ^ 40) (targetRows 43) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 43) := by decide +kernel

theorem rowFacts043 : PackedRowFacts 43 := by
  constructor <;> decide +kernel

theorem upper044 : packedUpper 44 =
    packSparse (2 ^ 40) (upperRows 44) := by decide +kernel

theorem packed044 : packedProduct (lowerRows 44) packedUpper =
    packSparse (2 ^ 40) (targetRows 44) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 44) := by decide +kernel

theorem rowFacts044 : PackedRowFacts 44 := by
  constructor <;> decide +kernel

theorem upper045 : packedUpper 45 =
    packSparse (2 ^ 40) (upperRows 45) := by decide +kernel

theorem packed045 : packedProduct (lowerRows 45) packedUpper =
    packSparse (2 ^ 40) (targetRows 45) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 45) := by decide +kernel

theorem rowFacts045 : PackedRowFacts 45 := by
  constructor <;> decide +kernel

theorem upper046 : packedUpper 46 =
    packSparse (2 ^ 40) (upperRows 46) := by decide +kernel

theorem packed046 : packedProduct (lowerRows 46) packedUpper =
    packSparse (2 ^ 40) (targetRows 46) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 46) := by decide +kernel

theorem rowFacts046 : PackedRowFacts 46 := by
  constructor <;> decide +kernel

theorem upper047 : packedUpper 47 =
    packSparse (2 ^ 40) (upperRows 47) := by decide +kernel

theorem packed047 : packedProduct (lowerRows 47) packedUpper =
    packSparse (2 ^ 40) (targetRows 47) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 47) := by decide +kernel

theorem rowFacts047 : PackedRowFacts 47 := by
  constructor <;> decide +kernel

theorem upper048 : packedUpper 48 =
    packSparse (2 ^ 40) (upperRows 48) := by decide +kernel

theorem packed048 : packedProduct (lowerRows 48) packedUpper =
    packSparse (2 ^ 40) (targetRows 48) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 48) := by decide +kernel

theorem rowFacts048 : PackedRowFacts 48 := by
  constructor <;> decide +kernel

theorem upper049 : packedUpper 49 =
    packSparse (2 ^ 40) (upperRows 49) := by decide +kernel

theorem packed049 : packedProduct (lowerRows 49) packedUpper =
    packSparse (2 ^ 40) (targetRows 49) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 49) := by decide +kernel

theorem rowFacts049 : PackedRowFacts 49 := by
  constructor <;> decide +kernel

theorem upper050 : packedUpper 50 =
    packSparse (2 ^ 40) (upperRows 50) := by decide +kernel

theorem packed050 : packedProduct (lowerRows 50) packedUpper =
    packSparse (2 ^ 40) (targetRows 50) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 50) := by decide +kernel

theorem rowFacts050 : PackedRowFacts 50 := by
  constructor <;> decide +kernel

theorem upper051 : packedUpper 51 =
    packSparse (2 ^ 40) (upperRows 51) := by decide +kernel

theorem packed051 : packedProduct (lowerRows 51) packedUpper =
    packSparse (2 ^ 40) (targetRows 51) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 51) := by decide +kernel

theorem rowFacts051 : PackedRowFacts 51 := by
  constructor <;> decide +kernel

theorem upper052 : packedUpper 52 =
    packSparse (2 ^ 40) (upperRows 52) := by decide +kernel

theorem packed052 : packedProduct (lowerRows 52) packedUpper =
    packSparse (2 ^ 40) (targetRows 52) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 52) := by decide +kernel

theorem rowFacts052 : PackedRowFacts 52 := by
  constructor <;> decide +kernel

theorem upper053 : packedUpper 53 =
    packSparse (2 ^ 40) (upperRows 53) := by decide +kernel

theorem packed053 : packedProduct (lowerRows 53) packedUpper =
    packSparse (2 ^ 40) (targetRows 53) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 53) := by decide +kernel

theorem rowFacts053 : PackedRowFacts 53 := by
  constructor <;> decide +kernel

theorem upper054 : packedUpper 54 =
    packSparse (2 ^ 40) (upperRows 54) := by decide +kernel

theorem packed054 : packedProduct (lowerRows 54) packedUpper =
    packSparse (2 ^ 40) (targetRows 54) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 54) := by decide +kernel

theorem rowFacts054 : PackedRowFacts 54 := by
  constructor <;> decide +kernel

theorem upper055 : packedUpper 55 =
    packSparse (2 ^ 40) (upperRows 55) := by decide +kernel

theorem packed055 : packedProduct (lowerRows 55) packedUpper =
    packSparse (2 ^ 40) (targetRows 55) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 55) := by decide +kernel

theorem rowFacts055 : PackedRowFacts 55 := by
  constructor <;> decide +kernel

theorem upper056 : packedUpper 56 =
    packSparse (2 ^ 40) (upperRows 56) := by decide +kernel

theorem packed056 : packedProduct (lowerRows 56) packedUpper =
    packSparse (2 ^ 40) (targetRows 56) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 56) := by decide +kernel

theorem rowFacts056 : PackedRowFacts 56 := by
  constructor <;> decide +kernel

theorem upper057 : packedUpper 57 =
    packSparse (2 ^ 40) (upperRows 57) := by decide +kernel

theorem packed057 : packedProduct (lowerRows 57) packedUpper =
    packSparse (2 ^ 40) (targetRows 57) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 57) := by decide +kernel

theorem rowFacts057 : PackedRowFacts 57 := by
  constructor <;> decide +kernel

theorem upper058 : packedUpper 58 =
    packSparse (2 ^ 40) (upperRows 58) := by decide +kernel

theorem packed058 : packedProduct (lowerRows 58) packedUpper =
    packSparse (2 ^ 40) (targetRows 58) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 58) := by decide +kernel

theorem rowFacts058 : PackedRowFacts 58 := by
  constructor <;> decide +kernel

theorem upper059 : packedUpper 59 =
    packSparse (2 ^ 40) (upperRows 59) := by decide +kernel

theorem packed059 : packedProduct (lowerRows 59) packedUpper =
    packSparse (2 ^ 40) (targetRows 59) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 59) := by decide +kernel

theorem rowFacts059 : PackedRowFacts 59 := by
  constructor <;> decide +kernel

theorem upper060 : packedUpper 60 =
    packSparse (2 ^ 40) (upperRows 60) := by decide +kernel

theorem packed060 : packedProduct (lowerRows 60) packedUpper =
    packSparse (2 ^ 40) (targetRows 60) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 60) := by decide +kernel

theorem rowFacts060 : PackedRowFacts 60 := by
  constructor <;> decide +kernel

theorem upper061 : packedUpper 61 =
    packSparse (2 ^ 40) (upperRows 61) := by decide +kernel

theorem packed061 : packedProduct (lowerRows 61) packedUpper =
    packSparse (2 ^ 40) (targetRows 61) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 61) := by decide +kernel

theorem rowFacts061 : PackedRowFacts 61 := by
  constructor <;> decide +kernel

theorem upper062 : packedUpper 62 =
    packSparse (2 ^ 40) (upperRows 62) := by decide +kernel

theorem packed062 : packedProduct (lowerRows 62) packedUpper =
    packSparse (2 ^ 40) (targetRows 62) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 62) := by decide +kernel

theorem rowFacts062 : PackedRowFacts 62 := by
  constructor <;> decide +kernel

theorem upper063 : packedUpper 63 =
    packSparse (2 ^ 40) (upperRows 63) := by decide +kernel

theorem packed063 : packedProduct (lowerRows 63) packedUpper =
    packSparse (2 ^ 40) (targetRows 63) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 63) := by decide +kernel

theorem rowFacts063 : PackedRowFacts 63 := by
  constructor <;> decide +kernel

#print axioms packed063

end CertifiedRank.C2.PackedCertificate
