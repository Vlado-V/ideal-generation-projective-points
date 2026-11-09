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

theorem upper000 : packedUpper 0 =
    packSparse (2 ^ 40) (upperRows 0) := by decide +kernel

theorem packed000 : packedProduct (lowerRows 0) packedUpper =
    packSparse (2 ^ 40) (targetRows 0) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 0) := by decide +kernel

theorem rowFacts000 : PackedRowFacts 0 := by
  constructor <;> decide +kernel

theorem upper001 : packedUpper 1 =
    packSparse (2 ^ 40) (upperRows 1) := by decide +kernel

theorem packed001 : packedProduct (lowerRows 1) packedUpper =
    packSparse (2 ^ 40) (targetRows 1) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 1) := by decide +kernel

theorem rowFacts001 : PackedRowFacts 1 := by
  constructor <;> decide +kernel

theorem upper002 : packedUpper 2 =
    packSparse (2 ^ 40) (upperRows 2) := by decide +kernel

theorem packed002 : packedProduct (lowerRows 2) packedUpper =
    packSparse (2 ^ 40) (targetRows 2) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 2) := by decide +kernel

theorem rowFacts002 : PackedRowFacts 2 := by
  constructor <;> decide +kernel

theorem upper003 : packedUpper 3 =
    packSparse (2 ^ 40) (upperRows 3) := by decide +kernel

theorem packed003 : packedProduct (lowerRows 3) packedUpper =
    packSparse (2 ^ 40) (targetRows 3) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 3) := by decide +kernel

theorem rowFacts003 : PackedRowFacts 3 := by
  constructor <;> decide +kernel

theorem upper004 : packedUpper 4 =
    packSparse (2 ^ 40) (upperRows 4) := by decide +kernel

theorem packed004 : packedProduct (lowerRows 4) packedUpper =
    packSparse (2 ^ 40) (targetRows 4) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 4) := by decide +kernel

theorem rowFacts004 : PackedRowFacts 4 := by
  constructor <;> decide +kernel

theorem upper005 : packedUpper 5 =
    packSparse (2 ^ 40) (upperRows 5) := by decide +kernel

theorem packed005 : packedProduct (lowerRows 5) packedUpper =
    packSparse (2 ^ 40) (targetRows 5) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 5) := by decide +kernel

theorem rowFacts005 : PackedRowFacts 5 := by
  constructor <;> decide +kernel

theorem upper006 : packedUpper 6 =
    packSparse (2 ^ 40) (upperRows 6) := by decide +kernel

theorem packed006 : packedProduct (lowerRows 6) packedUpper =
    packSparse (2 ^ 40) (targetRows 6) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 6) := by decide +kernel

theorem rowFacts006 : PackedRowFacts 6 := by
  constructor <;> decide +kernel

theorem upper007 : packedUpper 7 =
    packSparse (2 ^ 40) (upperRows 7) := by decide +kernel

theorem packed007 : packedProduct (lowerRows 7) packedUpper =
    packSparse (2 ^ 40) (targetRows 7) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 7) := by decide +kernel

theorem rowFacts007 : PackedRowFacts 7 := by
  constructor <;> decide +kernel

theorem upper008 : packedUpper 8 =
    packSparse (2 ^ 40) (upperRows 8) := by decide +kernel

theorem packed008 : packedProduct (lowerRows 8) packedUpper =
    packSparse (2 ^ 40) (targetRows 8) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 8) := by decide +kernel

theorem rowFacts008 : PackedRowFacts 8 := by
  constructor <;> decide +kernel

theorem upper009 : packedUpper 9 =
    packSparse (2 ^ 40) (upperRows 9) := by decide +kernel

theorem packed009 : packedProduct (lowerRows 9) packedUpper =
    packSparse (2 ^ 40) (targetRows 9) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 9) := by decide +kernel

theorem rowFacts009 : PackedRowFacts 9 := by
  constructor <;> decide +kernel

theorem upper010 : packedUpper 10 =
    packSparse (2 ^ 40) (upperRows 10) := by decide +kernel

theorem packed010 : packedProduct (lowerRows 10) packedUpper =
    packSparse (2 ^ 40) (targetRows 10) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 10) := by decide +kernel

theorem rowFacts010 : PackedRowFacts 10 := by
  constructor <;> decide +kernel

theorem upper011 : packedUpper 11 =
    packSparse (2 ^ 40) (upperRows 11) := by decide +kernel

theorem packed011 : packedProduct (lowerRows 11) packedUpper =
    packSparse (2 ^ 40) (targetRows 11) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 11) := by decide +kernel

theorem rowFacts011 : PackedRowFacts 11 := by
  constructor <;> decide +kernel

theorem upper012 : packedUpper 12 =
    packSparse (2 ^ 40) (upperRows 12) := by decide +kernel

theorem packed012 : packedProduct (lowerRows 12) packedUpper =
    packSparse (2 ^ 40) (targetRows 12) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 12) := by decide +kernel

theorem rowFacts012 : PackedRowFacts 12 := by
  constructor <;> decide +kernel

theorem upper013 : packedUpper 13 =
    packSparse (2 ^ 40) (upperRows 13) := by decide +kernel

theorem packed013 : packedProduct (lowerRows 13) packedUpper =
    packSparse (2 ^ 40) (targetRows 13) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 13) := by decide +kernel

theorem rowFacts013 : PackedRowFacts 13 := by
  constructor <;> decide +kernel

theorem upper014 : packedUpper 14 =
    packSparse (2 ^ 40) (upperRows 14) := by decide +kernel

theorem packed014 : packedProduct (lowerRows 14) packedUpper =
    packSparse (2 ^ 40) (targetRows 14) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 14) := by decide +kernel

theorem rowFacts014 : PackedRowFacts 14 := by
  constructor <;> decide +kernel

theorem upper015 : packedUpper 15 =
    packSparse (2 ^ 40) (upperRows 15) := by decide +kernel

theorem packed015 : packedProduct (lowerRows 15) packedUpper =
    packSparse (2 ^ 40) (targetRows 15) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 15) := by decide +kernel

theorem rowFacts015 : PackedRowFacts 15 := by
  constructor <;> decide +kernel

theorem upper016 : packedUpper 16 =
    packSparse (2 ^ 40) (upperRows 16) := by decide +kernel

theorem packed016 : packedProduct (lowerRows 16) packedUpper =
    packSparse (2 ^ 40) (targetRows 16) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 16) := by decide +kernel

theorem rowFacts016 : PackedRowFacts 16 := by
  constructor <;> decide +kernel

theorem upper017 : packedUpper 17 =
    packSparse (2 ^ 40) (upperRows 17) := by decide +kernel

theorem packed017 : packedProduct (lowerRows 17) packedUpper =
    packSparse (2 ^ 40) (targetRows 17) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 17) := by decide +kernel

theorem rowFacts017 : PackedRowFacts 17 := by
  constructor <;> decide +kernel

theorem upper018 : packedUpper 18 =
    packSparse (2 ^ 40) (upperRows 18) := by decide +kernel

theorem packed018 : packedProduct (lowerRows 18) packedUpper =
    packSparse (2 ^ 40) (targetRows 18) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 18) := by decide +kernel

theorem rowFacts018 : PackedRowFacts 18 := by
  constructor <;> decide +kernel

theorem upper019 : packedUpper 19 =
    packSparse (2 ^ 40) (upperRows 19) := by decide +kernel

theorem packed019 : packedProduct (lowerRows 19) packedUpper =
    packSparse (2 ^ 40) (targetRows 19) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 19) := by decide +kernel

theorem rowFacts019 : PackedRowFacts 19 := by
  constructor <;> decide +kernel

theorem upper020 : packedUpper 20 =
    packSparse (2 ^ 40) (upperRows 20) := by decide +kernel

theorem packed020 : packedProduct (lowerRows 20) packedUpper =
    packSparse (2 ^ 40) (targetRows 20) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 20) := by decide +kernel

theorem rowFacts020 : PackedRowFacts 20 := by
  constructor <;> decide +kernel

theorem upper021 : packedUpper 21 =
    packSparse (2 ^ 40) (upperRows 21) := by decide +kernel

theorem packed021 : packedProduct (lowerRows 21) packedUpper =
    packSparse (2 ^ 40) (targetRows 21) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 21) := by decide +kernel

theorem rowFacts021 : PackedRowFacts 21 := by
  constructor <;> decide +kernel

theorem upper022 : packedUpper 22 =
    packSparse (2 ^ 40) (upperRows 22) := by decide +kernel

theorem packed022 : packedProduct (lowerRows 22) packedUpper =
    packSparse (2 ^ 40) (targetRows 22) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 22) := by decide +kernel

theorem rowFacts022 : PackedRowFacts 22 := by
  constructor <;> decide +kernel

theorem upper023 : packedUpper 23 =
    packSparse (2 ^ 40) (upperRows 23) := by decide +kernel

theorem packed023 : packedProduct (lowerRows 23) packedUpper =
    packSparse (2 ^ 40) (targetRows 23) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 23) := by decide +kernel

theorem rowFacts023 : PackedRowFacts 23 := by
  constructor <;> decide +kernel

theorem upper024 : packedUpper 24 =
    packSparse (2 ^ 40) (upperRows 24) := by decide +kernel

theorem packed024 : packedProduct (lowerRows 24) packedUpper =
    packSparse (2 ^ 40) (targetRows 24) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 24) := by decide +kernel

theorem rowFacts024 : PackedRowFacts 24 := by
  constructor <;> decide +kernel

theorem upper025 : packedUpper 25 =
    packSparse (2 ^ 40) (upperRows 25) := by decide +kernel

theorem packed025 : packedProduct (lowerRows 25) packedUpper =
    packSparse (2 ^ 40) (targetRows 25) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 25) := by decide +kernel

theorem rowFacts025 : PackedRowFacts 25 := by
  constructor <;> decide +kernel

theorem upper026 : packedUpper 26 =
    packSparse (2 ^ 40) (upperRows 26) := by decide +kernel

theorem packed026 : packedProduct (lowerRows 26) packedUpper =
    packSparse (2 ^ 40) (targetRows 26) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 26) := by decide +kernel

theorem rowFacts026 : PackedRowFacts 26 := by
  constructor <;> decide +kernel

theorem upper027 : packedUpper 27 =
    packSparse (2 ^ 40) (upperRows 27) := by decide +kernel

theorem packed027 : packedProduct (lowerRows 27) packedUpper =
    packSparse (2 ^ 40) (targetRows 27) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 27) := by decide +kernel

theorem rowFacts027 : PackedRowFacts 27 := by
  constructor <;> decide +kernel

theorem upper028 : packedUpper 28 =
    packSparse (2 ^ 40) (upperRows 28) := by decide +kernel

theorem packed028 : packedProduct (lowerRows 28) packedUpper =
    packSparse (2 ^ 40) (targetRows 28) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 28) := by decide +kernel

theorem rowFacts028 : PackedRowFacts 28 := by
  constructor <;> decide +kernel

theorem upper029 : packedUpper 29 =
    packSparse (2 ^ 40) (upperRows 29) := by decide +kernel

theorem packed029 : packedProduct (lowerRows 29) packedUpper =
    packSparse (2 ^ 40) (targetRows 29) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 29) := by decide +kernel

theorem rowFacts029 : PackedRowFacts 29 := by
  constructor <;> decide +kernel

theorem upper030 : packedUpper 30 =
    packSparse (2 ^ 40) (upperRows 30) := by decide +kernel

theorem packed030 : packedProduct (lowerRows 30) packedUpper =
    packSparse (2 ^ 40) (targetRows 30) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 30) := by decide +kernel

theorem rowFacts030 : PackedRowFacts 30 := by
  constructor <;> decide +kernel

theorem upper031 : packedUpper 31 =
    packSparse (2 ^ 40) (upperRows 31) := by decide +kernel

theorem packed031 : packedProduct (lowerRows 31) packedUpper =
    packSparse (2 ^ 40) (targetRows 31) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 31) := by decide +kernel

theorem rowFacts031 : PackedRowFacts 31 := by
  constructor <;> decide +kernel

#print axioms packed031

end CertifiedRank.C2.PackedCertificate
