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

theorem upper192 : packedUpper 192 =
    packSparse (2 ^ 40) (upperRows 192) := by decide +kernel

theorem packed192 : packedProduct (lowerRows 192) packedUpper =
    packSparse (2 ^ 40) (targetRows 192) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 192) := by decide +kernel

theorem rowFacts192 : PackedRowFacts 192 := by
  constructor <;> decide +kernel

theorem upper193 : packedUpper 193 =
    packSparse (2 ^ 40) (upperRows 193) := by decide +kernel

theorem packed193 : packedProduct (lowerRows 193) packedUpper =
    packSparse (2 ^ 40) (targetRows 193) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 193) := by decide +kernel

theorem rowFacts193 : PackedRowFacts 193 := by
  constructor <;> decide +kernel

theorem upper194 : packedUpper 194 =
    packSparse (2 ^ 40) (upperRows 194) := by decide +kernel

theorem packed194 : packedProduct (lowerRows 194) packedUpper =
    packSparse (2 ^ 40) (targetRows 194) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 194) := by decide +kernel

theorem rowFacts194 : PackedRowFacts 194 := by
  constructor <;> decide +kernel

theorem upper195 : packedUpper 195 =
    packSparse (2 ^ 40) (upperRows 195) := by decide +kernel

theorem packed195 : packedProduct (lowerRows 195) packedUpper =
    packSparse (2 ^ 40) (targetRows 195) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 195) := by decide +kernel

theorem rowFacts195 : PackedRowFacts 195 := by
  constructor <;> decide +kernel

theorem upper196 : packedUpper 196 =
    packSparse (2 ^ 40) (upperRows 196) := by decide +kernel

theorem packed196 : packedProduct (lowerRows 196) packedUpper =
    packSparse (2 ^ 40) (targetRows 196) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 196) := by decide +kernel

theorem rowFacts196 : PackedRowFacts 196 := by
  constructor <;> decide +kernel

theorem upper197 : packedUpper 197 =
    packSparse (2 ^ 40) (upperRows 197) := by decide +kernel

theorem packed197 : packedProduct (lowerRows 197) packedUpper =
    packSparse (2 ^ 40) (targetRows 197) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 197) := by decide +kernel

theorem rowFacts197 : PackedRowFacts 197 := by
  constructor <;> decide +kernel

theorem upper198 : packedUpper 198 =
    packSparse (2 ^ 40) (upperRows 198) := by decide +kernel

theorem packed198 : packedProduct (lowerRows 198) packedUpper =
    packSparse (2 ^ 40) (targetRows 198) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 198) := by decide +kernel

theorem rowFacts198 : PackedRowFacts 198 := by
  constructor <;> decide +kernel

theorem upper199 : packedUpper 199 =
    packSparse (2 ^ 40) (upperRows 199) := by decide +kernel

theorem packed199 : packedProduct (lowerRows 199) packedUpper =
    packSparse (2 ^ 40) (targetRows 199) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 199) := by decide +kernel

theorem rowFacts199 : PackedRowFacts 199 := by
  constructor <;> decide +kernel

theorem upper200 : packedUpper 200 =
    packSparse (2 ^ 40) (upperRows 200) := by decide +kernel

theorem packed200 : packedProduct (lowerRows 200) packedUpper =
    packSparse (2 ^ 40) (targetRows 200) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 200) := by decide +kernel

theorem rowFacts200 : PackedRowFacts 200 := by
  constructor <;> decide +kernel

theorem upper201 : packedUpper 201 =
    packSparse (2 ^ 40) (upperRows 201) := by decide +kernel

theorem packed201 : packedProduct (lowerRows 201) packedUpper =
    packSparse (2 ^ 40) (targetRows 201) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 201) := by decide +kernel

theorem rowFacts201 : PackedRowFacts 201 := by
  constructor <;> decide +kernel

theorem upper202 : packedUpper 202 =
    packSparse (2 ^ 40) (upperRows 202) := by decide +kernel

theorem packed202 : packedProduct (lowerRows 202) packedUpper =
    packSparse (2 ^ 40) (targetRows 202) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 202) := by decide +kernel

theorem rowFacts202 : PackedRowFacts 202 := by
  constructor <;> decide +kernel

theorem upper203 : packedUpper 203 =
    packSparse (2 ^ 40) (upperRows 203) := by decide +kernel

theorem packed203 : packedProduct (lowerRows 203) packedUpper =
    packSparse (2 ^ 40) (targetRows 203) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 203) := by decide +kernel

theorem rowFacts203 : PackedRowFacts 203 := by
  constructor <;> decide +kernel

theorem upper204 : packedUpper 204 =
    packSparse (2 ^ 40) (upperRows 204) := by decide +kernel

theorem packed204 : packedProduct (lowerRows 204) packedUpper =
    packSparse (2 ^ 40) (targetRows 204) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 204) := by decide +kernel

theorem rowFacts204 : PackedRowFacts 204 := by
  constructor <;> decide +kernel

theorem upper205 : packedUpper 205 =
    packSparse (2 ^ 40) (upperRows 205) := by decide +kernel

theorem packed205 : packedProduct (lowerRows 205) packedUpper =
    packSparse (2 ^ 40) (targetRows 205) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 205) := by decide +kernel

theorem rowFacts205 : PackedRowFacts 205 := by
  constructor <;> decide +kernel

theorem upper206 : packedUpper 206 =
    packSparse (2 ^ 40) (upperRows 206) := by decide +kernel

theorem packed206 : packedProduct (lowerRows 206) packedUpper =
    packSparse (2 ^ 40) (targetRows 206) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 206) := by decide +kernel

theorem rowFacts206 : PackedRowFacts 206 := by
  constructor <;> decide +kernel

theorem upper207 : packedUpper 207 =
    packSparse (2 ^ 40) (upperRows 207) := by decide +kernel

theorem packed207 : packedProduct (lowerRows 207) packedUpper =
    packSparse (2 ^ 40) (targetRows 207) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 207) := by decide +kernel

theorem rowFacts207 : PackedRowFacts 207 := by
  constructor <;> decide +kernel

theorem upper208 : packedUpper 208 =
    packSparse (2 ^ 40) (upperRows 208) := by decide +kernel

theorem packed208 : packedProduct (lowerRows 208) packedUpper =
    packSparse (2 ^ 40) (targetRows 208) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 208) := by decide +kernel

theorem rowFacts208 : PackedRowFacts 208 := by
  constructor <;> decide +kernel

theorem upper209 : packedUpper 209 =
    packSparse (2 ^ 40) (upperRows 209) := by decide +kernel

theorem packed209 : packedProduct (lowerRows 209) packedUpper =
    packSparse (2 ^ 40) (targetRows 209) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 209) := by decide +kernel

theorem rowFacts209 : PackedRowFacts 209 := by
  constructor <;> decide +kernel

theorem upper210 : packedUpper 210 =
    packSparse (2 ^ 40) (upperRows 210) := by decide +kernel

theorem packed210 : packedProduct (lowerRows 210) packedUpper =
    packSparse (2 ^ 40) (targetRows 210) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 210) := by decide +kernel

theorem rowFacts210 : PackedRowFacts 210 := by
  constructor <;> decide +kernel

theorem upper211 : packedUpper 211 =
    packSparse (2 ^ 40) (upperRows 211) := by decide +kernel

theorem packed211 : packedProduct (lowerRows 211) packedUpper =
    packSparse (2 ^ 40) (targetRows 211) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 211) := by decide +kernel

theorem rowFacts211 : PackedRowFacts 211 := by
  constructor <;> decide +kernel

theorem upper212 : packedUpper 212 =
    packSparse (2 ^ 40) (upperRows 212) := by decide +kernel

theorem packed212 : packedProduct (lowerRows 212) packedUpper =
    packSparse (2 ^ 40) (targetRows 212) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 212) := by decide +kernel

theorem rowFacts212 : PackedRowFacts 212 := by
  constructor <;> decide +kernel

theorem upper213 : packedUpper 213 =
    packSparse (2 ^ 40) (upperRows 213) := by decide +kernel

theorem packed213 : packedProduct (lowerRows 213) packedUpper =
    packSparse (2 ^ 40) (targetRows 213) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 213) := by decide +kernel

theorem rowFacts213 : PackedRowFacts 213 := by
  constructor <;> decide +kernel

theorem upper214 : packedUpper 214 =
    packSparse (2 ^ 40) (upperRows 214) := by decide +kernel

theorem packed214 : packedProduct (lowerRows 214) packedUpper =
    packSparse (2 ^ 40) (targetRows 214) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 214) := by decide +kernel

theorem rowFacts214 : PackedRowFacts 214 := by
  constructor <;> decide +kernel

theorem upper215 : packedUpper 215 =
    packSparse (2 ^ 40) (upperRows 215) := by decide +kernel

theorem packed215 : packedProduct (lowerRows 215) packedUpper =
    packSparse (2 ^ 40) (targetRows 215) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 215) := by decide +kernel

theorem rowFacts215 : PackedRowFacts 215 := by
  constructor <;> decide +kernel

theorem upper216 : packedUpper 216 =
    packSparse (2 ^ 40) (upperRows 216) := by decide +kernel

theorem packed216 : packedProduct (lowerRows 216) packedUpper =
    packSparse (2 ^ 40) (targetRows 216) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 216) := by decide +kernel

theorem rowFacts216 : PackedRowFacts 216 := by
  constructor <;> decide +kernel

theorem upper217 : packedUpper 217 =
    packSparse (2 ^ 40) (upperRows 217) := by decide +kernel

theorem packed217 : packedProduct (lowerRows 217) packedUpper =
    packSparse (2 ^ 40) (targetRows 217) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 217) := by decide +kernel

theorem rowFacts217 : PackedRowFacts 217 := by
  constructor <;> decide +kernel

theorem upper218 : packedUpper 218 =
    packSparse (2 ^ 40) (upperRows 218) := by decide +kernel

theorem packed218 : packedProduct (lowerRows 218) packedUpper =
    packSparse (2 ^ 40) (targetRows 218) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 218) := by decide +kernel

theorem rowFacts218 : PackedRowFacts 218 := by
  constructor <;> decide +kernel

theorem upper219 : packedUpper 219 =
    packSparse (2 ^ 40) (upperRows 219) := by decide +kernel

theorem packed219 : packedProduct (lowerRows 219) packedUpper =
    packSparse (2 ^ 40) (targetRows 219) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 219) := by decide +kernel

theorem rowFacts219 : PackedRowFacts 219 := by
  constructor <;> decide +kernel

theorem upper220 : packedUpper 220 =
    packSparse (2 ^ 40) (upperRows 220) := by decide +kernel

theorem packed220 : packedProduct (lowerRows 220) packedUpper =
    packSparse (2 ^ 40) (targetRows 220) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 220) := by decide +kernel

theorem rowFacts220 : PackedRowFacts 220 := by
  constructor <;> decide +kernel

theorem upper221 : packedUpper 221 =
    packSparse (2 ^ 40) (upperRows 221) := by decide +kernel

theorem packed221 : packedProduct (lowerRows 221) packedUpper =
    packSparse (2 ^ 40) (targetRows 221) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 221) := by decide +kernel

theorem rowFacts221 : PackedRowFacts 221 := by
  constructor <;> decide +kernel

theorem upper222 : packedUpper 222 =
    packSparse (2 ^ 40) (upperRows 222) := by decide +kernel

theorem packed222 : packedProduct (lowerRows 222) packedUpper =
    packSparse (2 ^ 40) (targetRows 222) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 222) := by decide +kernel

theorem rowFacts222 : PackedRowFacts 222 := by
  constructor <;> decide +kernel

theorem upper223 : packedUpper 223 =
    packSparse (2 ^ 40) (upperRows 223) := by decide +kernel

theorem packed223 : packedProduct (lowerRows 223) packedUpper =
    packSparse (2 ^ 40) (targetRows 223) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 223) := by decide +kernel

theorem rowFacts223 : PackedRowFacts 223 := by
  constructor <;> decide +kernel

#print axioms packed223

end CertifiedRank.C2.PackedCertificate
