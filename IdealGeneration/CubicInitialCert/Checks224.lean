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

theorem upper224 : packedUpper 224 =
    packSparse (2 ^ 40) (upperRows 224) := by decide +kernel

theorem packed224 : packedProduct (lowerRows 224) packedUpper =
    packSparse (2 ^ 40) (targetRows 224) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 224) := by decide +kernel

theorem rowFacts224 : PackedRowFacts 224 := by
  constructor <;> decide +kernel

theorem upper225 : packedUpper 225 =
    packSparse (2 ^ 40) (upperRows 225) := by decide +kernel

theorem packed225 : packedProduct (lowerRows 225) packedUpper =
    packSparse (2 ^ 40) (targetRows 225) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 225) := by decide +kernel

theorem rowFacts225 : PackedRowFacts 225 := by
  constructor <;> decide +kernel

theorem upper226 : packedUpper 226 =
    packSparse (2 ^ 40) (upperRows 226) := by decide +kernel

theorem packed226 : packedProduct (lowerRows 226) packedUpper =
    packSparse (2 ^ 40) (targetRows 226) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 226) := by decide +kernel

theorem rowFacts226 : PackedRowFacts 226 := by
  constructor <;> decide +kernel

theorem upper227 : packedUpper 227 =
    packSparse (2 ^ 40) (upperRows 227) := by decide +kernel

theorem packed227 : packedProduct (lowerRows 227) packedUpper =
    packSparse (2 ^ 40) (targetRows 227) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 227) := by decide +kernel

theorem rowFacts227 : PackedRowFacts 227 := by
  constructor <;> decide +kernel

theorem upper228 : packedUpper 228 =
    packSparse (2 ^ 40) (upperRows 228) := by decide +kernel

theorem packed228 : packedProduct (lowerRows 228) packedUpper =
    packSparse (2 ^ 40) (targetRows 228) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 228) := by decide +kernel

theorem rowFacts228 : PackedRowFacts 228 := by
  constructor <;> decide +kernel

theorem upper229 : packedUpper 229 =
    packSparse (2 ^ 40) (upperRows 229) := by decide +kernel

theorem packed229 : packedProduct (lowerRows 229) packedUpper =
    packSparse (2 ^ 40) (targetRows 229) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 229) := by decide +kernel

theorem rowFacts229 : PackedRowFacts 229 := by
  constructor <;> decide +kernel

theorem upper230 : packedUpper 230 =
    packSparse (2 ^ 40) (upperRows 230) := by decide +kernel

theorem packed230 : packedProduct (lowerRows 230) packedUpper =
    packSparse (2 ^ 40) (targetRows 230) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 230) := by decide +kernel

theorem rowFacts230 : PackedRowFacts 230 := by
  constructor <;> decide +kernel

theorem upper231 : packedUpper 231 =
    packSparse (2 ^ 40) (upperRows 231) := by decide +kernel

theorem packed231 : packedProduct (lowerRows 231) packedUpper =
    packSparse (2 ^ 40) (targetRows 231) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 231) := by decide +kernel

theorem rowFacts231 : PackedRowFacts 231 := by
  constructor <;> decide +kernel

theorem upper232 : packedUpper 232 =
    packSparse (2 ^ 40) (upperRows 232) := by decide +kernel

theorem packed232 : packedProduct (lowerRows 232) packedUpper =
    packSparse (2 ^ 40) (targetRows 232) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 232) := by decide +kernel

theorem rowFacts232 : PackedRowFacts 232 := by
  constructor <;> decide +kernel

theorem upper233 : packedUpper 233 =
    packSparse (2 ^ 40) (upperRows 233) := by decide +kernel

theorem packed233 : packedProduct (lowerRows 233) packedUpper =
    packSparse (2 ^ 40) (targetRows 233) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 233) := by decide +kernel

theorem rowFacts233 : PackedRowFacts 233 := by
  constructor <;> decide +kernel

theorem upper234 : packedUpper 234 =
    packSparse (2 ^ 40) (upperRows 234) := by decide +kernel

theorem packed234 : packedProduct (lowerRows 234) packedUpper =
    packSparse (2 ^ 40) (targetRows 234) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 234) := by decide +kernel

theorem rowFacts234 : PackedRowFacts 234 := by
  constructor <;> decide +kernel

theorem upper235 : packedUpper 235 =
    packSparse (2 ^ 40) (upperRows 235) := by decide +kernel

theorem packed235 : packedProduct (lowerRows 235) packedUpper =
    packSparse (2 ^ 40) (targetRows 235) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 235) := by decide +kernel

theorem rowFacts235 : PackedRowFacts 235 := by
  constructor <;> decide +kernel

theorem upper236 : packedUpper 236 =
    packSparse (2 ^ 40) (upperRows 236) := by decide +kernel

theorem packed236 : packedProduct (lowerRows 236) packedUpper =
    packSparse (2 ^ 40) (targetRows 236) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 236) := by decide +kernel

theorem rowFacts236 : PackedRowFacts 236 := by
  constructor <;> decide +kernel

theorem upper237 : packedUpper 237 =
    packSparse (2 ^ 40) (upperRows 237) := by decide +kernel

theorem packed237 : packedProduct (lowerRows 237) packedUpper =
    packSparse (2 ^ 40) (targetRows 237) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 237) := by decide +kernel

theorem rowFacts237 : PackedRowFacts 237 := by
  constructor <;> decide +kernel

theorem upper238 : packedUpper 238 =
    packSparse (2 ^ 40) (upperRows 238) := by decide +kernel

theorem packed238 : packedProduct (lowerRows 238) packedUpper =
    packSparse (2 ^ 40) (targetRows 238) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 238) := by decide +kernel

theorem rowFacts238 : PackedRowFacts 238 := by
  constructor <;> decide +kernel

theorem upper239 : packedUpper 239 =
    packSparse (2 ^ 40) (upperRows 239) := by decide +kernel

theorem packed239 : packedProduct (lowerRows 239) packedUpper =
    packSparse (2 ^ 40) (targetRows 239) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 239) := by decide +kernel

theorem rowFacts239 : PackedRowFacts 239 := by
  constructor <;> decide +kernel

theorem upper240 : packedUpper 240 =
    packSparse (2 ^ 40) (upperRows 240) := by decide +kernel

theorem packed240 : packedProduct (lowerRows 240) packedUpper =
    packSparse (2 ^ 40) (targetRows 240) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 240) := by decide +kernel

theorem rowFacts240 : PackedRowFacts 240 := by
  constructor <;> decide +kernel

theorem upper241 : packedUpper 241 =
    packSparse (2 ^ 40) (upperRows 241) := by decide +kernel

theorem packed241 : packedProduct (lowerRows 241) packedUpper =
    packSparse (2 ^ 40) (targetRows 241) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 241) := by decide +kernel

theorem rowFacts241 : PackedRowFacts 241 := by
  constructor <;> decide +kernel

theorem upper242 : packedUpper 242 =
    packSparse (2 ^ 40) (upperRows 242) := by decide +kernel

theorem packed242 : packedProduct (lowerRows 242) packedUpper =
    packSparse (2 ^ 40) (targetRows 242) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 242) := by decide +kernel

theorem rowFacts242 : PackedRowFacts 242 := by
  constructor <;> decide +kernel

theorem upper243 : packedUpper 243 =
    packSparse (2 ^ 40) (upperRows 243) := by decide +kernel

theorem packed243 : packedProduct (lowerRows 243) packedUpper =
    packSparse (2 ^ 40) (targetRows 243) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 243) := by decide +kernel

theorem rowFacts243 : PackedRowFacts 243 := by
  constructor <;> decide +kernel

theorem upper244 : packedUpper 244 =
    packSparse (2 ^ 40) (upperRows 244) := by decide +kernel

theorem packed244 : packedProduct (lowerRows 244) packedUpper =
    packSparse (2 ^ 40) (targetRows 244) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 244) := by decide +kernel

theorem rowFacts244 : PackedRowFacts 244 := by
  constructor <;> decide +kernel

theorem upper245 : packedUpper 245 =
    packSparse (2 ^ 40) (upperRows 245) := by decide +kernel

theorem packed245 : packedProduct (lowerRows 245) packedUpper =
    packSparse (2 ^ 40) (targetRows 245) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 245) := by decide +kernel

theorem rowFacts245 : PackedRowFacts 245 := by
  constructor <;> decide +kernel

theorem upper246 : packedUpper 246 =
    packSparse (2 ^ 40) (upperRows 246) := by decide +kernel

theorem packed246 : packedProduct (lowerRows 246) packedUpper =
    packSparse (2 ^ 40) (targetRows 246) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 246) := by decide +kernel

theorem rowFacts246 : PackedRowFacts 246 := by
  constructor <;> decide +kernel

theorem upper247 : packedUpper 247 =
    packSparse (2 ^ 40) (upperRows 247) := by decide +kernel

theorem packed247 : packedProduct (lowerRows 247) packedUpper =
    packSparse (2 ^ 40) (targetRows 247) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 247) := by decide +kernel

theorem rowFacts247 : PackedRowFacts 247 := by
  constructor <;> decide +kernel

theorem upper248 : packedUpper 248 =
    packSparse (2 ^ 40) (upperRows 248) := by decide +kernel

theorem packed248 : packedProduct (lowerRows 248) packedUpper =
    packSparse (2 ^ 40) (targetRows 248) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 248) := by decide +kernel

theorem rowFacts248 : PackedRowFacts 248 := by
  constructor <;> decide +kernel

theorem upper249 : packedUpper 249 =
    packSparse (2 ^ 40) (upperRows 249) := by decide +kernel

theorem packed249 : packedProduct (lowerRows 249) packedUpper =
    packSparse (2 ^ 40) (targetRows 249) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 249) := by decide +kernel

theorem rowFacts249 : PackedRowFacts 249 := by
  constructor <;> decide +kernel

theorem upper250 : packedUpper 250 =
    packSparse (2 ^ 40) (upperRows 250) := by decide +kernel

theorem packed250 : packedProduct (lowerRows 250) packedUpper =
    packSparse (2 ^ 40) (targetRows 250) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 250) := by decide +kernel

theorem rowFacts250 : PackedRowFacts 250 := by
  constructor <;> decide +kernel

theorem upper251 : packedUpper 251 =
    packSparse (2 ^ 40) (upperRows 251) := by decide +kernel

theorem packed251 : packedProduct (lowerRows 251) packedUpper =
    packSparse (2 ^ 40) (targetRows 251) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 251) := by decide +kernel

theorem rowFacts251 : PackedRowFacts 251 := by
  constructor <;> decide +kernel

theorem upper252 : packedUpper 252 =
    packSparse (2 ^ 40) (upperRows 252) := by decide +kernel

theorem packed252 : packedProduct (lowerRows 252) packedUpper =
    packSparse (2 ^ 40) (targetRows 252) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 252) := by decide +kernel

theorem rowFacts252 : PackedRowFacts 252 := by
  constructor <;> decide +kernel

theorem upper253 : packedUpper 253 =
    packSparse (2 ^ 40) (upperRows 253) := by decide +kernel

theorem packed253 : packedProduct (lowerRows 253) packedUpper =
    packSparse (2 ^ 40) (targetRows 253) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 253) := by decide +kernel

theorem rowFacts253 : PackedRowFacts 253 := by
  constructor <;> decide +kernel

theorem upper254 : packedUpper 254 =
    packSparse (2 ^ 40) (upperRows 254) := by decide +kernel

theorem packed254 : packedProduct (lowerRows 254) packedUpper =
    packSparse (2 ^ 40) (targetRows 254) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 254) := by decide +kernel

theorem rowFacts254 : PackedRowFacts 254 := by
  constructor <;> decide +kernel

theorem upper255 : packedUpper 255 =
    packSparse (2 ^ 40) (upperRows 255) := by decide +kernel

theorem packed255 : packedProduct (lowerRows 255) packedUpper =
    packSparse (2 ^ 40) (targetRows 255) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 255) := by decide +kernel

theorem rowFacts255 : PackedRowFacts 255 := by
  constructor <;> decide +kernel

#print axioms packed255

end CertifiedRank.C2.PackedCertificate
