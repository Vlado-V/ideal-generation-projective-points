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

theorem upper256 : packedUpper 256 =
    packSparse (2 ^ 40) (upperRows 256) := by decide +kernel

theorem packed256 : packedProduct (lowerRows 256) packedUpper =
    packSparse (2 ^ 40) (targetRows 256) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 256) := by decide +kernel

theorem rowFacts256 : PackedRowFacts 256 := by
  constructor <;> decide +kernel

theorem upper257 : packedUpper 257 =
    packSparse (2 ^ 40) (upperRows 257) := by decide +kernel

theorem packed257 : packedProduct (lowerRows 257) packedUpper =
    packSparse (2 ^ 40) (targetRows 257) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 257) := by decide +kernel

theorem rowFacts257 : PackedRowFacts 257 := by
  constructor <;> decide +kernel

theorem upper258 : packedUpper 258 =
    packSparse (2 ^ 40) (upperRows 258) := by decide +kernel

theorem packed258 : packedProduct (lowerRows 258) packedUpper =
    packSparse (2 ^ 40) (targetRows 258) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 258) := by decide +kernel

theorem rowFacts258 : PackedRowFacts 258 := by
  constructor <;> decide +kernel

theorem upper259 : packedUpper 259 =
    packSparse (2 ^ 40) (upperRows 259) := by decide +kernel

theorem packed259 : packedProduct (lowerRows 259) packedUpper =
    packSparse (2 ^ 40) (targetRows 259) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 259) := by decide +kernel

theorem rowFacts259 : PackedRowFacts 259 := by
  constructor <;> decide +kernel

theorem upper260 : packedUpper 260 =
    packSparse (2 ^ 40) (upperRows 260) := by decide +kernel

theorem packed260 : packedProduct (lowerRows 260) packedUpper =
    packSparse (2 ^ 40) (targetRows 260) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 260) := by decide +kernel

theorem rowFacts260 : PackedRowFacts 260 := by
  constructor <;> decide +kernel

theorem upper261 : packedUpper 261 =
    packSparse (2 ^ 40) (upperRows 261) := by decide +kernel

theorem packed261 : packedProduct (lowerRows 261) packedUpper =
    packSparse (2 ^ 40) (targetRows 261) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 261) := by decide +kernel

theorem rowFacts261 : PackedRowFacts 261 := by
  constructor <;> decide +kernel

theorem upper262 : packedUpper 262 =
    packSparse (2 ^ 40) (upperRows 262) := by decide +kernel

theorem packed262 : packedProduct (lowerRows 262) packedUpper =
    packSparse (2 ^ 40) (targetRows 262) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 262) := by decide +kernel

theorem rowFacts262 : PackedRowFacts 262 := by
  constructor <;> decide +kernel

theorem upper263 : packedUpper 263 =
    packSparse (2 ^ 40) (upperRows 263) := by decide +kernel

theorem packed263 : packedProduct (lowerRows 263) packedUpper =
    packSparse (2 ^ 40) (targetRows 263) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 263) := by decide +kernel

theorem rowFacts263 : PackedRowFacts 263 := by
  constructor <;> decide +kernel

theorem upper264 : packedUpper 264 =
    packSparse (2 ^ 40) (upperRows 264) := by decide +kernel

theorem packed264 : packedProduct (lowerRows 264) packedUpper =
    packSparse (2 ^ 40) (targetRows 264) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 264) := by decide +kernel

theorem rowFacts264 : PackedRowFacts 264 := by
  constructor <;> decide +kernel

theorem upper265 : packedUpper 265 =
    packSparse (2 ^ 40) (upperRows 265) := by decide +kernel

theorem packed265 : packedProduct (lowerRows 265) packedUpper =
    packSparse (2 ^ 40) (targetRows 265) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 265) := by decide +kernel

theorem rowFacts265 : PackedRowFacts 265 := by
  constructor <;> decide +kernel

theorem upper266 : packedUpper 266 =
    packSparse (2 ^ 40) (upperRows 266) := by decide +kernel

theorem packed266 : packedProduct (lowerRows 266) packedUpper =
    packSparse (2 ^ 40) (targetRows 266) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 266) := by decide +kernel

theorem rowFacts266 : PackedRowFacts 266 := by
  constructor <;> decide +kernel

theorem upper267 : packedUpper 267 =
    packSparse (2 ^ 40) (upperRows 267) := by decide +kernel

theorem packed267 : packedProduct (lowerRows 267) packedUpper =
    packSparse (2 ^ 40) (targetRows 267) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 267) := by decide +kernel

theorem rowFacts267 : PackedRowFacts 267 := by
  constructor <;> decide +kernel

theorem upper268 : packedUpper 268 =
    packSparse (2 ^ 40) (upperRows 268) := by decide +kernel

theorem packed268 : packedProduct (lowerRows 268) packedUpper =
    packSparse (2 ^ 40) (targetRows 268) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 268) := by decide +kernel

theorem rowFacts268 : PackedRowFacts 268 := by
  constructor <;> decide +kernel

theorem upper269 : packedUpper 269 =
    packSparse (2 ^ 40) (upperRows 269) := by decide +kernel

theorem packed269 : packedProduct (lowerRows 269) packedUpper =
    packSparse (2 ^ 40) (targetRows 269) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 269) := by decide +kernel

theorem rowFacts269 : PackedRowFacts 269 := by
  constructor <;> decide +kernel

theorem upper270 : packedUpper 270 =
    packSparse (2 ^ 40) (upperRows 270) := by decide +kernel

theorem packed270 : packedProduct (lowerRows 270) packedUpper =
    packSparse (2 ^ 40) (targetRows 270) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 270) := by decide +kernel

theorem rowFacts270 : PackedRowFacts 270 := by
  constructor <;> decide +kernel

theorem upper271 : packedUpper 271 =
    packSparse (2 ^ 40) (upperRows 271) := by decide +kernel

theorem packed271 : packedProduct (lowerRows 271) packedUpper =
    packSparse (2 ^ 40) (targetRows 271) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 271) := by decide +kernel

theorem rowFacts271 : PackedRowFacts 271 := by
  constructor <;> decide +kernel

theorem upper272 : packedUpper 272 =
    packSparse (2 ^ 40) (upperRows 272) := by decide +kernel

theorem packed272 : packedProduct (lowerRows 272) packedUpper =
    packSparse (2 ^ 40) (targetRows 272) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 272) := by decide +kernel

theorem rowFacts272 : PackedRowFacts 272 := by
  constructor <;> decide +kernel

theorem upper273 : packedUpper 273 =
    packSparse (2 ^ 40) (upperRows 273) := by decide +kernel

theorem packed273 : packedProduct (lowerRows 273) packedUpper =
    packSparse (2 ^ 40) (targetRows 273) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 273) := by decide +kernel

theorem rowFacts273 : PackedRowFacts 273 := by
  constructor <;> decide +kernel

theorem upper274 : packedUpper 274 =
    packSparse (2 ^ 40) (upperRows 274) := by decide +kernel

theorem packed274 : packedProduct (lowerRows 274) packedUpper =
    packSparse (2 ^ 40) (targetRows 274) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 274) := by decide +kernel

theorem rowFacts274 : PackedRowFacts 274 := by
  constructor <;> decide +kernel

theorem upper275 : packedUpper 275 =
    packSparse (2 ^ 40) (upperRows 275) := by decide +kernel

theorem packed275 : packedProduct (lowerRows 275) packedUpper =
    packSparse (2 ^ 40) (targetRows 275) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 275) := by decide +kernel

theorem rowFacts275 : PackedRowFacts 275 := by
  constructor <;> decide +kernel

theorem upper276 : packedUpper 276 =
    packSparse (2 ^ 40) (upperRows 276) := by decide +kernel

theorem packed276 : packedProduct (lowerRows 276) packedUpper =
    packSparse (2 ^ 40) (targetRows 276) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 276) := by decide +kernel

theorem rowFacts276 : PackedRowFacts 276 := by
  constructor <;> decide +kernel

theorem upper277 : packedUpper 277 =
    packSparse (2 ^ 40) (upperRows 277) := by decide +kernel

theorem packed277 : packedProduct (lowerRows 277) packedUpper =
    packSparse (2 ^ 40) (targetRows 277) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 277) := by decide +kernel

theorem rowFacts277 : PackedRowFacts 277 := by
  constructor <;> decide +kernel

theorem upper278 : packedUpper 278 =
    packSparse (2 ^ 40) (upperRows 278) := by decide +kernel

theorem packed278 : packedProduct (lowerRows 278) packedUpper =
    packSparse (2 ^ 40) (targetRows 278) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 278) := by decide +kernel

theorem rowFacts278 : PackedRowFacts 278 := by
  constructor <;> decide +kernel

theorem upper279 : packedUpper 279 =
    packSparse (2 ^ 40) (upperRows 279) := by decide +kernel

theorem packed279 : packedProduct (lowerRows 279) packedUpper =
    packSparse (2 ^ 40) (targetRows 279) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 279) := by decide +kernel

theorem rowFacts279 : PackedRowFacts 279 := by
  constructor <;> decide +kernel

theorem upper280 : packedUpper 280 =
    packSparse (2 ^ 40) (upperRows 280) := by decide +kernel

theorem packed280 : packedProduct (lowerRows 280) packedUpper =
    packSparse (2 ^ 40) (targetRows 280) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 280) := by decide +kernel

theorem rowFacts280 : PackedRowFacts 280 := by
  constructor <;> decide +kernel

theorem upper281 : packedUpper 281 =
    packSparse (2 ^ 40) (upperRows 281) := by decide +kernel

theorem packed281 : packedProduct (lowerRows 281) packedUpper =
    packSparse (2 ^ 40) (targetRows 281) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 281) := by decide +kernel

theorem rowFacts281 : PackedRowFacts 281 := by
  constructor <;> decide +kernel

theorem upper282 : packedUpper 282 =
    packSparse (2 ^ 40) (upperRows 282) := by decide +kernel

theorem packed282 : packedProduct (lowerRows 282) packedUpper =
    packSparse (2 ^ 40) (targetRows 282) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 282) := by decide +kernel

theorem rowFacts282 : PackedRowFacts 282 := by
  constructor <;> decide +kernel

theorem upper283 : packedUpper 283 =
    packSparse (2 ^ 40) (upperRows 283) := by decide +kernel

theorem packed283 : packedProduct (lowerRows 283) packedUpper =
    packSparse (2 ^ 40) (targetRows 283) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 283) := by decide +kernel

theorem rowFacts283 : PackedRowFacts 283 := by
  constructor <;> decide +kernel

theorem upper284 : packedUpper 284 =
    packSparse (2 ^ 40) (upperRows 284) := by decide +kernel

theorem packed284 : packedProduct (lowerRows 284) packedUpper =
    packSparse (2 ^ 40) (targetRows 284) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 284) := by decide +kernel

theorem rowFacts284 : PackedRowFacts 284 := by
  constructor <;> decide +kernel

theorem upper285 : packedUpper 285 =
    packSparse (2 ^ 40) (upperRows 285) := by decide +kernel

theorem packed285 : packedProduct (lowerRows 285) packedUpper =
    packSparse (2 ^ 40) (targetRows 285) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 285) := by decide +kernel

theorem rowFacts285 : PackedRowFacts 285 := by
  constructor <;> decide +kernel

theorem upper286 : packedUpper 286 =
    packSparse (2 ^ 40) (upperRows 286) := by decide +kernel

theorem packed286 : packedProduct (lowerRows 286) packedUpper =
    packSparse (2 ^ 40) (targetRows 286) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 286) := by decide +kernel

theorem rowFacts286 : PackedRowFacts 286 := by
  constructor <;> decide +kernel

theorem upper287 : packedUpper 287 =
    packSparse (2 ^ 40) (upperRows 287) := by decide +kernel

theorem packed287 : packedProduct (lowerRows 287) packedUpper =
    packSparse (2 ^ 40) (targetRows 287) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 287) := by decide +kernel

theorem rowFacts287 : PackedRowFacts 287 := by
  constructor <;> decide +kernel

#print axioms packed287

end CertifiedRank.C2.PackedCertificate
