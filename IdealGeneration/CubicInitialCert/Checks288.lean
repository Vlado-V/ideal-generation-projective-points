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

theorem upper288 : packedUpper 288 =
    packSparse (2 ^ 40) (upperRows 288) := by decide +kernel

theorem packed288 : packedProduct (lowerRows 288) packedUpper =
    packSparse (2 ^ 40) (targetRows 288) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 288) := by decide +kernel

theorem rowFacts288 : PackedRowFacts 288 := by
  constructor <;> decide +kernel

theorem upper289 : packedUpper 289 =
    packSparse (2 ^ 40) (upperRows 289) := by decide +kernel

theorem packed289 : packedProduct (lowerRows 289) packedUpper =
    packSparse (2 ^ 40) (targetRows 289) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 289) := by decide +kernel

theorem rowFacts289 : PackedRowFacts 289 := by
  constructor <;> decide +kernel

theorem upper290 : packedUpper 290 =
    packSparse (2 ^ 40) (upperRows 290) := by decide +kernel

theorem packed290 : packedProduct (lowerRows 290) packedUpper =
    packSparse (2 ^ 40) (targetRows 290) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 290) := by decide +kernel

theorem rowFacts290 : PackedRowFacts 290 := by
  constructor <;> decide +kernel

theorem upper291 : packedUpper 291 =
    packSparse (2 ^ 40) (upperRows 291) := by decide +kernel

theorem packed291 : packedProduct (lowerRows 291) packedUpper =
    packSparse (2 ^ 40) (targetRows 291) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 291) := by decide +kernel

theorem rowFacts291 : PackedRowFacts 291 := by
  constructor <;> decide +kernel

theorem upper292 : packedUpper 292 =
    packSparse (2 ^ 40) (upperRows 292) := by decide +kernel

theorem packed292 : packedProduct (lowerRows 292) packedUpper =
    packSparse (2 ^ 40) (targetRows 292) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 292) := by decide +kernel

theorem rowFacts292 : PackedRowFacts 292 := by
  constructor <;> decide +kernel

theorem upper293 : packedUpper 293 =
    packSparse (2 ^ 40) (upperRows 293) := by decide +kernel

theorem packed293 : packedProduct (lowerRows 293) packedUpper =
    packSparse (2 ^ 40) (targetRows 293) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 293) := by decide +kernel

theorem rowFacts293 : PackedRowFacts 293 := by
  constructor <;> decide +kernel

theorem upper294 : packedUpper 294 =
    packSparse (2 ^ 40) (upperRows 294) := by decide +kernel

theorem packed294 : packedProduct (lowerRows 294) packedUpper =
    packSparse (2 ^ 40) (targetRows 294) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 294) := by decide +kernel

theorem rowFacts294 : PackedRowFacts 294 := by
  constructor <;> decide +kernel

theorem upper295 : packedUpper 295 =
    packSparse (2 ^ 40) (upperRows 295) := by decide +kernel

theorem packed295 : packedProduct (lowerRows 295) packedUpper =
    packSparse (2 ^ 40) (targetRows 295) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 295) := by decide +kernel

theorem rowFacts295 : PackedRowFacts 295 := by
  constructor <;> decide +kernel

theorem upper296 : packedUpper 296 =
    packSparse (2 ^ 40) (upperRows 296) := by decide +kernel

theorem packed296 : packedProduct (lowerRows 296) packedUpper =
    packSparse (2 ^ 40) (targetRows 296) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 296) := by decide +kernel

theorem rowFacts296 : PackedRowFacts 296 := by
  constructor <;> decide +kernel

theorem upper297 : packedUpper 297 =
    packSparse (2 ^ 40) (upperRows 297) := by decide +kernel

theorem packed297 : packedProduct (lowerRows 297) packedUpper =
    packSparse (2 ^ 40) (targetRows 297) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 297) := by decide +kernel

theorem rowFacts297 : PackedRowFacts 297 := by
  constructor <;> decide +kernel

theorem upper298 : packedUpper 298 =
    packSparse (2 ^ 40) (upperRows 298) := by decide +kernel

theorem packed298 : packedProduct (lowerRows 298) packedUpper =
    packSparse (2 ^ 40) (targetRows 298) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 298) := by decide +kernel

theorem rowFacts298 : PackedRowFacts 298 := by
  constructor <;> decide +kernel

theorem upper299 : packedUpper 299 =
    packSparse (2 ^ 40) (upperRows 299) := by decide +kernel

theorem packed299 : packedProduct (lowerRows 299) packedUpper =
    packSparse (2 ^ 40) (targetRows 299) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 299) := by decide +kernel

theorem rowFacts299 : PackedRowFacts 299 := by
  constructor <;> decide +kernel

theorem upper300 : packedUpper 300 =
    packSparse (2 ^ 40) (upperRows 300) := by decide +kernel

theorem packed300 : packedProduct (lowerRows 300) packedUpper =
    packSparse (2 ^ 40) (targetRows 300) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 300) := by decide +kernel

theorem rowFacts300 : PackedRowFacts 300 := by
  constructor <;> decide +kernel

theorem upper301 : packedUpper 301 =
    packSparse (2 ^ 40) (upperRows 301) := by decide +kernel

theorem packed301 : packedProduct (lowerRows 301) packedUpper =
    packSparse (2 ^ 40) (targetRows 301) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 301) := by decide +kernel

theorem rowFacts301 : PackedRowFacts 301 := by
  constructor <;> decide +kernel

theorem upper302 : packedUpper 302 =
    packSparse (2 ^ 40) (upperRows 302) := by decide +kernel

theorem packed302 : packedProduct (lowerRows 302) packedUpper =
    packSparse (2 ^ 40) (targetRows 302) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 302) := by decide +kernel

theorem rowFacts302 : PackedRowFacts 302 := by
  constructor <;> decide +kernel

theorem upper303 : packedUpper 303 =
    packSparse (2 ^ 40) (upperRows 303) := by decide +kernel

theorem packed303 : packedProduct (lowerRows 303) packedUpper =
    packSparse (2 ^ 40) (targetRows 303) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 303) := by decide +kernel

theorem rowFacts303 : PackedRowFacts 303 := by
  constructor <;> decide +kernel

theorem upper304 : packedUpper 304 =
    packSparse (2 ^ 40) (upperRows 304) := by decide +kernel

theorem packed304 : packedProduct (lowerRows 304) packedUpper =
    packSparse (2 ^ 40) (targetRows 304) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 304) := by decide +kernel

theorem rowFacts304 : PackedRowFacts 304 := by
  constructor <;> decide +kernel

theorem upper305 : packedUpper 305 =
    packSparse (2 ^ 40) (upperRows 305) := by decide +kernel

theorem packed305 : packedProduct (lowerRows 305) packedUpper =
    packSparse (2 ^ 40) (targetRows 305) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 305) := by decide +kernel

theorem rowFacts305 : PackedRowFacts 305 := by
  constructor <;> decide +kernel

theorem upper306 : packedUpper 306 =
    packSparse (2 ^ 40) (upperRows 306) := by decide +kernel

theorem packed306 : packedProduct (lowerRows 306) packedUpper =
    packSparse (2 ^ 40) (targetRows 306) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 306) := by decide +kernel

theorem rowFacts306 : PackedRowFacts 306 := by
  constructor <;> decide +kernel

theorem upper307 : packedUpper 307 =
    packSparse (2 ^ 40) (upperRows 307) := by decide +kernel

theorem packed307 : packedProduct (lowerRows 307) packedUpper =
    packSparse (2 ^ 40) (targetRows 307) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 307) := by decide +kernel

theorem rowFacts307 : PackedRowFacts 307 := by
  constructor <;> decide +kernel

theorem upper308 : packedUpper 308 =
    packSparse (2 ^ 40) (upperRows 308) := by decide +kernel

theorem packed308 : packedProduct (lowerRows 308) packedUpper =
    packSparse (2 ^ 40) (targetRows 308) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 308) := by decide +kernel

theorem rowFacts308 : PackedRowFacts 308 := by
  constructor <;> decide +kernel

theorem upper309 : packedUpper 309 =
    packSparse (2 ^ 40) (upperRows 309) := by decide +kernel

theorem packed309 : packedProduct (lowerRows 309) packedUpper =
    packSparse (2 ^ 40) (targetRows 309) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 309) := by decide +kernel

theorem rowFacts309 : PackedRowFacts 309 := by
  constructor <;> decide +kernel

theorem upper310 : packedUpper 310 =
    packSparse (2 ^ 40) (upperRows 310) := by decide +kernel

theorem packed310 : packedProduct (lowerRows 310) packedUpper =
    packSparse (2 ^ 40) (targetRows 310) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 310) := by decide +kernel

theorem rowFacts310 : PackedRowFacts 310 := by
  constructor <;> decide +kernel

theorem upper311 : packedUpper 311 =
    packSparse (2 ^ 40) (upperRows 311) := by decide +kernel

theorem packed311 : packedProduct (lowerRows 311) packedUpper =
    packSparse (2 ^ 40) (targetRows 311) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 311) := by decide +kernel

theorem rowFacts311 : PackedRowFacts 311 := by
  constructor <;> decide +kernel

theorem upper312 : packedUpper 312 =
    packSparse (2 ^ 40) (upperRows 312) := by decide +kernel

theorem packed312 : packedProduct (lowerRows 312) packedUpper =
    packSparse (2 ^ 40) (targetRows 312) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 312) := by decide +kernel

theorem rowFacts312 : PackedRowFacts 312 := by
  constructor <;> decide +kernel

theorem upper313 : packedUpper 313 =
    packSparse (2 ^ 40) (upperRows 313) := by decide +kernel

theorem packed313 : packedProduct (lowerRows 313) packedUpper =
    packSparse (2 ^ 40) (targetRows 313) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 313) := by decide +kernel

theorem rowFacts313 : PackedRowFacts 313 := by
  constructor <;> decide +kernel

theorem upper314 : packedUpper 314 =
    packSparse (2 ^ 40) (upperRows 314) := by decide +kernel

theorem packed314 : packedProduct (lowerRows 314) packedUpper =
    packSparse (2 ^ 40) (targetRows 314) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 314) := by decide +kernel

theorem rowFacts314 : PackedRowFacts 314 := by
  constructor <;> decide +kernel

theorem upper315 : packedUpper 315 =
    packSparse (2 ^ 40) (upperRows 315) := by decide +kernel

theorem packed315 : packedProduct (lowerRows 315) packedUpper =
    packSparse (2 ^ 40) (targetRows 315) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 315) := by decide +kernel

theorem rowFacts315 : PackedRowFacts 315 := by
  constructor <;> decide +kernel

theorem upper316 : packedUpper 316 =
    packSparse (2 ^ 40) (upperRows 316) := by decide +kernel

theorem packed316 : packedProduct (lowerRows 316) packedUpper =
    packSparse (2 ^ 40) (targetRows 316) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 316) := by decide +kernel

theorem rowFacts316 : PackedRowFacts 316 := by
  constructor <;> decide +kernel

theorem upper317 : packedUpper 317 =
    packSparse (2 ^ 40) (upperRows 317) := by decide +kernel

theorem packed317 : packedProduct (lowerRows 317) packedUpper =
    packSparse (2 ^ 40) (targetRows 317) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 317) := by decide +kernel

theorem rowFacts317 : PackedRowFacts 317 := by
  constructor <;> decide +kernel

theorem upper318 : packedUpper 318 =
    packSparse (2 ^ 40) (upperRows 318) := by decide +kernel

theorem packed318 : packedProduct (lowerRows 318) packedUpper =
    packSparse (2 ^ 40) (targetRows 318) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 318) := by decide +kernel

theorem rowFacts318 : PackedRowFacts 318 := by
  constructor <;> decide +kernel

theorem upper319 : packedUpper 319 =
    packSparse (2 ^ 40) (upperRows 319) := by decide +kernel

theorem packed319 : packedProduct (lowerRows 319) packedUpper =
    packSparse (2 ^ 40) (targetRows 319) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 319) := by decide +kernel

theorem rowFacts319 : PackedRowFacts 319 := by
  constructor <;> decide +kernel

#print axioms packed319

end CertifiedRank.C2.PackedCertificate
