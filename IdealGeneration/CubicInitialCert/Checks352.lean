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

theorem upper352 : packedUpper 352 =
    packSparse (2 ^ 40) (upperRows 352) := by decide +kernel

theorem packed352 : packedProduct (lowerRows 352) packedUpper =
    packSparse (2 ^ 40) (targetRows 352) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 352) := by decide +kernel

theorem rowFacts352 : PackedRowFacts 352 := by
  constructor <;> decide +kernel

theorem upper353 : packedUpper 353 =
    packSparse (2 ^ 40) (upperRows 353) := by decide +kernel

theorem packed353 : packedProduct (lowerRows 353) packedUpper =
    packSparse (2 ^ 40) (targetRows 353) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 353) := by decide +kernel

theorem rowFacts353 : PackedRowFacts 353 := by
  constructor <;> decide +kernel

theorem upper354 : packedUpper 354 =
    packSparse (2 ^ 40) (upperRows 354) := by decide +kernel

theorem packed354 : packedProduct (lowerRows 354) packedUpper =
    packSparse (2 ^ 40) (targetRows 354) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 354) := by decide +kernel

theorem rowFacts354 : PackedRowFacts 354 := by
  constructor <;> decide +kernel

theorem upper355 : packedUpper 355 =
    packSparse (2 ^ 40) (upperRows 355) := by decide +kernel

theorem packed355 : packedProduct (lowerRows 355) packedUpper =
    packSparse (2 ^ 40) (targetRows 355) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 355) := by decide +kernel

theorem rowFacts355 : PackedRowFacts 355 := by
  constructor <;> decide +kernel

theorem upper356 : packedUpper 356 =
    packSparse (2 ^ 40) (upperRows 356) := by decide +kernel

theorem packed356 : packedProduct (lowerRows 356) packedUpper =
    packSparse (2 ^ 40) (targetRows 356) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 356) := by decide +kernel

theorem rowFacts356 : PackedRowFacts 356 := by
  constructor <;> decide +kernel

theorem upper357 : packedUpper 357 =
    packSparse (2 ^ 40) (upperRows 357) := by decide +kernel

theorem packed357 : packedProduct (lowerRows 357) packedUpper =
    packSparse (2 ^ 40) (targetRows 357) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 357) := by decide +kernel

theorem rowFacts357 : PackedRowFacts 357 := by
  constructor <;> decide +kernel

theorem upper358 : packedUpper 358 =
    packSparse (2 ^ 40) (upperRows 358) := by decide +kernel

theorem packed358 : packedProduct (lowerRows 358) packedUpper =
    packSparse (2 ^ 40) (targetRows 358) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 358) := by decide +kernel

theorem rowFacts358 : PackedRowFacts 358 := by
  constructor <;> decide +kernel

theorem upper359 : packedUpper 359 =
    packSparse (2 ^ 40) (upperRows 359) := by decide +kernel

theorem packed359 : packedProduct (lowerRows 359) packedUpper =
    packSparse (2 ^ 40) (targetRows 359) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 359) := by decide +kernel

theorem rowFacts359 : PackedRowFacts 359 := by
  constructor <;> decide +kernel

theorem upper360 : packedUpper 360 =
    packSparse (2 ^ 40) (upperRows 360) := by decide +kernel

theorem packed360 : packedProduct (lowerRows 360) packedUpper =
    packSparse (2 ^ 40) (targetRows 360) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 360) := by decide +kernel

theorem rowFacts360 : PackedRowFacts 360 := by
  constructor <;> decide +kernel

theorem upper361 : packedUpper 361 =
    packSparse (2 ^ 40) (upperRows 361) := by decide +kernel

theorem packed361 : packedProduct (lowerRows 361) packedUpper =
    packSparse (2 ^ 40) (targetRows 361) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 361) := by decide +kernel

theorem rowFacts361 : PackedRowFacts 361 := by
  constructor <;> decide +kernel

theorem upper362 : packedUpper 362 =
    packSparse (2 ^ 40) (upperRows 362) := by decide +kernel

theorem packed362 : packedProduct (lowerRows 362) packedUpper =
    packSparse (2 ^ 40) (targetRows 362) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 362) := by decide +kernel

theorem rowFacts362 : PackedRowFacts 362 := by
  constructor <;> decide +kernel

theorem upper363 : packedUpper 363 =
    packSparse (2 ^ 40) (upperRows 363) := by decide +kernel

theorem packed363 : packedProduct (lowerRows 363) packedUpper =
    packSparse (2 ^ 40) (targetRows 363) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 363) := by decide +kernel

theorem rowFacts363 : PackedRowFacts 363 := by
  constructor <;> decide +kernel

theorem upper364 : packedUpper 364 =
    packSparse (2 ^ 40) (upperRows 364) := by decide +kernel

theorem packed364 : packedProduct (lowerRows 364) packedUpper =
    packSparse (2 ^ 40) (targetRows 364) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 364) := by decide +kernel

theorem rowFacts364 : PackedRowFacts 364 := by
  constructor <;> decide +kernel

theorem upper365 : packedUpper 365 =
    packSparse (2 ^ 40) (upperRows 365) := by decide +kernel

theorem packed365 : packedProduct (lowerRows 365) packedUpper =
    packSparse (2 ^ 40) (targetRows 365) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 365) := by decide +kernel

theorem rowFacts365 : PackedRowFacts 365 := by
  constructor <;> decide +kernel

theorem upper366 : packedUpper 366 =
    packSparse (2 ^ 40) (upperRows 366) := by decide +kernel

theorem packed366 : packedProduct (lowerRows 366) packedUpper =
    packSparse (2 ^ 40) (targetRows 366) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 366) := by decide +kernel

theorem rowFacts366 : PackedRowFacts 366 := by
  constructor <;> decide +kernel

theorem upper367 : packedUpper 367 =
    packSparse (2 ^ 40) (upperRows 367) := by decide +kernel

theorem packed367 : packedProduct (lowerRows 367) packedUpper =
    packSparse (2 ^ 40) (targetRows 367) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 367) := by decide +kernel

theorem rowFacts367 : PackedRowFacts 367 := by
  constructor <;> decide +kernel

theorem upper368 : packedUpper 368 =
    packSparse (2 ^ 40) (upperRows 368) := by decide +kernel

theorem packed368 : packedProduct (lowerRows 368) packedUpper =
    packSparse (2 ^ 40) (targetRows 368) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 368) := by decide +kernel

theorem rowFacts368 : PackedRowFacts 368 := by
  constructor <;> decide +kernel

theorem upper369 : packedUpper 369 =
    packSparse (2 ^ 40) (upperRows 369) := by decide +kernel

theorem packed369 : packedProduct (lowerRows 369) packedUpper =
    packSparse (2 ^ 40) (targetRows 369) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 369) := by decide +kernel

theorem rowFacts369 : PackedRowFacts 369 := by
  constructor <;> decide +kernel

theorem upper370 : packedUpper 370 =
    packSparse (2 ^ 40) (upperRows 370) := by decide +kernel

theorem packed370 : packedProduct (lowerRows 370) packedUpper =
    packSparse (2 ^ 40) (targetRows 370) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 370) := by decide +kernel

theorem rowFacts370 : PackedRowFacts 370 := by
  constructor <;> decide +kernel

theorem upper371 : packedUpper 371 =
    packSparse (2 ^ 40) (upperRows 371) := by decide +kernel

theorem packed371 : packedProduct (lowerRows 371) packedUpper =
    packSparse (2 ^ 40) (targetRows 371) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 371) := by decide +kernel

theorem rowFacts371 : PackedRowFacts 371 := by
  constructor <;> decide +kernel

theorem upper372 : packedUpper 372 =
    packSparse (2 ^ 40) (upperRows 372) := by decide +kernel

theorem packed372 : packedProduct (lowerRows 372) packedUpper =
    packSparse (2 ^ 40) (targetRows 372) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 372) := by decide +kernel

theorem rowFacts372 : PackedRowFacts 372 := by
  constructor <;> decide +kernel

theorem upper373 : packedUpper 373 =
    packSparse (2 ^ 40) (upperRows 373) := by decide +kernel

theorem packed373 : packedProduct (lowerRows 373) packedUpper =
    packSparse (2 ^ 40) (targetRows 373) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 373) := by decide +kernel

theorem rowFacts373 : PackedRowFacts 373 := by
  constructor <;> decide +kernel

theorem upper374 : packedUpper 374 =
    packSparse (2 ^ 40) (upperRows 374) := by decide +kernel

theorem packed374 : packedProduct (lowerRows 374) packedUpper =
    packSparse (2 ^ 40) (targetRows 374) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 374) := by decide +kernel

theorem rowFacts374 : PackedRowFacts 374 := by
  constructor <;> decide +kernel

theorem upper375 : packedUpper 375 =
    packSparse (2 ^ 40) (upperRows 375) := by decide +kernel

theorem packed375 : packedProduct (lowerRows 375) packedUpper =
    packSparse (2 ^ 40) (targetRows 375) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 375) := by decide +kernel

theorem rowFacts375 : PackedRowFacts 375 := by
  constructor <;> decide +kernel

theorem upper376 : packedUpper 376 =
    packSparse (2 ^ 40) (upperRows 376) := by decide +kernel

theorem packed376 : packedProduct (lowerRows 376) packedUpper =
    packSparse (2 ^ 40) (targetRows 376) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 376) := by decide +kernel

theorem rowFacts376 : PackedRowFacts 376 := by
  constructor <;> decide +kernel

theorem upper377 : packedUpper 377 =
    packSparse (2 ^ 40) (upperRows 377) := by decide +kernel

theorem packed377 : packedProduct (lowerRows 377) packedUpper =
    packSparse (2 ^ 40) (targetRows 377) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 377) := by decide +kernel

theorem rowFacts377 : PackedRowFacts 377 := by
  constructor <;> decide +kernel

theorem upper378 : packedUpper 378 =
    packSparse (2 ^ 40) (upperRows 378) := by decide +kernel

theorem packed378 : packedProduct (lowerRows 378) packedUpper =
    packSparse (2 ^ 40) (targetRows 378) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 378) := by decide +kernel

theorem rowFacts378 : PackedRowFacts 378 := by
  constructor <;> decide +kernel

theorem upper379 : packedUpper 379 =
    packSparse (2 ^ 40) (upperRows 379) := by decide +kernel

theorem packed379 : packedProduct (lowerRows 379) packedUpper =
    packSparse (2 ^ 40) (targetRows 379) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 379) := by decide +kernel

theorem rowFacts379 : PackedRowFacts 379 := by
  constructor <;> decide +kernel

theorem upper380 : packedUpper 380 =
    packSparse (2 ^ 40) (upperRows 380) := by decide +kernel

theorem packed380 : packedProduct (lowerRows 380) packedUpper =
    packSparse (2 ^ 40) (targetRows 380) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 380) := by decide +kernel

theorem rowFacts380 : PackedRowFacts 380 := by
  constructor <;> decide +kernel

theorem upper381 : packedUpper 381 =
    packSparse (2 ^ 40) (upperRows 381) := by decide +kernel

theorem packed381 : packedProduct (lowerRows 381) packedUpper =
    packSparse (2 ^ 40) (targetRows 381) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 381) := by decide +kernel

theorem rowFacts381 : PackedRowFacts 381 := by
  constructor <;> decide +kernel

theorem upper382 : packedUpper 382 =
    packSparse (2 ^ 40) (upperRows 382) := by decide +kernel

theorem packed382 : packedProduct (lowerRows 382) packedUpper =
    packSparse (2 ^ 40) (targetRows 382) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 382) := by decide +kernel

theorem rowFacts382 : PackedRowFacts 382 := by
  constructor <;> decide +kernel

theorem upper383 : packedUpper 383 =
    packSparse (2 ^ 40) (upperRows 383) := by decide +kernel

theorem packed383 : packedProduct (lowerRows 383) packedUpper =
    packSparse (2 ^ 40) (targetRows 383) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 383) := by decide +kernel

theorem rowFacts383 : PackedRowFacts 383 := by
  constructor <;> decide +kernel

#print axioms packed383

end CertifiedRank.C2.PackedCertificate
