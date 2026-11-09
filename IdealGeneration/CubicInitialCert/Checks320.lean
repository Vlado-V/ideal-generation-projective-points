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

theorem upper320 : packedUpper 320 =
    packSparse (2 ^ 40) (upperRows 320) := by decide +kernel

theorem packed320 : packedProduct (lowerRows 320) packedUpper =
    packSparse (2 ^ 40) (targetRows 320) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 320) := by decide +kernel

theorem rowFacts320 : PackedRowFacts 320 := by
  constructor <;> decide +kernel

theorem upper321 : packedUpper 321 =
    packSparse (2 ^ 40) (upperRows 321) := by decide +kernel

theorem packed321 : packedProduct (lowerRows 321) packedUpper =
    packSparse (2 ^ 40) (targetRows 321) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 321) := by decide +kernel

theorem rowFacts321 : PackedRowFacts 321 := by
  constructor <;> decide +kernel

theorem upper322 : packedUpper 322 =
    packSparse (2 ^ 40) (upperRows 322) := by decide +kernel

theorem packed322 : packedProduct (lowerRows 322) packedUpper =
    packSparse (2 ^ 40) (targetRows 322) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 322) := by decide +kernel

theorem rowFacts322 : PackedRowFacts 322 := by
  constructor <;> decide +kernel

theorem upper323 : packedUpper 323 =
    packSparse (2 ^ 40) (upperRows 323) := by decide +kernel

theorem packed323 : packedProduct (lowerRows 323) packedUpper =
    packSparse (2 ^ 40) (targetRows 323) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 323) := by decide +kernel

theorem rowFacts323 : PackedRowFacts 323 := by
  constructor <;> decide +kernel

theorem upper324 : packedUpper 324 =
    packSparse (2 ^ 40) (upperRows 324) := by decide +kernel

theorem packed324 : packedProduct (lowerRows 324) packedUpper =
    packSparse (2 ^ 40) (targetRows 324) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 324) := by decide +kernel

theorem rowFacts324 : PackedRowFacts 324 := by
  constructor <;> decide +kernel

theorem upper325 : packedUpper 325 =
    packSparse (2 ^ 40) (upperRows 325) := by decide +kernel

theorem packed325 : packedProduct (lowerRows 325) packedUpper =
    packSparse (2 ^ 40) (targetRows 325) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 325) := by decide +kernel

theorem rowFacts325 : PackedRowFacts 325 := by
  constructor <;> decide +kernel

theorem upper326 : packedUpper 326 =
    packSparse (2 ^ 40) (upperRows 326) := by decide +kernel

theorem packed326 : packedProduct (lowerRows 326) packedUpper =
    packSparse (2 ^ 40) (targetRows 326) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 326) := by decide +kernel

theorem rowFacts326 : PackedRowFacts 326 := by
  constructor <;> decide +kernel

theorem upper327 : packedUpper 327 =
    packSparse (2 ^ 40) (upperRows 327) := by decide +kernel

theorem packed327 : packedProduct (lowerRows 327) packedUpper =
    packSparse (2 ^ 40) (targetRows 327) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 327) := by decide +kernel

theorem rowFacts327 : PackedRowFacts 327 := by
  constructor <;> decide +kernel

theorem upper328 : packedUpper 328 =
    packSparse (2 ^ 40) (upperRows 328) := by decide +kernel

theorem packed328 : packedProduct (lowerRows 328) packedUpper =
    packSparse (2 ^ 40) (targetRows 328) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 328) := by decide +kernel

theorem rowFacts328 : PackedRowFacts 328 := by
  constructor <;> decide +kernel

theorem upper329 : packedUpper 329 =
    packSparse (2 ^ 40) (upperRows 329) := by decide +kernel

theorem packed329 : packedProduct (lowerRows 329) packedUpper =
    packSparse (2 ^ 40) (targetRows 329) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 329) := by decide +kernel

theorem rowFacts329 : PackedRowFacts 329 := by
  constructor <;> decide +kernel

theorem upper330 : packedUpper 330 =
    packSparse (2 ^ 40) (upperRows 330) := by decide +kernel

theorem packed330 : packedProduct (lowerRows 330) packedUpper =
    packSparse (2 ^ 40) (targetRows 330) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 330) := by decide +kernel

theorem rowFacts330 : PackedRowFacts 330 := by
  constructor <;> decide +kernel

theorem upper331 : packedUpper 331 =
    packSparse (2 ^ 40) (upperRows 331) := by decide +kernel

theorem packed331 : packedProduct (lowerRows 331) packedUpper =
    packSparse (2 ^ 40) (targetRows 331) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 331) := by decide +kernel

theorem rowFacts331 : PackedRowFacts 331 := by
  constructor <;> decide +kernel

theorem upper332 : packedUpper 332 =
    packSparse (2 ^ 40) (upperRows 332) := by decide +kernel

theorem packed332 : packedProduct (lowerRows 332) packedUpper =
    packSparse (2 ^ 40) (targetRows 332) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 332) := by decide +kernel

theorem rowFacts332 : PackedRowFacts 332 := by
  constructor <;> decide +kernel

theorem upper333 : packedUpper 333 =
    packSparse (2 ^ 40) (upperRows 333) := by decide +kernel

theorem packed333 : packedProduct (lowerRows 333) packedUpper =
    packSparse (2 ^ 40) (targetRows 333) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 333) := by decide +kernel

theorem rowFacts333 : PackedRowFacts 333 := by
  constructor <;> decide +kernel

theorem upper334 : packedUpper 334 =
    packSparse (2 ^ 40) (upperRows 334) := by decide +kernel

theorem packed334 : packedProduct (lowerRows 334) packedUpper =
    packSparse (2 ^ 40) (targetRows 334) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 334) := by decide +kernel

theorem rowFacts334 : PackedRowFacts 334 := by
  constructor <;> decide +kernel

theorem upper335 : packedUpper 335 =
    packSparse (2 ^ 40) (upperRows 335) := by decide +kernel

theorem packed335 : packedProduct (lowerRows 335) packedUpper =
    packSparse (2 ^ 40) (targetRows 335) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 335) := by decide +kernel

theorem rowFacts335 : PackedRowFacts 335 := by
  constructor <;> decide +kernel

theorem upper336 : packedUpper 336 =
    packSparse (2 ^ 40) (upperRows 336) := by decide +kernel

theorem packed336 : packedProduct (lowerRows 336) packedUpper =
    packSparse (2 ^ 40) (targetRows 336) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 336) := by decide +kernel

theorem rowFacts336 : PackedRowFacts 336 := by
  constructor <;> decide +kernel

theorem upper337 : packedUpper 337 =
    packSparse (2 ^ 40) (upperRows 337) := by decide +kernel

theorem packed337 : packedProduct (lowerRows 337) packedUpper =
    packSparse (2 ^ 40) (targetRows 337) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 337) := by decide +kernel

theorem rowFacts337 : PackedRowFacts 337 := by
  constructor <;> decide +kernel

theorem upper338 : packedUpper 338 =
    packSparse (2 ^ 40) (upperRows 338) := by decide +kernel

theorem packed338 : packedProduct (lowerRows 338) packedUpper =
    packSparse (2 ^ 40) (targetRows 338) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 338) := by decide +kernel

theorem rowFacts338 : PackedRowFacts 338 := by
  constructor <;> decide +kernel

theorem upper339 : packedUpper 339 =
    packSparse (2 ^ 40) (upperRows 339) := by decide +kernel

theorem packed339 : packedProduct (lowerRows 339) packedUpper =
    packSparse (2 ^ 40) (targetRows 339) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 339) := by decide +kernel

theorem rowFacts339 : PackedRowFacts 339 := by
  constructor <;> decide +kernel

theorem upper340 : packedUpper 340 =
    packSparse (2 ^ 40) (upperRows 340) := by decide +kernel

theorem packed340 : packedProduct (lowerRows 340) packedUpper =
    packSparse (2 ^ 40) (targetRows 340) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 340) := by decide +kernel

theorem rowFacts340 : PackedRowFacts 340 := by
  constructor <;> decide +kernel

theorem upper341 : packedUpper 341 =
    packSparse (2 ^ 40) (upperRows 341) := by decide +kernel

theorem packed341 : packedProduct (lowerRows 341) packedUpper =
    packSparse (2 ^ 40) (targetRows 341) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 341) := by decide +kernel

theorem rowFacts341 : PackedRowFacts 341 := by
  constructor <;> decide +kernel

theorem upper342 : packedUpper 342 =
    packSparse (2 ^ 40) (upperRows 342) := by decide +kernel

theorem packed342 : packedProduct (lowerRows 342) packedUpper =
    packSparse (2 ^ 40) (targetRows 342) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 342) := by decide +kernel

theorem rowFacts342 : PackedRowFacts 342 := by
  constructor <;> decide +kernel

theorem upper343 : packedUpper 343 =
    packSparse (2 ^ 40) (upperRows 343) := by decide +kernel

theorem packed343 : packedProduct (lowerRows 343) packedUpper =
    packSparse (2 ^ 40) (targetRows 343) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 343) := by decide +kernel

theorem rowFacts343 : PackedRowFacts 343 := by
  constructor <;> decide +kernel

theorem upper344 : packedUpper 344 =
    packSparse (2 ^ 40) (upperRows 344) := by decide +kernel

theorem packed344 : packedProduct (lowerRows 344) packedUpper =
    packSparse (2 ^ 40) (targetRows 344) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 344) := by decide +kernel

theorem rowFacts344 : PackedRowFacts 344 := by
  constructor <;> decide +kernel

theorem upper345 : packedUpper 345 =
    packSparse (2 ^ 40) (upperRows 345) := by decide +kernel

theorem packed345 : packedProduct (lowerRows 345) packedUpper =
    packSparse (2 ^ 40) (targetRows 345) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 345) := by decide +kernel

theorem rowFacts345 : PackedRowFacts 345 := by
  constructor <;> decide +kernel

theorem upper346 : packedUpper 346 =
    packSparse (2 ^ 40) (upperRows 346) := by decide +kernel

theorem packed346 : packedProduct (lowerRows 346) packedUpper =
    packSparse (2 ^ 40) (targetRows 346) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 346) := by decide +kernel

theorem rowFacts346 : PackedRowFacts 346 := by
  constructor <;> decide +kernel

theorem upper347 : packedUpper 347 =
    packSparse (2 ^ 40) (upperRows 347) := by decide +kernel

theorem packed347 : packedProduct (lowerRows 347) packedUpper =
    packSparse (2 ^ 40) (targetRows 347) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 347) := by decide +kernel

theorem rowFacts347 : PackedRowFacts 347 := by
  constructor <;> decide +kernel

theorem upper348 : packedUpper 348 =
    packSparse (2 ^ 40) (upperRows 348) := by decide +kernel

theorem packed348 : packedProduct (lowerRows 348) packedUpper =
    packSparse (2 ^ 40) (targetRows 348) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 348) := by decide +kernel

theorem rowFacts348 : PackedRowFacts 348 := by
  constructor <;> decide +kernel

theorem upper349 : packedUpper 349 =
    packSparse (2 ^ 40) (upperRows 349) := by decide +kernel

theorem packed349 : packedProduct (lowerRows 349) packedUpper =
    packSparse (2 ^ 40) (targetRows 349) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 349) := by decide +kernel

theorem rowFacts349 : PackedRowFacts 349 := by
  constructor <;> decide +kernel

theorem upper350 : packedUpper 350 =
    packSparse (2 ^ 40) (upperRows 350) := by decide +kernel

theorem packed350 : packedProduct (lowerRows 350) packedUpper =
    packSparse (2 ^ 40) (targetRows 350) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 350) := by decide +kernel

theorem rowFacts350 : PackedRowFacts 350 := by
  constructor <;> decide +kernel

theorem upper351 : packedUpper 351 =
    packSparse (2 ^ 40) (upperRows 351) := by decide +kernel

theorem packed351 : packedProduct (lowerRows 351) packedUpper =
    packSparse (2 ^ 40) (targetRows 351) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 351) := by decide +kernel

theorem rowFacts351 : PackedRowFacts 351 := by
  constructor <;> decide +kernel

#print axioms packed351

end CertifiedRank.C2.PackedCertificate
