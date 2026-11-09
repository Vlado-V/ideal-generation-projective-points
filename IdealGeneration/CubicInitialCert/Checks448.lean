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

theorem upper448 : packedUpper 448 =
    packSparse (2 ^ 40) (upperRows 448) := by decide +kernel

theorem packed448 : packedProduct (lowerRows 448) packedUpper =
    packSparse (2 ^ 40) (targetRows 448) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 448) := by decide +kernel

theorem rowFacts448 : PackedRowFacts 448 := by
  constructor <;> decide +kernel

theorem upper449 : packedUpper 449 =
    packSparse (2 ^ 40) (upperRows 449) := by decide +kernel

theorem packed449 : packedProduct (lowerRows 449) packedUpper =
    packSparse (2 ^ 40) (targetRows 449) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 449) := by decide +kernel

theorem rowFacts449 : PackedRowFacts 449 := by
  constructor <;> decide +kernel

theorem upper450 : packedUpper 450 =
    packSparse (2 ^ 40) (upperRows 450) := by decide +kernel

theorem packed450 : packedProduct (lowerRows 450) packedUpper =
    packSparse (2 ^ 40) (targetRows 450) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 450) := by decide +kernel

theorem rowFacts450 : PackedRowFacts 450 := by
  constructor <;> decide +kernel

theorem upper451 : packedUpper 451 =
    packSparse (2 ^ 40) (upperRows 451) := by decide +kernel

theorem packed451 : packedProduct (lowerRows 451) packedUpper =
    packSparse (2 ^ 40) (targetRows 451) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 451) := by decide +kernel

theorem rowFacts451 : PackedRowFacts 451 := by
  constructor <;> decide +kernel

theorem upper452 : packedUpper 452 =
    packSparse (2 ^ 40) (upperRows 452) := by decide +kernel

theorem packed452 : packedProduct (lowerRows 452) packedUpper =
    packSparse (2 ^ 40) (targetRows 452) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 452) := by decide +kernel

theorem rowFacts452 : PackedRowFacts 452 := by
  constructor <;> decide +kernel

theorem upper453 : packedUpper 453 =
    packSparse (2 ^ 40) (upperRows 453) := by decide +kernel

theorem packed453 : packedProduct (lowerRows 453) packedUpper =
    packSparse (2 ^ 40) (targetRows 453) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 453) := by decide +kernel

theorem rowFacts453 : PackedRowFacts 453 := by
  constructor <;> decide +kernel

theorem upper454 : packedUpper 454 =
    packSparse (2 ^ 40) (upperRows 454) := by decide +kernel

theorem packed454 : packedProduct (lowerRows 454) packedUpper =
    packSparse (2 ^ 40) (targetRows 454) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 454) := by decide +kernel

theorem rowFacts454 : PackedRowFacts 454 := by
  constructor <;> decide +kernel

theorem upper455 : packedUpper 455 =
    packSparse (2 ^ 40) (upperRows 455) := by decide +kernel

theorem packed455 : packedProduct (lowerRows 455) packedUpper =
    packSparse (2 ^ 40) (targetRows 455) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 455) := by decide +kernel

theorem rowFacts455 : PackedRowFacts 455 := by
  constructor <;> decide +kernel

theorem upper456 : packedUpper 456 =
    packSparse (2 ^ 40) (upperRows 456) := by decide +kernel

theorem packed456 : packedProduct (lowerRows 456) packedUpper =
    packSparse (2 ^ 40) (targetRows 456) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 456) := by decide +kernel

theorem rowFacts456 : PackedRowFacts 456 := by
  constructor <;> decide +kernel

theorem upper457 : packedUpper 457 =
    packSparse (2 ^ 40) (upperRows 457) := by decide +kernel

theorem packed457 : packedProduct (lowerRows 457) packedUpper =
    packSparse (2 ^ 40) (targetRows 457) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 457) := by decide +kernel

theorem rowFacts457 : PackedRowFacts 457 := by
  constructor <;> decide +kernel

theorem upper458 : packedUpper 458 =
    packSparse (2 ^ 40) (upperRows 458) := by decide +kernel

theorem packed458 : packedProduct (lowerRows 458) packedUpper =
    packSparse (2 ^ 40) (targetRows 458) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 458) := by decide +kernel

theorem rowFacts458 : PackedRowFacts 458 := by
  constructor <;> decide +kernel

theorem upper459 : packedUpper 459 =
    packSparse (2 ^ 40) (upperRows 459) := by decide +kernel

theorem packed459 : packedProduct (lowerRows 459) packedUpper =
    packSparse (2 ^ 40) (targetRows 459) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 459) := by decide +kernel

theorem rowFacts459 : PackedRowFacts 459 := by
  constructor <;> decide +kernel

theorem upper460 : packedUpper 460 =
    packSparse (2 ^ 40) (upperRows 460) := by decide +kernel

theorem packed460 : packedProduct (lowerRows 460) packedUpper =
    packSparse (2 ^ 40) (targetRows 460) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 460) := by decide +kernel

theorem rowFacts460 : PackedRowFacts 460 := by
  constructor <;> decide +kernel

theorem upper461 : packedUpper 461 =
    packSparse (2 ^ 40) (upperRows 461) := by decide +kernel

theorem packed461 : packedProduct (lowerRows 461) packedUpper =
    packSparse (2 ^ 40) (targetRows 461) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 461) := by decide +kernel

theorem rowFacts461 : PackedRowFacts 461 := by
  constructor <;> decide +kernel

theorem upper462 : packedUpper 462 =
    packSparse (2 ^ 40) (upperRows 462) := by decide +kernel

theorem packed462 : packedProduct (lowerRows 462) packedUpper =
    packSparse (2 ^ 40) (targetRows 462) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 462) := by decide +kernel

theorem rowFacts462 : PackedRowFacts 462 := by
  constructor <;> decide +kernel

theorem upper463 : packedUpper 463 =
    packSparse (2 ^ 40) (upperRows 463) := by decide +kernel

theorem packed463 : packedProduct (lowerRows 463) packedUpper =
    packSparse (2 ^ 40) (targetRows 463) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 463) := by decide +kernel

theorem rowFacts463 : PackedRowFacts 463 := by
  constructor <;> decide +kernel

theorem upper464 : packedUpper 464 =
    packSparse (2 ^ 40) (upperRows 464) := by decide +kernel

theorem packed464 : packedProduct (lowerRows 464) packedUpper =
    packSparse (2 ^ 40) (targetRows 464) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 464) := by decide +kernel

theorem rowFacts464 : PackedRowFacts 464 := by
  constructor <;> decide +kernel

theorem upper465 : packedUpper 465 =
    packSparse (2 ^ 40) (upperRows 465) := by decide +kernel

theorem packed465 : packedProduct (lowerRows 465) packedUpper =
    packSparse (2 ^ 40) (targetRows 465) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 465) := by decide +kernel

theorem rowFacts465 : PackedRowFacts 465 := by
  constructor <;> decide +kernel

theorem upper466 : packedUpper 466 =
    packSparse (2 ^ 40) (upperRows 466) := by decide +kernel

theorem packed466 : packedProduct (lowerRows 466) packedUpper =
    packSparse (2 ^ 40) (targetRows 466) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 466) := by decide +kernel

theorem rowFacts466 : PackedRowFacts 466 := by
  constructor <;> decide +kernel

theorem upper467 : packedUpper 467 =
    packSparse (2 ^ 40) (upperRows 467) := by decide +kernel

theorem packed467 : packedProduct (lowerRows 467) packedUpper =
    packSparse (2 ^ 40) (targetRows 467) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 467) := by decide +kernel

theorem rowFacts467 : PackedRowFacts 467 := by
  constructor <;> decide +kernel

theorem upper468 : packedUpper 468 =
    packSparse (2 ^ 40) (upperRows 468) := by decide +kernel

theorem packed468 : packedProduct (lowerRows 468) packedUpper =
    packSparse (2 ^ 40) (targetRows 468) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 468) := by decide +kernel

theorem rowFacts468 : PackedRowFacts 468 := by
  constructor <;> decide +kernel

theorem upper469 : packedUpper 469 =
    packSparse (2 ^ 40) (upperRows 469) := by decide +kernel

theorem packed469 : packedProduct (lowerRows 469) packedUpper =
    packSparse (2 ^ 40) (targetRows 469) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 469) := by decide +kernel

theorem rowFacts469 : PackedRowFacts 469 := by
  constructor <;> decide +kernel

theorem upper470 : packedUpper 470 =
    packSparse (2 ^ 40) (upperRows 470) := by decide +kernel

theorem packed470 : packedProduct (lowerRows 470) packedUpper =
    packSparse (2 ^ 40) (targetRows 470) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 470) := by decide +kernel

theorem rowFacts470 : PackedRowFacts 470 := by
  constructor <;> decide +kernel

theorem upper471 : packedUpper 471 =
    packSparse (2 ^ 40) (upperRows 471) := by decide +kernel

theorem packed471 : packedProduct (lowerRows 471) packedUpper =
    packSparse (2 ^ 40) (targetRows 471) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 471) := by decide +kernel

theorem rowFacts471 : PackedRowFacts 471 := by
  constructor <;> decide +kernel

theorem upper472 : packedUpper 472 =
    packSparse (2 ^ 40) (upperRows 472) := by decide +kernel

theorem packed472 : packedProduct (lowerRows 472) packedUpper =
    packSparse (2 ^ 40) (targetRows 472) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 472) := by decide +kernel

theorem rowFacts472 : PackedRowFacts 472 := by
  constructor <;> decide +kernel

theorem upper473 : packedUpper 473 =
    packSparse (2 ^ 40) (upperRows 473) := by decide +kernel

theorem packed473 : packedProduct (lowerRows 473) packedUpper =
    packSparse (2 ^ 40) (targetRows 473) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 473) := by decide +kernel

theorem rowFacts473 : PackedRowFacts 473 := by
  constructor <;> decide +kernel

theorem upper474 : packedUpper 474 =
    packSparse (2 ^ 40) (upperRows 474) := by decide +kernel

theorem packed474 : packedProduct (lowerRows 474) packedUpper =
    packSparse (2 ^ 40) (targetRows 474) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 474) := by decide +kernel

theorem rowFacts474 : PackedRowFacts 474 := by
  constructor <;> decide +kernel

theorem upper475 : packedUpper 475 =
    packSparse (2 ^ 40) (upperRows 475) := by decide +kernel

theorem packed475 : packedProduct (lowerRows 475) packedUpper =
    packSparse (2 ^ 40) (targetRows 475) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 475) := by decide +kernel

theorem rowFacts475 : PackedRowFacts 475 := by
  constructor <;> decide +kernel

theorem upper476 : packedUpper 476 =
    packSparse (2 ^ 40) (upperRows 476) := by decide +kernel

theorem packed476 : packedProduct (lowerRows 476) packedUpper =
    packSparse (2 ^ 40) (targetRows 476) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 476) := by decide +kernel

theorem rowFacts476 : PackedRowFacts 476 := by
  constructor <;> decide +kernel

theorem upper477 : packedUpper 477 =
    packSparse (2 ^ 40) (upperRows 477) := by decide +kernel

theorem packed477 : packedProduct (lowerRows 477) packedUpper =
    packSparse (2 ^ 40) (targetRows 477) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 477) := by decide +kernel

theorem rowFacts477 : PackedRowFacts 477 := by
  constructor <;> decide +kernel

theorem upper478 : packedUpper 478 =
    packSparse (2 ^ 40) (upperRows 478) := by decide +kernel

theorem packed478 : packedProduct (lowerRows 478) packedUpper =
    packSparse (2 ^ 40) (targetRows 478) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 478) := by decide +kernel

theorem rowFacts478 : PackedRowFacts 478 := by
  constructor <;> decide +kernel

theorem upper479 : packedUpper 479 =
    packSparse (2 ^ 40) (upperRows 479) := by decide +kernel

theorem packed479 : packedProduct (lowerRows 479) packedUpper =
    packSparse (2 ^ 40) (targetRows 479) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 479) := by decide +kernel

theorem rowFacts479 : PackedRowFacts 479 := by
  constructor <;> decide +kernel

#print axioms packed479

end CertifiedRank.C2.PackedCertificate
