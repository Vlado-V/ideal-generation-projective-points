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

theorem upper480 : packedUpper 480 =
    packSparse (2 ^ 40) (upperRows 480) := by decide +kernel

theorem packed480 : packedProduct (lowerRows 480) packedUpper =
    packSparse (2 ^ 40) (targetRows 480) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 480) := by decide +kernel

theorem rowFacts480 : PackedRowFacts 480 := by
  constructor <;> decide +kernel

theorem upper481 : packedUpper 481 =
    packSparse (2 ^ 40) (upperRows 481) := by decide +kernel

theorem packed481 : packedProduct (lowerRows 481) packedUpper =
    packSparse (2 ^ 40) (targetRows 481) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 481) := by decide +kernel

theorem rowFacts481 : PackedRowFacts 481 := by
  constructor <;> decide +kernel

theorem upper482 : packedUpper 482 =
    packSparse (2 ^ 40) (upperRows 482) := by decide +kernel

theorem packed482 : packedProduct (lowerRows 482) packedUpper =
    packSparse (2 ^ 40) (targetRows 482) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 482) := by decide +kernel

theorem rowFacts482 : PackedRowFacts 482 := by
  constructor <;> decide +kernel

theorem upper483 : packedUpper 483 =
    packSparse (2 ^ 40) (upperRows 483) := by decide +kernel

theorem packed483 : packedProduct (lowerRows 483) packedUpper =
    packSparse (2 ^ 40) (targetRows 483) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 483) := by decide +kernel

theorem rowFacts483 : PackedRowFacts 483 := by
  constructor <;> decide +kernel

theorem upper484 : packedUpper 484 =
    packSparse (2 ^ 40) (upperRows 484) := by decide +kernel

theorem packed484 : packedProduct (lowerRows 484) packedUpper =
    packSparse (2 ^ 40) (targetRows 484) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 484) := by decide +kernel

theorem rowFacts484 : PackedRowFacts 484 := by
  constructor <;> decide +kernel

theorem upper485 : packedUpper 485 =
    packSparse (2 ^ 40) (upperRows 485) := by decide +kernel

theorem packed485 : packedProduct (lowerRows 485) packedUpper =
    packSparse (2 ^ 40) (targetRows 485) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 485) := by decide +kernel

theorem rowFacts485 : PackedRowFacts 485 := by
  constructor <;> decide +kernel

theorem upper486 : packedUpper 486 =
    packSparse (2 ^ 40) (upperRows 486) := by decide +kernel

theorem packed486 : packedProduct (lowerRows 486) packedUpper =
    packSparse (2 ^ 40) (targetRows 486) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 486) := by decide +kernel

theorem rowFacts486 : PackedRowFacts 486 := by
  constructor <;> decide +kernel

theorem upper487 : packedUpper 487 =
    packSparse (2 ^ 40) (upperRows 487) := by decide +kernel

theorem packed487 : packedProduct (lowerRows 487) packedUpper =
    packSparse (2 ^ 40) (targetRows 487) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 487) := by decide +kernel

theorem rowFacts487 : PackedRowFacts 487 := by
  constructor <;> decide +kernel

theorem upper488 : packedUpper 488 =
    packSparse (2 ^ 40) (upperRows 488) := by decide +kernel

theorem packed488 : packedProduct (lowerRows 488) packedUpper =
    packSparse (2 ^ 40) (targetRows 488) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 488) := by decide +kernel

theorem rowFacts488 : PackedRowFacts 488 := by
  constructor <;> decide +kernel

theorem upper489 : packedUpper 489 =
    packSparse (2 ^ 40) (upperRows 489) := by decide +kernel

theorem packed489 : packedProduct (lowerRows 489) packedUpper =
    packSparse (2 ^ 40) (targetRows 489) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 489) := by decide +kernel

theorem rowFacts489 : PackedRowFacts 489 := by
  constructor <;> decide +kernel

theorem upper490 : packedUpper 490 =
    packSparse (2 ^ 40) (upperRows 490) := by decide +kernel

theorem packed490 : packedProduct (lowerRows 490) packedUpper =
    packSparse (2 ^ 40) (targetRows 490) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 490) := by decide +kernel

theorem rowFacts490 : PackedRowFacts 490 := by
  constructor <;> decide +kernel

theorem upper491 : packedUpper 491 =
    packSparse (2 ^ 40) (upperRows 491) := by decide +kernel

theorem packed491 : packedProduct (lowerRows 491) packedUpper =
    packSparse (2 ^ 40) (targetRows 491) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 491) := by decide +kernel

theorem rowFacts491 : PackedRowFacts 491 := by
  constructor <;> decide +kernel

theorem upper492 : packedUpper 492 =
    packSparse (2 ^ 40) (upperRows 492) := by decide +kernel

theorem packed492 : packedProduct (lowerRows 492) packedUpper =
    packSparse (2 ^ 40) (targetRows 492) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 492) := by decide +kernel

theorem rowFacts492 : PackedRowFacts 492 := by
  constructor <;> decide +kernel

theorem upper493 : packedUpper 493 =
    packSparse (2 ^ 40) (upperRows 493) := by decide +kernel

theorem packed493 : packedProduct (lowerRows 493) packedUpper =
    packSparse (2 ^ 40) (targetRows 493) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 493) := by decide +kernel

theorem rowFacts493 : PackedRowFacts 493 := by
  constructor <;> decide +kernel

theorem upper494 : packedUpper 494 =
    packSparse (2 ^ 40) (upperRows 494) := by decide +kernel

theorem packed494 : packedProduct (lowerRows 494) packedUpper =
    packSparse (2 ^ 40) (targetRows 494) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 494) := by decide +kernel

theorem rowFacts494 : PackedRowFacts 494 := by
  constructor <;> decide +kernel

theorem upper495 : packedUpper 495 =
    packSparse (2 ^ 40) (upperRows 495) := by decide +kernel

theorem packed495 : packedProduct (lowerRows 495) packedUpper =
    packSparse (2 ^ 40) (targetRows 495) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 495) := by decide +kernel

theorem rowFacts495 : PackedRowFacts 495 := by
  constructor <;> decide +kernel

theorem upper496 : packedUpper 496 =
    packSparse (2 ^ 40) (upperRows 496) := by decide +kernel

theorem packed496 : packedProduct (lowerRows 496) packedUpper =
    packSparse (2 ^ 40) (targetRows 496) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 496) := by decide +kernel

theorem rowFacts496 : PackedRowFacts 496 := by
  constructor <;> decide +kernel

theorem upper497 : packedUpper 497 =
    packSparse (2 ^ 40) (upperRows 497) := by decide +kernel

theorem packed497 : packedProduct (lowerRows 497) packedUpper =
    packSparse (2 ^ 40) (targetRows 497) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 497) := by decide +kernel

theorem rowFacts497 : PackedRowFacts 497 := by
  constructor <;> decide +kernel

theorem upper498 : packedUpper 498 =
    packSparse (2 ^ 40) (upperRows 498) := by decide +kernel

theorem packed498 : packedProduct (lowerRows 498) packedUpper =
    packSparse (2 ^ 40) (targetRows 498) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 498) := by decide +kernel

theorem rowFacts498 : PackedRowFacts 498 := by
  constructor <;> decide +kernel

theorem upper499 : packedUpper 499 =
    packSparse (2 ^ 40) (upperRows 499) := by decide +kernel

theorem packed499 : packedProduct (lowerRows 499) packedUpper =
    packSparse (2 ^ 40) (targetRows 499) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 499) := by decide +kernel

theorem rowFacts499 : PackedRowFacts 499 := by
  constructor <;> decide +kernel

theorem upper500 : packedUpper 500 =
    packSparse (2 ^ 40) (upperRows 500) := by decide +kernel

theorem packed500 : packedProduct (lowerRows 500) packedUpper =
    packSparse (2 ^ 40) (targetRows 500) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 500) := by decide +kernel

theorem rowFacts500 : PackedRowFacts 500 := by
  constructor <;> decide +kernel

theorem upper501 : packedUpper 501 =
    packSparse (2 ^ 40) (upperRows 501) := by decide +kernel

theorem packed501 : packedProduct (lowerRows 501) packedUpper =
    packSparse (2 ^ 40) (targetRows 501) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 501) := by decide +kernel

theorem rowFacts501 : PackedRowFacts 501 := by
  constructor <;> decide +kernel

theorem upper502 : packedUpper 502 =
    packSparse (2 ^ 40) (upperRows 502) := by decide +kernel

theorem packed502 : packedProduct (lowerRows 502) packedUpper =
    packSparse (2 ^ 40) (targetRows 502) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 502) := by decide +kernel

theorem rowFacts502 : PackedRowFacts 502 := by
  constructor <;> decide +kernel

theorem upper503 : packedUpper 503 =
    packSparse (2 ^ 40) (upperRows 503) := by decide +kernel

theorem packed503 : packedProduct (lowerRows 503) packedUpper =
    packSparse (2 ^ 40) (targetRows 503) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 503) := by decide +kernel

theorem rowFacts503 : PackedRowFacts 503 := by
  constructor <;> decide +kernel

theorem upper504 : packedUpper 504 =
    packSparse (2 ^ 40) (upperRows 504) := by decide +kernel

theorem packed504 : packedProduct (lowerRows 504) packedUpper =
    packSparse (2 ^ 40) (targetRows 504) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 504) := by decide +kernel

theorem rowFacts504 : PackedRowFacts 504 := by
  constructor <;> decide +kernel

theorem upper505 : packedUpper 505 =
    packSparse (2 ^ 40) (upperRows 505) := by decide +kernel

theorem packed505 : packedProduct (lowerRows 505) packedUpper =
    packSparse (2 ^ 40) (targetRows 505) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 505) := by decide +kernel

theorem rowFacts505 : PackedRowFacts 505 := by
  constructor <;> decide +kernel

theorem upper506 : packedUpper 506 =
    packSparse (2 ^ 40) (upperRows 506) := by decide +kernel

theorem packed506 : packedProduct (lowerRows 506) packedUpper =
    packSparse (2 ^ 40) (targetRows 506) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 506) := by decide +kernel

theorem rowFacts506 : PackedRowFacts 506 := by
  constructor <;> decide +kernel

theorem upper507 : packedUpper 507 =
    packSparse (2 ^ 40) (upperRows 507) := by decide +kernel

theorem packed507 : packedProduct (lowerRows 507) packedUpper =
    packSparse (2 ^ 40) (targetRows 507) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 507) := by decide +kernel

theorem rowFacts507 : PackedRowFacts 507 := by
  constructor <;> decide +kernel

theorem upper508 : packedUpper 508 =
    packSparse (2 ^ 40) (upperRows 508) := by decide +kernel

theorem packed508 : packedProduct (lowerRows 508) packedUpper =
    packSparse (2 ^ 40) (targetRows 508) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 508) := by decide +kernel

theorem rowFacts508 : PackedRowFacts 508 := by
  constructor <;> decide +kernel

theorem upper509 : packedUpper 509 =
    packSparse (2 ^ 40) (upperRows 509) := by decide +kernel

theorem packed509 : packedProduct (lowerRows 509) packedUpper =
    packSparse (2 ^ 40) (targetRows 509) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 509) := by decide +kernel

theorem rowFacts509 : PackedRowFacts 509 := by
  constructor <;> decide +kernel

theorem upper510 : packedUpper 510 =
    packSparse (2 ^ 40) (upperRows 510) := by decide +kernel

theorem packed510 : packedProduct (lowerRows 510) packedUpper =
    packSparse (2 ^ 40) (targetRows 510) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 510) := by decide +kernel

theorem rowFacts510 : PackedRowFacts 510 := by
  constructor <;> decide +kernel

theorem upper511 : packedUpper 511 =
    packSparse (2 ^ 40) (upperRows 511) := by decide +kernel

theorem packed511 : packedProduct (lowerRows 511) packedUpper =
    packSparse (2 ^ 40) (targetRows 511) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 511) := by decide +kernel

theorem rowFacts511 : PackedRowFacts 511 := by
  constructor <;> decide +kernel

#print axioms packed511

end CertifiedRank.C2.PackedCertificate
