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

theorem upper512 : packedUpper 512 =
    packSparse (2 ^ 40) (upperRows 512) := by decide +kernel

theorem packed512 : packedProduct (lowerRows 512) packedUpper =
    packSparse (2 ^ 40) (targetRows 512) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 512) := by decide +kernel

theorem rowFacts512 : PackedRowFacts 512 := by
  constructor <;> decide +kernel

theorem upper513 : packedUpper 513 =
    packSparse (2 ^ 40) (upperRows 513) := by decide +kernel

theorem packed513 : packedProduct (lowerRows 513) packedUpper =
    packSparse (2 ^ 40) (targetRows 513) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 513) := by decide +kernel

theorem rowFacts513 : PackedRowFacts 513 := by
  constructor <;> decide +kernel

theorem upper514 : packedUpper 514 =
    packSparse (2 ^ 40) (upperRows 514) := by decide +kernel

theorem packed514 : packedProduct (lowerRows 514) packedUpper =
    packSparse (2 ^ 40) (targetRows 514) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 514) := by decide +kernel

theorem rowFacts514 : PackedRowFacts 514 := by
  constructor <;> decide +kernel

theorem upper515 : packedUpper 515 =
    packSparse (2 ^ 40) (upperRows 515) := by decide +kernel

theorem packed515 : packedProduct (lowerRows 515) packedUpper =
    packSparse (2 ^ 40) (targetRows 515) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 515) := by decide +kernel

theorem rowFacts515 : PackedRowFacts 515 := by
  constructor <;> decide +kernel

theorem upper516 : packedUpper 516 =
    packSparse (2 ^ 40) (upperRows 516) := by decide +kernel

theorem packed516 : packedProduct (lowerRows 516) packedUpper =
    packSparse (2 ^ 40) (targetRows 516) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 516) := by decide +kernel

theorem rowFacts516 : PackedRowFacts 516 := by
  constructor <;> decide +kernel

theorem upper517 : packedUpper 517 =
    packSparse (2 ^ 40) (upperRows 517) := by decide +kernel

theorem packed517 : packedProduct (lowerRows 517) packedUpper =
    packSparse (2 ^ 40) (targetRows 517) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 517) := by decide +kernel

theorem rowFacts517 : PackedRowFacts 517 := by
  constructor <;> decide +kernel

theorem upper518 : packedUpper 518 =
    packSparse (2 ^ 40) (upperRows 518) := by decide +kernel

theorem packed518 : packedProduct (lowerRows 518) packedUpper =
    packSparse (2 ^ 40) (targetRows 518) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 518) := by decide +kernel

theorem rowFacts518 : PackedRowFacts 518 := by
  constructor <;> decide +kernel

theorem upper519 : packedUpper 519 =
    packSparse (2 ^ 40) (upperRows 519) := by decide +kernel

theorem packed519 : packedProduct (lowerRows 519) packedUpper =
    packSparse (2 ^ 40) (targetRows 519) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 519) := by decide +kernel

theorem rowFacts519 : PackedRowFacts 519 := by
  constructor <;> decide +kernel

theorem upper520 : packedUpper 520 =
    packSparse (2 ^ 40) (upperRows 520) := by decide +kernel

theorem packed520 : packedProduct (lowerRows 520) packedUpper =
    packSparse (2 ^ 40) (targetRows 520) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 520) := by decide +kernel

theorem rowFacts520 : PackedRowFacts 520 := by
  constructor <;> decide +kernel

theorem upper521 : packedUpper 521 =
    packSparse (2 ^ 40) (upperRows 521) := by decide +kernel

theorem packed521 : packedProduct (lowerRows 521) packedUpper =
    packSparse (2 ^ 40) (targetRows 521) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 521) := by decide +kernel

theorem rowFacts521 : PackedRowFacts 521 := by
  constructor <;> decide +kernel

theorem upper522 : packedUpper 522 =
    packSparse (2 ^ 40) (upperRows 522) := by decide +kernel

theorem packed522 : packedProduct (lowerRows 522) packedUpper =
    packSparse (2 ^ 40) (targetRows 522) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 522) := by decide +kernel

theorem rowFacts522 : PackedRowFacts 522 := by
  constructor <;> decide +kernel

theorem upper523 : packedUpper 523 =
    packSparse (2 ^ 40) (upperRows 523) := by decide +kernel

theorem packed523 : packedProduct (lowerRows 523) packedUpper =
    packSparse (2 ^ 40) (targetRows 523) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 523) := by decide +kernel

theorem rowFacts523 : PackedRowFacts 523 := by
  constructor <;> decide +kernel

theorem upper524 : packedUpper 524 =
    packSparse (2 ^ 40) (upperRows 524) := by decide +kernel

theorem packed524 : packedProduct (lowerRows 524) packedUpper =
    packSparse (2 ^ 40) (targetRows 524) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 524) := by decide +kernel

theorem rowFacts524 : PackedRowFacts 524 := by
  constructor <;> decide +kernel

theorem upper525 : packedUpper 525 =
    packSparse (2 ^ 40) (upperRows 525) := by decide +kernel

theorem packed525 : packedProduct (lowerRows 525) packedUpper =
    packSparse (2 ^ 40) (targetRows 525) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 525) := by decide +kernel

theorem rowFacts525 : PackedRowFacts 525 := by
  constructor <;> decide +kernel

theorem upper526 : packedUpper 526 =
    packSparse (2 ^ 40) (upperRows 526) := by decide +kernel

theorem packed526 : packedProduct (lowerRows 526) packedUpper =
    packSparse (2 ^ 40) (targetRows 526) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 526) := by decide +kernel

theorem rowFacts526 : PackedRowFacts 526 := by
  constructor <;> decide +kernel

theorem upper527 : packedUpper 527 =
    packSparse (2 ^ 40) (upperRows 527) := by decide +kernel

theorem packed527 : packedProduct (lowerRows 527) packedUpper =
    packSparse (2 ^ 40) (targetRows 527) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 527) := by decide +kernel

theorem rowFacts527 : PackedRowFacts 527 := by
  constructor <;> decide +kernel

theorem upper528 : packedUpper 528 =
    packSparse (2 ^ 40) (upperRows 528) := by decide +kernel

theorem packed528 : packedProduct (lowerRows 528) packedUpper =
    packSparse (2 ^ 40) (targetRows 528) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 528) := by decide +kernel

theorem rowFacts528 : PackedRowFacts 528 := by
  constructor <;> decide +kernel

theorem upper529 : packedUpper 529 =
    packSparse (2 ^ 40) (upperRows 529) := by decide +kernel

theorem packed529 : packedProduct (lowerRows 529) packedUpper =
    packSparse (2 ^ 40) (targetRows 529) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 529) := by decide +kernel

theorem rowFacts529 : PackedRowFacts 529 := by
  constructor <;> decide +kernel

theorem upper530 : packedUpper 530 =
    packSparse (2 ^ 40) (upperRows 530) := by decide +kernel

theorem packed530 : packedProduct (lowerRows 530) packedUpper =
    packSparse (2 ^ 40) (targetRows 530) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 530) := by decide +kernel

theorem rowFacts530 : PackedRowFacts 530 := by
  constructor <;> decide +kernel

theorem upper531 : packedUpper 531 =
    packSparse (2 ^ 40) (upperRows 531) := by decide +kernel

theorem packed531 : packedProduct (lowerRows 531) packedUpper =
    packSparse (2 ^ 40) (targetRows 531) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 531) := by decide +kernel

theorem rowFacts531 : PackedRowFacts 531 := by
  constructor <;> decide +kernel

theorem upper532 : packedUpper 532 =
    packSparse (2 ^ 40) (upperRows 532) := by decide +kernel

theorem packed532 : packedProduct (lowerRows 532) packedUpper =
    packSparse (2 ^ 40) (targetRows 532) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 532) := by decide +kernel

theorem rowFacts532 : PackedRowFacts 532 := by
  constructor <;> decide +kernel

theorem upper533 : packedUpper 533 =
    packSparse (2 ^ 40) (upperRows 533) := by decide +kernel

theorem packed533 : packedProduct (lowerRows 533) packedUpper =
    packSparse (2 ^ 40) (targetRows 533) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 533) := by decide +kernel

theorem rowFacts533 : PackedRowFacts 533 := by
  constructor <;> decide +kernel

theorem upper534 : packedUpper 534 =
    packSparse (2 ^ 40) (upperRows 534) := by decide +kernel

theorem packed534 : packedProduct (lowerRows 534) packedUpper =
    packSparse (2 ^ 40) (targetRows 534) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 534) := by decide +kernel

theorem rowFacts534 : PackedRowFacts 534 := by
  constructor <;> decide +kernel

theorem upper535 : packedUpper 535 =
    packSparse (2 ^ 40) (upperRows 535) := by decide +kernel

theorem packed535 : packedProduct (lowerRows 535) packedUpper =
    packSparse (2 ^ 40) (targetRows 535) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 535) := by decide +kernel

theorem rowFacts535 : PackedRowFacts 535 := by
  constructor <;> decide +kernel

theorem upper536 : packedUpper 536 =
    packSparse (2 ^ 40) (upperRows 536) := by decide +kernel

theorem packed536 : packedProduct (lowerRows 536) packedUpper =
    packSparse (2 ^ 40) (targetRows 536) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 536) := by decide +kernel

theorem rowFacts536 : PackedRowFacts 536 := by
  constructor <;> decide +kernel

theorem upper537 : packedUpper 537 =
    packSparse (2 ^ 40) (upperRows 537) := by decide +kernel

theorem packed537 : packedProduct (lowerRows 537) packedUpper =
    packSparse (2 ^ 40) (targetRows 537) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 537) := by decide +kernel

theorem rowFacts537 : PackedRowFacts 537 := by
  constructor <;> decide +kernel

theorem upper538 : packedUpper 538 =
    packSparse (2 ^ 40) (upperRows 538) := by decide +kernel

theorem packed538 : packedProduct (lowerRows 538) packedUpper =
    packSparse (2 ^ 40) (targetRows 538) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 538) := by decide +kernel

theorem rowFacts538 : PackedRowFacts 538 := by
  constructor <;> decide +kernel

theorem upper539 : packedUpper 539 =
    packSparse (2 ^ 40) (upperRows 539) := by decide +kernel

theorem packed539 : packedProduct (lowerRows 539) packedUpper =
    packSparse (2 ^ 40) (targetRows 539) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 539) := by decide +kernel

theorem rowFacts539 : PackedRowFacts 539 := by
  constructor <;> decide +kernel

theorem upper540 : packedUpper 540 =
    packSparse (2 ^ 40) (upperRows 540) := by decide +kernel

theorem packed540 : packedProduct (lowerRows 540) packedUpper =
    packSparse (2 ^ 40) (targetRows 540) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 540) := by decide +kernel

theorem rowFacts540 : PackedRowFacts 540 := by
  constructor <;> decide +kernel

theorem upper541 : packedUpper 541 =
    packSparse (2 ^ 40) (upperRows 541) := by decide +kernel

theorem packed541 : packedProduct (lowerRows 541) packedUpper =
    packSparse (2 ^ 40) (targetRows 541) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 541) := by decide +kernel

theorem rowFacts541 : PackedRowFacts 541 := by
  constructor <;> decide +kernel

#print axioms packed541

end CertifiedRank.C2.PackedCertificate
