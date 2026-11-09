module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 480–571 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_480 :
    twelvePackedRows 480 = packedMinorResidueRow twelveMinor 2 1024 480 := by rfl

theorem twelve_packed_product_480 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 480) twelvePackedRows =
      1024 ^ (480 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 480) := by rfl

theorem twelve_packed_row_481 :
    twelvePackedRows 481 = packedMinorResidueRow twelveMinor 2 1024 481 := by rfl

theorem twelve_packed_product_481 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 481) twelvePackedRows =
      1024 ^ (481 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 481) := by rfl

theorem twelve_packed_row_482 :
    twelvePackedRows 482 = packedMinorResidueRow twelveMinor 2 1024 482 := by rfl

theorem twelve_packed_product_482 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 482) twelvePackedRows =
      1024 ^ (482 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 482) := by rfl

theorem twelve_packed_row_483 :
    twelvePackedRows 483 = packedMinorResidueRow twelveMinor 2 1024 483 := by rfl

theorem twelve_packed_product_483 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 483) twelvePackedRows =
      1024 ^ (483 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 483) := by rfl

theorem twelve_packed_row_484 :
    twelvePackedRows 484 = packedMinorResidueRow twelveMinor 2 1024 484 := by rfl

theorem twelve_packed_product_484 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 484) twelvePackedRows =
      1024 ^ (484 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 484) := by rfl

theorem twelve_packed_row_485 :
    twelvePackedRows 485 = packedMinorResidueRow twelveMinor 2 1024 485 := by rfl

theorem twelve_packed_product_485 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 485) twelvePackedRows =
      1024 ^ (485 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 485) := by rfl

theorem twelve_packed_row_486 :
    twelvePackedRows 486 = packedMinorResidueRow twelveMinor 2 1024 486 := by rfl

theorem twelve_packed_product_486 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 486) twelvePackedRows =
      1024 ^ (486 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 486) := by rfl

theorem twelve_packed_row_487 :
    twelvePackedRows 487 = packedMinorResidueRow twelveMinor 2 1024 487 := by rfl

theorem twelve_packed_product_487 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 487) twelvePackedRows =
      1024 ^ (487 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 487) := by rfl

theorem twelve_packed_row_488 :
    twelvePackedRows 488 = packedMinorResidueRow twelveMinor 2 1024 488 := by rfl

theorem twelve_packed_product_488 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 488) twelvePackedRows =
      1024 ^ (488 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 488) := by rfl

theorem twelve_packed_row_489 :
    twelvePackedRows 489 = packedMinorResidueRow twelveMinor 2 1024 489 := by rfl

theorem twelve_packed_product_489 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 489) twelvePackedRows =
      1024 ^ (489 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 489) := by rfl

theorem twelve_packed_row_490 :
    twelvePackedRows 490 = packedMinorResidueRow twelveMinor 2 1024 490 := by rfl

theorem twelve_packed_product_490 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 490) twelvePackedRows =
      1024 ^ (490 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 490) := by rfl

theorem twelve_packed_row_491 :
    twelvePackedRows 491 = packedMinorResidueRow twelveMinor 2 1024 491 := by rfl

theorem twelve_packed_product_491 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 491) twelvePackedRows =
      1024 ^ (491 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 491) := by rfl

theorem twelve_packed_row_492 :
    twelvePackedRows 492 = packedMinorResidueRow twelveMinor 2 1024 492 := by rfl

theorem twelve_packed_product_492 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 492) twelvePackedRows =
      1024 ^ (492 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 492) := by rfl

theorem twelve_packed_row_493 :
    twelvePackedRows 493 = packedMinorResidueRow twelveMinor 2 1024 493 := by rfl

theorem twelve_packed_product_493 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 493) twelvePackedRows =
      1024 ^ (493 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 493) := by rfl

theorem twelve_packed_row_494 :
    twelvePackedRows 494 = packedMinorResidueRow twelveMinor 2 1024 494 := by rfl

theorem twelve_packed_product_494 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 494) twelvePackedRows =
      1024 ^ (494 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 494) := by rfl

theorem twelve_packed_row_495 :
    twelvePackedRows 495 = packedMinorResidueRow twelveMinor 2 1024 495 := by rfl

theorem twelve_packed_product_495 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 495) twelvePackedRows =
      1024 ^ (495 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 495) := by rfl

theorem twelve_packed_row_496 :
    twelvePackedRows 496 = packedMinorResidueRow twelveMinor 2 1024 496 := by rfl

theorem twelve_packed_product_496 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 496) twelvePackedRows =
      1024 ^ (496 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 496) := by rfl

theorem twelve_packed_row_497 :
    twelvePackedRows 497 = packedMinorResidueRow twelveMinor 2 1024 497 := by rfl

theorem twelve_packed_product_497 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 497) twelvePackedRows =
      1024 ^ (497 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 497) := by rfl

theorem twelve_packed_row_498 :
    twelvePackedRows 498 = packedMinorResidueRow twelveMinor 2 1024 498 := by rfl

theorem twelve_packed_product_498 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 498) twelvePackedRows =
      1024 ^ (498 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 498) := by rfl

theorem twelve_packed_row_499 :
    twelvePackedRows 499 = packedMinorResidueRow twelveMinor 2 1024 499 := by rfl

theorem twelve_packed_product_499 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 499) twelvePackedRows =
      1024 ^ (499 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 499) := by rfl

theorem twelve_packed_row_500 :
    twelvePackedRows 500 = packedMinorResidueRow twelveMinor 2 1024 500 := by rfl

theorem twelve_packed_product_500 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 500) twelvePackedRows =
      1024 ^ (500 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 500) := by rfl

theorem twelve_packed_row_501 :
    twelvePackedRows 501 = packedMinorResidueRow twelveMinor 2 1024 501 := by rfl

theorem twelve_packed_product_501 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 501) twelvePackedRows =
      1024 ^ (501 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 501) := by rfl

theorem twelve_packed_row_502 :
    twelvePackedRows 502 = packedMinorResidueRow twelveMinor 2 1024 502 := by rfl

theorem twelve_packed_product_502 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 502) twelvePackedRows =
      1024 ^ (502 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 502) := by rfl

theorem twelve_packed_row_503 :
    twelvePackedRows 503 = packedMinorResidueRow twelveMinor 2 1024 503 := by rfl

theorem twelve_packed_product_503 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 503) twelvePackedRows =
      1024 ^ (503 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 503) := by rfl

theorem twelve_packed_row_504 :
    twelvePackedRows 504 = packedMinorResidueRow twelveMinor 2 1024 504 := by rfl

theorem twelve_packed_product_504 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 504) twelvePackedRows =
      1024 ^ (504 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 504) := by rfl

theorem twelve_packed_row_505 :
    twelvePackedRows 505 = packedMinorResidueRow twelveMinor 2 1024 505 := by rfl

theorem twelve_packed_product_505 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 505) twelvePackedRows =
      1024 ^ (505 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 505) := by rfl

theorem twelve_packed_row_506 :
    twelvePackedRows 506 = packedMinorResidueRow twelveMinor 2 1024 506 := by rfl

theorem twelve_packed_product_506 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 506) twelvePackedRows =
      1024 ^ (506 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 506) := by rfl

theorem twelve_packed_row_507 :
    twelvePackedRows 507 = packedMinorResidueRow twelveMinor 2 1024 507 := by rfl

theorem twelve_packed_product_507 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 507) twelvePackedRows =
      1024 ^ (507 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 507) := by rfl

theorem twelve_packed_row_508 :
    twelvePackedRows 508 = packedMinorResidueRow twelveMinor 2 1024 508 := by rfl

theorem twelve_packed_product_508 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 508) twelvePackedRows =
      1024 ^ (508 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 508) := by rfl

theorem twelve_packed_row_509 :
    twelvePackedRows 509 = packedMinorResidueRow twelveMinor 2 1024 509 := by rfl

theorem twelve_packed_product_509 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 509) twelvePackedRows =
      1024 ^ (509 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 509) := by rfl

theorem twelve_packed_row_510 :
    twelvePackedRows 510 = packedMinorResidueRow twelveMinor 2 1024 510 := by rfl

theorem twelve_packed_product_510 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 510) twelvePackedRows =
      1024 ^ (510 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 510) := by rfl

theorem twelve_packed_row_511 :
    twelvePackedRows 511 = packedMinorResidueRow twelveMinor 2 1024 511 := by rfl

theorem twelve_packed_product_511 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 511) twelvePackedRows =
      1024 ^ (511 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 511) := by rfl

theorem twelve_packed_row_512 :
    twelvePackedRows 512 = packedMinorResidueRow twelveMinor 2 1024 512 := by rfl

theorem twelve_packed_product_512 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 512) twelvePackedRows =
      1024 ^ (512 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 512) := by rfl

theorem twelve_packed_row_513 :
    twelvePackedRows 513 = packedMinorResidueRow twelveMinor 2 1024 513 := by rfl

theorem twelve_packed_product_513 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 513) twelvePackedRows =
      1024 ^ (513 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 513) := by rfl

theorem twelve_packed_row_514 :
    twelvePackedRows 514 = packedMinorResidueRow twelveMinor 2 1024 514 := by rfl

theorem twelve_packed_product_514 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 514) twelvePackedRows =
      1024 ^ (514 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 514) := by rfl

theorem twelve_packed_row_515 :
    twelvePackedRows 515 = packedMinorResidueRow twelveMinor 2 1024 515 := by rfl

theorem twelve_packed_product_515 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 515) twelvePackedRows =
      1024 ^ (515 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 515) := by rfl

theorem twelve_packed_row_516 :
    twelvePackedRows 516 = packedMinorResidueRow twelveMinor 2 1024 516 := by rfl

theorem twelve_packed_product_516 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 516) twelvePackedRows =
      1024 ^ (516 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 516) := by rfl

theorem twelve_packed_row_517 :
    twelvePackedRows 517 = packedMinorResidueRow twelveMinor 2 1024 517 := by rfl

theorem twelve_packed_product_517 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 517) twelvePackedRows =
      1024 ^ (517 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 517) := by rfl

theorem twelve_packed_row_518 :
    twelvePackedRows 518 = packedMinorResidueRow twelveMinor 2 1024 518 := by rfl

theorem twelve_packed_product_518 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 518) twelvePackedRows =
      1024 ^ (518 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 518) := by rfl

theorem twelve_packed_row_519 :
    twelvePackedRows 519 = packedMinorResidueRow twelveMinor 2 1024 519 := by rfl

theorem twelve_packed_product_519 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 519) twelvePackedRows =
      1024 ^ (519 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 519) := by rfl

theorem twelve_packed_row_520 :
    twelvePackedRows 520 = packedMinorResidueRow twelveMinor 2 1024 520 := by rfl

theorem twelve_packed_product_520 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 520) twelvePackedRows =
      1024 ^ (520 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 520) := by rfl

theorem twelve_packed_row_521 :
    twelvePackedRows 521 = packedMinorResidueRow twelveMinor 2 1024 521 := by rfl

theorem twelve_packed_product_521 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 521) twelvePackedRows =
      1024 ^ (521 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 521) := by rfl

theorem twelve_packed_row_522 :
    twelvePackedRows 522 = packedMinorResidueRow twelveMinor 2 1024 522 := by rfl

theorem twelve_packed_product_522 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 522) twelvePackedRows =
      1024 ^ (522 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 522) := by rfl

theorem twelve_packed_row_523 :
    twelvePackedRows 523 = packedMinorResidueRow twelveMinor 2 1024 523 := by rfl

theorem twelve_packed_product_523 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 523) twelvePackedRows =
      1024 ^ (523 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 523) := by rfl

theorem twelve_packed_row_524 :
    twelvePackedRows 524 = packedMinorResidueRow twelveMinor 2 1024 524 := by rfl

theorem twelve_packed_product_524 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 524) twelvePackedRows =
      1024 ^ (524 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 524) := by rfl

theorem twelve_packed_row_525 :
    twelvePackedRows 525 = packedMinorResidueRow twelveMinor 2 1024 525 := by rfl

theorem twelve_packed_product_525 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 525) twelvePackedRows =
      1024 ^ (525 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 525) := by rfl

theorem twelve_packed_row_526 :
    twelvePackedRows 526 = packedMinorResidueRow twelveMinor 2 1024 526 := by rfl

theorem twelve_packed_product_526 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 526) twelvePackedRows =
      1024 ^ (526 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 526) := by rfl

theorem twelve_packed_row_527 :
    twelvePackedRows 527 = packedMinorResidueRow twelveMinor 2 1024 527 := by rfl

theorem twelve_packed_product_527 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 527) twelvePackedRows =
      1024 ^ (527 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 527) := by rfl

theorem twelve_packed_row_528 :
    twelvePackedRows 528 = packedMinorResidueRow twelveMinor 2 1024 528 := by rfl

theorem twelve_packed_product_528 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 528) twelvePackedRows =
      1024 ^ (528 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 528) := by rfl

theorem twelve_packed_row_529 :
    twelvePackedRows 529 = packedMinorResidueRow twelveMinor 2 1024 529 := by rfl

theorem twelve_packed_product_529 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 529) twelvePackedRows =
      1024 ^ (529 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 529) := by rfl

theorem twelve_packed_row_530 :
    twelvePackedRows 530 = packedMinorResidueRow twelveMinor 2 1024 530 := by rfl

theorem twelve_packed_product_530 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 530) twelvePackedRows =
      1024 ^ (530 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 530) := by rfl

theorem twelve_packed_row_531 :
    twelvePackedRows 531 = packedMinorResidueRow twelveMinor 2 1024 531 := by rfl

theorem twelve_packed_product_531 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 531) twelvePackedRows =
      1024 ^ (531 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 531) := by rfl

theorem twelve_packed_row_532 :
    twelvePackedRows 532 = packedMinorResidueRow twelveMinor 2 1024 532 := by rfl

theorem twelve_packed_product_532 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 532) twelvePackedRows =
      1024 ^ (532 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 532) := by rfl

theorem twelve_packed_row_533 :
    twelvePackedRows 533 = packedMinorResidueRow twelveMinor 2 1024 533 := by rfl

theorem twelve_packed_product_533 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 533) twelvePackedRows =
      1024 ^ (533 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 533) := by rfl

theorem twelve_packed_row_534 :
    twelvePackedRows 534 = packedMinorResidueRow twelveMinor 2 1024 534 := by rfl

theorem twelve_packed_product_534 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 534) twelvePackedRows =
      1024 ^ (534 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 534) := by rfl

theorem twelve_packed_row_535 :
    twelvePackedRows 535 = packedMinorResidueRow twelveMinor 2 1024 535 := by rfl

theorem twelve_packed_product_535 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 535) twelvePackedRows =
      1024 ^ (535 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 535) := by rfl

theorem twelve_packed_row_536 :
    twelvePackedRows 536 = packedMinorResidueRow twelveMinor 2 1024 536 := by rfl

theorem twelve_packed_product_536 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 536) twelvePackedRows =
      1024 ^ (536 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 536) := by rfl

theorem twelve_packed_row_537 :
    twelvePackedRows 537 = packedMinorResidueRow twelveMinor 2 1024 537 := by rfl

theorem twelve_packed_product_537 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 537) twelvePackedRows =
      1024 ^ (537 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 537) := by rfl

theorem twelve_packed_row_538 :
    twelvePackedRows 538 = packedMinorResidueRow twelveMinor 2 1024 538 := by rfl

theorem twelve_packed_product_538 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 538) twelvePackedRows =
      1024 ^ (538 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 538) := by rfl

theorem twelve_packed_row_539 :
    twelvePackedRows 539 = packedMinorResidueRow twelveMinor 2 1024 539 := by rfl

theorem twelve_packed_product_539 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 539) twelvePackedRows =
      1024 ^ (539 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 539) := by rfl

theorem twelve_packed_row_540 :
    twelvePackedRows 540 = packedMinorResidueRow twelveMinor 2 1024 540 := by rfl

theorem twelve_packed_product_540 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 540) twelvePackedRows =
      1024 ^ (540 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 540) := by rfl

theorem twelve_packed_row_541 :
    twelvePackedRows 541 = packedMinorResidueRow twelveMinor 2 1024 541 := by rfl

theorem twelve_packed_product_541 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 541) twelvePackedRows =
      1024 ^ (541 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 541) := by rfl

theorem twelve_packed_row_542 :
    twelvePackedRows 542 = packedMinorResidueRow twelveMinor 2 1024 542 := by rfl

theorem twelve_packed_product_542 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 542) twelvePackedRows =
      1024 ^ (542 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 542) := by rfl

theorem twelve_packed_row_543 :
    twelvePackedRows 543 = packedMinorResidueRow twelveMinor 2 1024 543 := by rfl

theorem twelve_packed_product_543 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 543) twelvePackedRows =
      1024 ^ (543 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 543) := by rfl

theorem twelve_packed_row_544 :
    twelvePackedRows 544 = packedMinorResidueRow twelveMinor 2 1024 544 := by rfl

theorem twelve_packed_product_544 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 544) twelvePackedRows =
      1024 ^ (544 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 544) := by rfl

theorem twelve_packed_row_545 :
    twelvePackedRows 545 = packedMinorResidueRow twelveMinor 2 1024 545 := by rfl

theorem twelve_packed_product_545 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 545) twelvePackedRows =
      1024 ^ (545 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 545) := by rfl

theorem twelve_packed_row_546 :
    twelvePackedRows 546 = packedMinorResidueRow twelveMinor 2 1024 546 := by rfl

theorem twelve_packed_product_546 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 546) twelvePackedRows =
      1024 ^ (546 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 546) := by rfl

theorem twelve_packed_row_547 :
    twelvePackedRows 547 = packedMinorResidueRow twelveMinor 2 1024 547 := by rfl

theorem twelve_packed_product_547 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 547) twelvePackedRows =
      1024 ^ (547 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 547) := by rfl

theorem twelve_packed_row_548 :
    twelvePackedRows 548 = packedMinorResidueRow twelveMinor 2 1024 548 := by rfl

theorem twelve_packed_product_548 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 548) twelvePackedRows =
      1024 ^ (548 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 548) := by rfl

theorem twelve_packed_row_549 :
    twelvePackedRows 549 = packedMinorResidueRow twelveMinor 2 1024 549 := by rfl

theorem twelve_packed_product_549 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 549) twelvePackedRows =
      1024 ^ (549 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 549) := by rfl

theorem twelve_packed_row_550 :
    twelvePackedRows 550 = packedMinorResidueRow twelveMinor 2 1024 550 := by rfl

theorem twelve_packed_product_550 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 550) twelvePackedRows =
      1024 ^ (550 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 550) := by rfl

theorem twelve_packed_row_551 :
    twelvePackedRows 551 = packedMinorResidueRow twelveMinor 2 1024 551 := by rfl

theorem twelve_packed_product_551 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 551) twelvePackedRows =
      1024 ^ (551 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 551) := by rfl

theorem twelve_packed_row_552 :
    twelvePackedRows 552 = packedMinorResidueRow twelveMinor 2 1024 552 := by rfl

theorem twelve_packed_product_552 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 552) twelvePackedRows =
      1024 ^ (552 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 552) := by rfl

theorem twelve_packed_row_553 :
    twelvePackedRows 553 = packedMinorResidueRow twelveMinor 2 1024 553 := by rfl

theorem twelve_packed_product_553 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 553) twelvePackedRows =
      1024 ^ (553 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 553) := by rfl

theorem twelve_packed_row_554 :
    twelvePackedRows 554 = packedMinorResidueRow twelveMinor 2 1024 554 := by rfl

theorem twelve_packed_product_554 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 554) twelvePackedRows =
      1024 ^ (554 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 554) := by rfl

theorem twelve_packed_row_555 :
    twelvePackedRows 555 = packedMinorResidueRow twelveMinor 2 1024 555 := by rfl

theorem twelve_packed_product_555 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 555) twelvePackedRows =
      1024 ^ (555 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 555) := by rfl

theorem twelve_packed_row_556 :
    twelvePackedRows 556 = packedMinorResidueRow twelveMinor 2 1024 556 := by rfl

theorem twelve_packed_product_556 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 556) twelvePackedRows =
      1024 ^ (556 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 556) := by rfl

theorem twelve_packed_row_557 :
    twelvePackedRows 557 = packedMinorResidueRow twelveMinor 2 1024 557 := by rfl

theorem twelve_packed_product_557 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 557) twelvePackedRows =
      1024 ^ (557 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 557) := by rfl

theorem twelve_packed_row_558 :
    twelvePackedRows 558 = packedMinorResidueRow twelveMinor 2 1024 558 := by rfl

theorem twelve_packed_product_558 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 558) twelvePackedRows =
      1024 ^ (558 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 558) := by rfl

theorem twelve_packed_row_559 :
    twelvePackedRows 559 = packedMinorResidueRow twelveMinor 2 1024 559 := by rfl

theorem twelve_packed_product_559 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 559) twelvePackedRows =
      1024 ^ (559 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 559) := by rfl

theorem twelve_packed_row_560 :
    twelvePackedRows 560 = packedMinorResidueRow twelveMinor 2 1024 560 := by rfl

theorem twelve_packed_product_560 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 560) twelvePackedRows =
      1024 ^ (560 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 560) := by rfl

theorem twelve_packed_row_561 :
    twelvePackedRows 561 = packedMinorResidueRow twelveMinor 2 1024 561 := by rfl

theorem twelve_packed_product_561 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 561) twelvePackedRows =
      1024 ^ (561 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 561) := by rfl

theorem twelve_packed_row_562 :
    twelvePackedRows 562 = packedMinorResidueRow twelveMinor 2 1024 562 := by rfl

theorem twelve_packed_product_562 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 562) twelvePackedRows =
      1024 ^ (562 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 562) := by rfl

theorem twelve_packed_row_563 :
    twelvePackedRows 563 = packedMinorResidueRow twelveMinor 2 1024 563 := by rfl

theorem twelve_packed_product_563 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 563) twelvePackedRows =
      1024 ^ (563 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 563) := by rfl

theorem twelve_packed_row_564 :
    twelvePackedRows 564 = packedMinorResidueRow twelveMinor 2 1024 564 := by rfl

theorem twelve_packed_product_564 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 564) twelvePackedRows =
      1024 ^ (564 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 564) := by rfl

theorem twelve_packed_row_565 :
    twelvePackedRows 565 = packedMinorResidueRow twelveMinor 2 1024 565 := by rfl

theorem twelve_packed_product_565 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 565) twelvePackedRows =
      1024 ^ (565 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 565) := by rfl

theorem twelve_packed_row_566 :
    twelvePackedRows 566 = packedMinorResidueRow twelveMinor 2 1024 566 := by rfl

theorem twelve_packed_product_566 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 566) twelvePackedRows =
      1024 ^ (566 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 566) := by rfl

theorem twelve_packed_row_567 :
    twelvePackedRows 567 = packedMinorResidueRow twelveMinor 2 1024 567 := by rfl

theorem twelve_packed_product_567 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 567) twelvePackedRows =
      1024 ^ (567 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 567) := by rfl

theorem twelve_packed_row_568 :
    twelvePackedRows 568 = packedMinorResidueRow twelveMinor 2 1024 568 := by rfl

theorem twelve_packed_product_568 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 568) twelvePackedRows =
      1024 ^ (568 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 568) := by rfl

theorem twelve_packed_row_569 :
    twelvePackedRows 569 = packedMinorResidueRow twelveMinor 2 1024 569 := by rfl

theorem twelve_packed_product_569 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 569) twelvePackedRows =
      1024 ^ (569 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 569) := by rfl

theorem twelve_packed_row_570 :
    twelvePackedRows 570 = packedMinorResidueRow twelveMinor 2 1024 570 := by rfl

theorem twelve_packed_product_570 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 570) twelvePackedRows =
      1024 ^ (570 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 570) := by rfl

theorem twelve_packed_row_571 :
    twelvePackedRows 571 = packedMinorResidueRow twelveMinor 2 1024 571 := by rfl

theorem twelve_packed_product_571 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 571) twelvePackedRows =
      1024 ^ (571 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 571) := by rfl

end IdealGeneration.QuadraticLowDimension
