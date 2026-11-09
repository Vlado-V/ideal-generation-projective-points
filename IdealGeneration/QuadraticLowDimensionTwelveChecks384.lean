module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 384–479 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_384 :
    twelvePackedRows 384 = packedMinorResidueRow twelveMinor 2 1024 384 := by rfl

theorem twelve_packed_product_384 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 384) twelvePackedRows =
      1024 ^ (384 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 384) := by rfl

theorem twelve_packed_row_385 :
    twelvePackedRows 385 = packedMinorResidueRow twelveMinor 2 1024 385 := by rfl

theorem twelve_packed_product_385 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 385) twelvePackedRows =
      1024 ^ (385 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 385) := by rfl

theorem twelve_packed_row_386 :
    twelvePackedRows 386 = packedMinorResidueRow twelveMinor 2 1024 386 := by rfl

theorem twelve_packed_product_386 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 386) twelvePackedRows =
      1024 ^ (386 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 386) := by rfl

theorem twelve_packed_row_387 :
    twelvePackedRows 387 = packedMinorResidueRow twelveMinor 2 1024 387 := by rfl

theorem twelve_packed_product_387 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 387) twelvePackedRows =
      1024 ^ (387 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 387) := by rfl

theorem twelve_packed_row_388 :
    twelvePackedRows 388 = packedMinorResidueRow twelveMinor 2 1024 388 := by rfl

theorem twelve_packed_product_388 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 388) twelvePackedRows =
      1024 ^ (388 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 388) := by rfl

theorem twelve_packed_row_389 :
    twelvePackedRows 389 = packedMinorResidueRow twelveMinor 2 1024 389 := by rfl

theorem twelve_packed_product_389 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 389) twelvePackedRows =
      1024 ^ (389 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 389) := by rfl

theorem twelve_packed_row_390 :
    twelvePackedRows 390 = packedMinorResidueRow twelveMinor 2 1024 390 := by rfl

theorem twelve_packed_product_390 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 390) twelvePackedRows =
      1024 ^ (390 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 390) := by rfl

theorem twelve_packed_row_391 :
    twelvePackedRows 391 = packedMinorResidueRow twelveMinor 2 1024 391 := by rfl

theorem twelve_packed_product_391 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 391) twelvePackedRows =
      1024 ^ (391 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 391) := by rfl

theorem twelve_packed_row_392 :
    twelvePackedRows 392 = packedMinorResidueRow twelveMinor 2 1024 392 := by rfl

theorem twelve_packed_product_392 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 392) twelvePackedRows =
      1024 ^ (392 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 392) := by rfl

theorem twelve_packed_row_393 :
    twelvePackedRows 393 = packedMinorResidueRow twelveMinor 2 1024 393 := by rfl

theorem twelve_packed_product_393 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 393) twelvePackedRows =
      1024 ^ (393 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 393) := by rfl

theorem twelve_packed_row_394 :
    twelvePackedRows 394 = packedMinorResidueRow twelveMinor 2 1024 394 := by rfl

theorem twelve_packed_product_394 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 394) twelvePackedRows =
      1024 ^ (394 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 394) := by rfl

theorem twelve_packed_row_395 :
    twelvePackedRows 395 = packedMinorResidueRow twelveMinor 2 1024 395 := by rfl

theorem twelve_packed_product_395 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 395) twelvePackedRows =
      1024 ^ (395 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 395) := by rfl

theorem twelve_packed_row_396 :
    twelvePackedRows 396 = packedMinorResidueRow twelveMinor 2 1024 396 := by rfl

theorem twelve_packed_product_396 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 396) twelvePackedRows =
      1024 ^ (396 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 396) := by rfl

theorem twelve_packed_row_397 :
    twelvePackedRows 397 = packedMinorResidueRow twelveMinor 2 1024 397 := by rfl

theorem twelve_packed_product_397 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 397) twelvePackedRows =
      1024 ^ (397 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 397) := by rfl

theorem twelve_packed_row_398 :
    twelvePackedRows 398 = packedMinorResidueRow twelveMinor 2 1024 398 := by rfl

theorem twelve_packed_product_398 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 398) twelvePackedRows =
      1024 ^ (398 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 398) := by rfl

theorem twelve_packed_row_399 :
    twelvePackedRows 399 = packedMinorResidueRow twelveMinor 2 1024 399 := by rfl

theorem twelve_packed_product_399 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 399) twelvePackedRows =
      1024 ^ (399 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 399) := by rfl

theorem twelve_packed_row_400 :
    twelvePackedRows 400 = packedMinorResidueRow twelveMinor 2 1024 400 := by rfl

theorem twelve_packed_product_400 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 400) twelvePackedRows =
      1024 ^ (400 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 400) := by rfl

theorem twelve_packed_row_401 :
    twelvePackedRows 401 = packedMinorResidueRow twelveMinor 2 1024 401 := by rfl

theorem twelve_packed_product_401 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 401) twelvePackedRows =
      1024 ^ (401 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 401) := by rfl

theorem twelve_packed_row_402 :
    twelvePackedRows 402 = packedMinorResidueRow twelveMinor 2 1024 402 := by rfl

theorem twelve_packed_product_402 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 402) twelvePackedRows =
      1024 ^ (402 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 402) := by rfl

theorem twelve_packed_row_403 :
    twelvePackedRows 403 = packedMinorResidueRow twelveMinor 2 1024 403 := by rfl

theorem twelve_packed_product_403 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 403) twelvePackedRows =
      1024 ^ (403 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 403) := by rfl

theorem twelve_packed_row_404 :
    twelvePackedRows 404 = packedMinorResidueRow twelveMinor 2 1024 404 := by rfl

theorem twelve_packed_product_404 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 404) twelvePackedRows =
      1024 ^ (404 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 404) := by rfl

theorem twelve_packed_row_405 :
    twelvePackedRows 405 = packedMinorResidueRow twelveMinor 2 1024 405 := by rfl

theorem twelve_packed_product_405 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 405) twelvePackedRows =
      1024 ^ (405 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 405) := by rfl

theorem twelve_packed_row_406 :
    twelvePackedRows 406 = packedMinorResidueRow twelveMinor 2 1024 406 := by rfl

theorem twelve_packed_product_406 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 406) twelvePackedRows =
      1024 ^ (406 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 406) := by rfl

theorem twelve_packed_row_407 :
    twelvePackedRows 407 = packedMinorResidueRow twelveMinor 2 1024 407 := by rfl

theorem twelve_packed_product_407 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 407) twelvePackedRows =
      1024 ^ (407 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 407) := by rfl

theorem twelve_packed_row_408 :
    twelvePackedRows 408 = packedMinorResidueRow twelveMinor 2 1024 408 := by rfl

theorem twelve_packed_product_408 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 408) twelvePackedRows =
      1024 ^ (408 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 408) := by rfl

theorem twelve_packed_row_409 :
    twelvePackedRows 409 = packedMinorResidueRow twelveMinor 2 1024 409 := by rfl

theorem twelve_packed_product_409 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 409) twelvePackedRows =
      1024 ^ (409 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 409) := by rfl

theorem twelve_packed_row_410 :
    twelvePackedRows 410 = packedMinorResidueRow twelveMinor 2 1024 410 := by rfl

theorem twelve_packed_product_410 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 410) twelvePackedRows =
      1024 ^ (410 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 410) := by rfl

theorem twelve_packed_row_411 :
    twelvePackedRows 411 = packedMinorResidueRow twelveMinor 2 1024 411 := by rfl

theorem twelve_packed_product_411 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 411) twelvePackedRows =
      1024 ^ (411 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 411) := by rfl

theorem twelve_packed_row_412 :
    twelvePackedRows 412 = packedMinorResidueRow twelveMinor 2 1024 412 := by rfl

theorem twelve_packed_product_412 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 412) twelvePackedRows =
      1024 ^ (412 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 412) := by rfl

theorem twelve_packed_row_413 :
    twelvePackedRows 413 = packedMinorResidueRow twelveMinor 2 1024 413 := by rfl

theorem twelve_packed_product_413 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 413) twelvePackedRows =
      1024 ^ (413 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 413) := by rfl

theorem twelve_packed_row_414 :
    twelvePackedRows 414 = packedMinorResidueRow twelveMinor 2 1024 414 := by rfl

theorem twelve_packed_product_414 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 414) twelvePackedRows =
      1024 ^ (414 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 414) := by rfl

theorem twelve_packed_row_415 :
    twelvePackedRows 415 = packedMinorResidueRow twelveMinor 2 1024 415 := by rfl

theorem twelve_packed_product_415 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 415) twelvePackedRows =
      1024 ^ (415 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 415) := by rfl

theorem twelve_packed_row_416 :
    twelvePackedRows 416 = packedMinorResidueRow twelveMinor 2 1024 416 := by rfl

theorem twelve_packed_product_416 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 416) twelvePackedRows =
      1024 ^ (416 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 416) := by rfl

theorem twelve_packed_row_417 :
    twelvePackedRows 417 = packedMinorResidueRow twelveMinor 2 1024 417 := by rfl

theorem twelve_packed_product_417 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 417) twelvePackedRows =
      1024 ^ (417 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 417) := by rfl

theorem twelve_packed_row_418 :
    twelvePackedRows 418 = packedMinorResidueRow twelveMinor 2 1024 418 := by rfl

theorem twelve_packed_product_418 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 418) twelvePackedRows =
      1024 ^ (418 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 418) := by rfl

theorem twelve_packed_row_419 :
    twelvePackedRows 419 = packedMinorResidueRow twelveMinor 2 1024 419 := by rfl

theorem twelve_packed_product_419 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 419) twelvePackedRows =
      1024 ^ (419 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 419) := by rfl

theorem twelve_packed_row_420 :
    twelvePackedRows 420 = packedMinorResidueRow twelveMinor 2 1024 420 := by rfl

theorem twelve_packed_product_420 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 420) twelvePackedRows =
      1024 ^ (420 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 420) := by rfl

theorem twelve_packed_row_421 :
    twelvePackedRows 421 = packedMinorResidueRow twelveMinor 2 1024 421 := by rfl

theorem twelve_packed_product_421 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 421) twelvePackedRows =
      1024 ^ (421 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 421) := by rfl

theorem twelve_packed_row_422 :
    twelvePackedRows 422 = packedMinorResidueRow twelveMinor 2 1024 422 := by rfl

theorem twelve_packed_product_422 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 422) twelvePackedRows =
      1024 ^ (422 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 422) := by rfl

theorem twelve_packed_row_423 :
    twelvePackedRows 423 = packedMinorResidueRow twelveMinor 2 1024 423 := by rfl

theorem twelve_packed_product_423 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 423) twelvePackedRows =
      1024 ^ (423 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 423) := by rfl

theorem twelve_packed_row_424 :
    twelvePackedRows 424 = packedMinorResidueRow twelveMinor 2 1024 424 := by rfl

theorem twelve_packed_product_424 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 424) twelvePackedRows =
      1024 ^ (424 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 424) := by rfl

theorem twelve_packed_row_425 :
    twelvePackedRows 425 = packedMinorResidueRow twelveMinor 2 1024 425 := by rfl

theorem twelve_packed_product_425 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 425) twelvePackedRows =
      1024 ^ (425 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 425) := by rfl

theorem twelve_packed_row_426 :
    twelvePackedRows 426 = packedMinorResidueRow twelveMinor 2 1024 426 := by rfl

theorem twelve_packed_product_426 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 426) twelvePackedRows =
      1024 ^ (426 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 426) := by rfl

theorem twelve_packed_row_427 :
    twelvePackedRows 427 = packedMinorResidueRow twelveMinor 2 1024 427 := by rfl

theorem twelve_packed_product_427 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 427) twelvePackedRows =
      1024 ^ (427 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 427) := by rfl

theorem twelve_packed_row_428 :
    twelvePackedRows 428 = packedMinorResidueRow twelveMinor 2 1024 428 := by rfl

theorem twelve_packed_product_428 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 428) twelvePackedRows =
      1024 ^ (428 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 428) := by rfl

theorem twelve_packed_row_429 :
    twelvePackedRows 429 = packedMinorResidueRow twelveMinor 2 1024 429 := by rfl

theorem twelve_packed_product_429 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 429) twelvePackedRows =
      1024 ^ (429 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 429) := by rfl

theorem twelve_packed_row_430 :
    twelvePackedRows 430 = packedMinorResidueRow twelveMinor 2 1024 430 := by rfl

theorem twelve_packed_product_430 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 430) twelvePackedRows =
      1024 ^ (430 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 430) := by rfl

theorem twelve_packed_row_431 :
    twelvePackedRows 431 = packedMinorResidueRow twelveMinor 2 1024 431 := by rfl

theorem twelve_packed_product_431 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 431) twelvePackedRows =
      1024 ^ (431 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 431) := by rfl

theorem twelve_packed_row_432 :
    twelvePackedRows 432 = packedMinorResidueRow twelveMinor 2 1024 432 := by rfl

theorem twelve_packed_product_432 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 432) twelvePackedRows =
      1024 ^ (432 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 432) := by rfl

theorem twelve_packed_row_433 :
    twelvePackedRows 433 = packedMinorResidueRow twelveMinor 2 1024 433 := by rfl

theorem twelve_packed_product_433 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 433) twelvePackedRows =
      1024 ^ (433 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 433) := by rfl

theorem twelve_packed_row_434 :
    twelvePackedRows 434 = packedMinorResidueRow twelveMinor 2 1024 434 := by rfl

theorem twelve_packed_product_434 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 434) twelvePackedRows =
      1024 ^ (434 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 434) := by rfl

theorem twelve_packed_row_435 :
    twelvePackedRows 435 = packedMinorResidueRow twelveMinor 2 1024 435 := by rfl

theorem twelve_packed_product_435 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 435) twelvePackedRows =
      1024 ^ (435 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 435) := by rfl

theorem twelve_packed_row_436 :
    twelvePackedRows 436 = packedMinorResidueRow twelveMinor 2 1024 436 := by rfl

theorem twelve_packed_product_436 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 436) twelvePackedRows =
      1024 ^ (436 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 436) := by rfl

theorem twelve_packed_row_437 :
    twelvePackedRows 437 = packedMinorResidueRow twelveMinor 2 1024 437 := by rfl

theorem twelve_packed_product_437 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 437) twelvePackedRows =
      1024 ^ (437 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 437) := by rfl

theorem twelve_packed_row_438 :
    twelvePackedRows 438 = packedMinorResidueRow twelveMinor 2 1024 438 := by rfl

theorem twelve_packed_product_438 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 438) twelvePackedRows =
      1024 ^ (438 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 438) := by rfl

theorem twelve_packed_row_439 :
    twelvePackedRows 439 = packedMinorResidueRow twelveMinor 2 1024 439 := by rfl

theorem twelve_packed_product_439 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 439) twelvePackedRows =
      1024 ^ (439 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 439) := by rfl

theorem twelve_packed_row_440 :
    twelvePackedRows 440 = packedMinorResidueRow twelveMinor 2 1024 440 := by rfl

theorem twelve_packed_product_440 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 440) twelvePackedRows =
      1024 ^ (440 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 440) := by rfl

theorem twelve_packed_row_441 :
    twelvePackedRows 441 = packedMinorResidueRow twelveMinor 2 1024 441 := by rfl

theorem twelve_packed_product_441 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 441) twelvePackedRows =
      1024 ^ (441 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 441) := by rfl

theorem twelve_packed_row_442 :
    twelvePackedRows 442 = packedMinorResidueRow twelveMinor 2 1024 442 := by rfl

theorem twelve_packed_product_442 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 442) twelvePackedRows =
      1024 ^ (442 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 442) := by rfl

theorem twelve_packed_row_443 :
    twelvePackedRows 443 = packedMinorResidueRow twelveMinor 2 1024 443 := by rfl

theorem twelve_packed_product_443 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 443) twelvePackedRows =
      1024 ^ (443 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 443) := by rfl

theorem twelve_packed_row_444 :
    twelvePackedRows 444 = packedMinorResidueRow twelveMinor 2 1024 444 := by rfl

theorem twelve_packed_product_444 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 444) twelvePackedRows =
      1024 ^ (444 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 444) := by rfl

theorem twelve_packed_row_445 :
    twelvePackedRows 445 = packedMinorResidueRow twelveMinor 2 1024 445 := by rfl

theorem twelve_packed_product_445 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 445) twelvePackedRows =
      1024 ^ (445 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 445) := by rfl

theorem twelve_packed_row_446 :
    twelvePackedRows 446 = packedMinorResidueRow twelveMinor 2 1024 446 := by rfl

theorem twelve_packed_product_446 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 446) twelvePackedRows =
      1024 ^ (446 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 446) := by rfl

theorem twelve_packed_row_447 :
    twelvePackedRows 447 = packedMinorResidueRow twelveMinor 2 1024 447 := by rfl

theorem twelve_packed_product_447 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 447) twelvePackedRows =
      1024 ^ (447 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 447) := by rfl

theorem twelve_packed_row_448 :
    twelvePackedRows 448 = packedMinorResidueRow twelveMinor 2 1024 448 := by rfl

theorem twelve_packed_product_448 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 448) twelvePackedRows =
      1024 ^ (448 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 448) := by rfl

theorem twelve_packed_row_449 :
    twelvePackedRows 449 = packedMinorResidueRow twelveMinor 2 1024 449 := by rfl

theorem twelve_packed_product_449 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 449) twelvePackedRows =
      1024 ^ (449 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 449) := by rfl

theorem twelve_packed_row_450 :
    twelvePackedRows 450 = packedMinorResidueRow twelveMinor 2 1024 450 := by rfl

theorem twelve_packed_product_450 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 450) twelvePackedRows =
      1024 ^ (450 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 450) := by rfl

theorem twelve_packed_row_451 :
    twelvePackedRows 451 = packedMinorResidueRow twelveMinor 2 1024 451 := by rfl

theorem twelve_packed_product_451 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 451) twelvePackedRows =
      1024 ^ (451 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 451) := by rfl

theorem twelve_packed_row_452 :
    twelvePackedRows 452 = packedMinorResidueRow twelveMinor 2 1024 452 := by rfl

theorem twelve_packed_product_452 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 452) twelvePackedRows =
      1024 ^ (452 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 452) := by rfl

theorem twelve_packed_row_453 :
    twelvePackedRows 453 = packedMinorResidueRow twelveMinor 2 1024 453 := by rfl

theorem twelve_packed_product_453 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 453) twelvePackedRows =
      1024 ^ (453 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 453) := by rfl

theorem twelve_packed_row_454 :
    twelvePackedRows 454 = packedMinorResidueRow twelveMinor 2 1024 454 := by rfl

theorem twelve_packed_product_454 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 454) twelvePackedRows =
      1024 ^ (454 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 454) := by rfl

theorem twelve_packed_row_455 :
    twelvePackedRows 455 = packedMinorResidueRow twelveMinor 2 1024 455 := by rfl

theorem twelve_packed_product_455 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 455) twelvePackedRows =
      1024 ^ (455 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 455) := by rfl

theorem twelve_packed_row_456 :
    twelvePackedRows 456 = packedMinorResidueRow twelveMinor 2 1024 456 := by rfl

theorem twelve_packed_product_456 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 456) twelvePackedRows =
      1024 ^ (456 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 456) := by rfl

theorem twelve_packed_row_457 :
    twelvePackedRows 457 = packedMinorResidueRow twelveMinor 2 1024 457 := by rfl

theorem twelve_packed_product_457 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 457) twelvePackedRows =
      1024 ^ (457 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 457) := by rfl

theorem twelve_packed_row_458 :
    twelvePackedRows 458 = packedMinorResidueRow twelveMinor 2 1024 458 := by rfl

theorem twelve_packed_product_458 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 458) twelvePackedRows =
      1024 ^ (458 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 458) := by rfl

theorem twelve_packed_row_459 :
    twelvePackedRows 459 = packedMinorResidueRow twelveMinor 2 1024 459 := by rfl

theorem twelve_packed_product_459 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 459) twelvePackedRows =
      1024 ^ (459 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 459) := by rfl

theorem twelve_packed_row_460 :
    twelvePackedRows 460 = packedMinorResidueRow twelveMinor 2 1024 460 := by rfl

theorem twelve_packed_product_460 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 460) twelvePackedRows =
      1024 ^ (460 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 460) := by rfl

theorem twelve_packed_row_461 :
    twelvePackedRows 461 = packedMinorResidueRow twelveMinor 2 1024 461 := by rfl

theorem twelve_packed_product_461 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 461) twelvePackedRows =
      1024 ^ (461 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 461) := by rfl

theorem twelve_packed_row_462 :
    twelvePackedRows 462 = packedMinorResidueRow twelveMinor 2 1024 462 := by rfl

theorem twelve_packed_product_462 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 462) twelvePackedRows =
      1024 ^ (462 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 462) := by rfl

theorem twelve_packed_row_463 :
    twelvePackedRows 463 = packedMinorResidueRow twelveMinor 2 1024 463 := by rfl

theorem twelve_packed_product_463 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 463) twelvePackedRows =
      1024 ^ (463 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 463) := by rfl

theorem twelve_packed_row_464 :
    twelvePackedRows 464 = packedMinorResidueRow twelveMinor 2 1024 464 := by rfl

theorem twelve_packed_product_464 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 464) twelvePackedRows =
      1024 ^ (464 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 464) := by rfl

theorem twelve_packed_row_465 :
    twelvePackedRows 465 = packedMinorResidueRow twelveMinor 2 1024 465 := by rfl

theorem twelve_packed_product_465 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 465) twelvePackedRows =
      1024 ^ (465 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 465) := by rfl

theorem twelve_packed_row_466 :
    twelvePackedRows 466 = packedMinorResidueRow twelveMinor 2 1024 466 := by rfl

theorem twelve_packed_product_466 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 466) twelvePackedRows =
      1024 ^ (466 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 466) := by rfl

theorem twelve_packed_row_467 :
    twelvePackedRows 467 = packedMinorResidueRow twelveMinor 2 1024 467 := by rfl

theorem twelve_packed_product_467 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 467) twelvePackedRows =
      1024 ^ (467 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 467) := by rfl

theorem twelve_packed_row_468 :
    twelvePackedRows 468 = packedMinorResidueRow twelveMinor 2 1024 468 := by rfl

theorem twelve_packed_product_468 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 468) twelvePackedRows =
      1024 ^ (468 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 468) := by rfl

theorem twelve_packed_row_469 :
    twelvePackedRows 469 = packedMinorResidueRow twelveMinor 2 1024 469 := by rfl

theorem twelve_packed_product_469 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 469) twelvePackedRows =
      1024 ^ (469 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 469) := by rfl

theorem twelve_packed_row_470 :
    twelvePackedRows 470 = packedMinorResidueRow twelveMinor 2 1024 470 := by rfl

theorem twelve_packed_product_470 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 470) twelvePackedRows =
      1024 ^ (470 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 470) := by rfl

theorem twelve_packed_row_471 :
    twelvePackedRows 471 = packedMinorResidueRow twelveMinor 2 1024 471 := by rfl

theorem twelve_packed_product_471 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 471) twelvePackedRows =
      1024 ^ (471 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 471) := by rfl

theorem twelve_packed_row_472 :
    twelvePackedRows 472 = packedMinorResidueRow twelveMinor 2 1024 472 := by rfl

theorem twelve_packed_product_472 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 472) twelvePackedRows =
      1024 ^ (472 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 472) := by rfl

theorem twelve_packed_row_473 :
    twelvePackedRows 473 = packedMinorResidueRow twelveMinor 2 1024 473 := by rfl

theorem twelve_packed_product_473 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 473) twelvePackedRows =
      1024 ^ (473 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 473) := by rfl

theorem twelve_packed_row_474 :
    twelvePackedRows 474 = packedMinorResidueRow twelveMinor 2 1024 474 := by rfl

theorem twelve_packed_product_474 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 474) twelvePackedRows =
      1024 ^ (474 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 474) := by rfl

theorem twelve_packed_row_475 :
    twelvePackedRows 475 = packedMinorResidueRow twelveMinor 2 1024 475 := by rfl

theorem twelve_packed_product_475 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 475) twelvePackedRows =
      1024 ^ (475 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 475) := by rfl

theorem twelve_packed_row_476 :
    twelvePackedRows 476 = packedMinorResidueRow twelveMinor 2 1024 476 := by rfl

theorem twelve_packed_product_476 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 476) twelvePackedRows =
      1024 ^ (476 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 476) := by rfl

theorem twelve_packed_row_477 :
    twelvePackedRows 477 = packedMinorResidueRow twelveMinor 2 1024 477 := by rfl

theorem twelve_packed_product_477 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 477) twelvePackedRows =
      1024 ^ (477 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 477) := by rfl

theorem twelve_packed_row_478 :
    twelvePackedRows 478 = packedMinorResidueRow twelveMinor 2 1024 478 := by rfl

theorem twelve_packed_product_478 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 478) twelvePackedRows =
      1024 ^ (478 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 478) := by rfl

theorem twelve_packed_row_479 :
    twelvePackedRows 479 = packedMinorResidueRow twelveMinor 2 1024 479 := by rfl

theorem twelve_packed_product_479 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 479) twelvePackedRows =
      1024 ^ (479 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 479) := by rfl

end IdealGeneration.QuadraticLowDimension
