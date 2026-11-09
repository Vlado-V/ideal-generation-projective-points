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

theorem upper416 : packedUpper 416 =
    packSparse (2 ^ 40) (upperRows 416) := by decide +kernel

theorem packed416 : packedProduct (lowerRows 416) packedUpper =
    packSparse (2 ^ 40) (targetRows 416) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 416) := by decide +kernel

theorem rowFacts416 : PackedRowFacts 416 := by
  constructor <;> decide +kernel

theorem upper417 : packedUpper 417 =
    packSparse (2 ^ 40) (upperRows 417) := by decide +kernel

theorem packed417 : packedProduct (lowerRows 417) packedUpper =
    packSparse (2 ^ 40) (targetRows 417) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 417) := by decide +kernel

theorem rowFacts417 : PackedRowFacts 417 := by
  constructor <;> decide +kernel

theorem upper418 : packedUpper 418 =
    packSparse (2 ^ 40) (upperRows 418) := by decide +kernel

theorem packed418 : packedProduct (lowerRows 418) packedUpper =
    packSparse (2 ^ 40) (targetRows 418) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 418) := by decide +kernel

theorem rowFacts418 : PackedRowFacts 418 := by
  constructor <;> decide +kernel

theorem upper419 : packedUpper 419 =
    packSparse (2 ^ 40) (upperRows 419) := by decide +kernel

theorem packed419 : packedProduct (lowerRows 419) packedUpper =
    packSparse (2 ^ 40) (targetRows 419) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 419) := by decide +kernel

theorem rowFacts419 : PackedRowFacts 419 := by
  constructor <;> decide +kernel

theorem upper420 : packedUpper 420 =
    packSparse (2 ^ 40) (upperRows 420) := by decide +kernel

theorem packed420 : packedProduct (lowerRows 420) packedUpper =
    packSparse (2 ^ 40) (targetRows 420) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 420) := by decide +kernel

theorem rowFacts420 : PackedRowFacts 420 := by
  constructor <;> decide +kernel

theorem upper421 : packedUpper 421 =
    packSparse (2 ^ 40) (upperRows 421) := by decide +kernel

theorem packed421 : packedProduct (lowerRows 421) packedUpper =
    packSparse (2 ^ 40) (targetRows 421) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 421) := by decide +kernel

theorem rowFacts421 : PackedRowFacts 421 := by
  constructor <;> decide +kernel

theorem upper422 : packedUpper 422 =
    packSparse (2 ^ 40) (upperRows 422) := by decide +kernel

theorem packed422 : packedProduct (lowerRows 422) packedUpper =
    packSparse (2 ^ 40) (targetRows 422) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 422) := by decide +kernel

theorem rowFacts422 : PackedRowFacts 422 := by
  constructor <;> decide +kernel

theorem upper423 : packedUpper 423 =
    packSparse (2 ^ 40) (upperRows 423) := by decide +kernel

theorem packed423 : packedProduct (lowerRows 423) packedUpper =
    packSparse (2 ^ 40) (targetRows 423) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 423) := by decide +kernel

theorem rowFacts423 : PackedRowFacts 423 := by
  constructor <;> decide +kernel

theorem upper424 : packedUpper 424 =
    packSparse (2 ^ 40) (upperRows 424) := by decide +kernel

theorem packed424 : packedProduct (lowerRows 424) packedUpper =
    packSparse (2 ^ 40) (targetRows 424) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 424) := by decide +kernel

theorem rowFacts424 : PackedRowFacts 424 := by
  constructor <;> decide +kernel

theorem upper425 : packedUpper 425 =
    packSparse (2 ^ 40) (upperRows 425) := by decide +kernel

theorem packed425 : packedProduct (lowerRows 425) packedUpper =
    packSparse (2 ^ 40) (targetRows 425) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 425) := by decide +kernel

theorem rowFacts425 : PackedRowFacts 425 := by
  constructor <;> decide +kernel

theorem upper426 : packedUpper 426 =
    packSparse (2 ^ 40) (upperRows 426) := by decide +kernel

theorem packed426 : packedProduct (lowerRows 426) packedUpper =
    packSparse (2 ^ 40) (targetRows 426) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 426) := by decide +kernel

theorem rowFacts426 : PackedRowFacts 426 := by
  constructor <;> decide +kernel

theorem upper427 : packedUpper 427 =
    packSparse (2 ^ 40) (upperRows 427) := by decide +kernel

theorem packed427 : packedProduct (lowerRows 427) packedUpper =
    packSparse (2 ^ 40) (targetRows 427) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 427) := by decide +kernel

theorem rowFacts427 : PackedRowFacts 427 := by
  constructor <;> decide +kernel

theorem upper428 : packedUpper 428 =
    packSparse (2 ^ 40) (upperRows 428) := by decide +kernel

theorem packed428 : packedProduct (lowerRows 428) packedUpper =
    packSparse (2 ^ 40) (targetRows 428) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 428) := by decide +kernel

theorem rowFacts428 : PackedRowFacts 428 := by
  constructor <;> decide +kernel

theorem upper429 : packedUpper 429 =
    packSparse (2 ^ 40) (upperRows 429) := by decide +kernel

theorem packed429 : packedProduct (lowerRows 429) packedUpper =
    packSparse (2 ^ 40) (targetRows 429) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 429) := by decide +kernel

theorem rowFacts429 : PackedRowFacts 429 := by
  constructor <;> decide +kernel

theorem upper430 : packedUpper 430 =
    packSparse (2 ^ 40) (upperRows 430) := by decide +kernel

theorem packed430 : packedProduct (lowerRows 430) packedUpper =
    packSparse (2 ^ 40) (targetRows 430) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 430) := by decide +kernel

theorem rowFacts430 : PackedRowFacts 430 := by
  constructor <;> decide +kernel

theorem upper431 : packedUpper 431 =
    packSparse (2 ^ 40) (upperRows 431) := by decide +kernel

theorem packed431 : packedProduct (lowerRows 431) packedUpper =
    packSparse (2 ^ 40) (targetRows 431) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 431) := by decide +kernel

theorem rowFacts431 : PackedRowFacts 431 := by
  constructor <;> decide +kernel

theorem upper432 : packedUpper 432 =
    packSparse (2 ^ 40) (upperRows 432) := by decide +kernel

theorem packed432 : packedProduct (lowerRows 432) packedUpper =
    packSparse (2 ^ 40) (targetRows 432) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 432) := by decide +kernel

theorem rowFacts432 : PackedRowFacts 432 := by
  constructor <;> decide +kernel

theorem upper433 : packedUpper 433 =
    packSparse (2 ^ 40) (upperRows 433) := by decide +kernel

theorem packed433 : packedProduct (lowerRows 433) packedUpper =
    packSparse (2 ^ 40) (targetRows 433) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 433) := by decide +kernel

theorem rowFacts433 : PackedRowFacts 433 := by
  constructor <;> decide +kernel

theorem upper434 : packedUpper 434 =
    packSparse (2 ^ 40) (upperRows 434) := by decide +kernel

theorem packed434 : packedProduct (lowerRows 434) packedUpper =
    packSparse (2 ^ 40) (targetRows 434) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 434) := by decide +kernel

theorem rowFacts434 : PackedRowFacts 434 := by
  constructor <;> decide +kernel

theorem upper435 : packedUpper 435 =
    packSparse (2 ^ 40) (upperRows 435) := by decide +kernel

theorem packed435 : packedProduct (lowerRows 435) packedUpper =
    packSparse (2 ^ 40) (targetRows 435) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 435) := by decide +kernel

theorem rowFacts435 : PackedRowFacts 435 := by
  constructor <;> decide +kernel

theorem upper436 : packedUpper 436 =
    packSparse (2 ^ 40) (upperRows 436) := by decide +kernel

theorem packed436 : packedProduct (lowerRows 436) packedUpper =
    packSparse (2 ^ 40) (targetRows 436) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 436) := by decide +kernel

theorem rowFacts436 : PackedRowFacts 436 := by
  constructor <;> decide +kernel

theorem upper437 : packedUpper 437 =
    packSparse (2 ^ 40) (upperRows 437) := by decide +kernel

theorem packed437 : packedProduct (lowerRows 437) packedUpper =
    packSparse (2 ^ 40) (targetRows 437) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 437) := by decide +kernel

theorem rowFacts437 : PackedRowFacts 437 := by
  constructor <;> decide +kernel

theorem upper438 : packedUpper 438 =
    packSparse (2 ^ 40) (upperRows 438) := by decide +kernel

theorem packed438 : packedProduct (lowerRows 438) packedUpper =
    packSparse (2 ^ 40) (targetRows 438) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 438) := by decide +kernel

theorem rowFacts438 : PackedRowFacts 438 := by
  constructor <;> decide +kernel

theorem upper439 : packedUpper 439 =
    packSparse (2 ^ 40) (upperRows 439) := by decide +kernel

theorem packed439 : packedProduct (lowerRows 439) packedUpper =
    packSparse (2 ^ 40) (targetRows 439) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 439) := by decide +kernel

theorem rowFacts439 : PackedRowFacts 439 := by
  constructor <;> decide +kernel

theorem upper440 : packedUpper 440 =
    packSparse (2 ^ 40) (upperRows 440) := by decide +kernel

theorem packed440 : packedProduct (lowerRows 440) packedUpper =
    packSparse (2 ^ 40) (targetRows 440) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 440) := by decide +kernel

theorem rowFacts440 : PackedRowFacts 440 := by
  constructor <;> decide +kernel

theorem upper441 : packedUpper 441 =
    packSparse (2 ^ 40) (upperRows 441) := by decide +kernel

theorem packed441 : packedProduct (lowerRows 441) packedUpper =
    packSparse (2 ^ 40) (targetRows 441) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 441) := by decide +kernel

theorem rowFacts441 : PackedRowFacts 441 := by
  constructor <;> decide +kernel

theorem upper442 : packedUpper 442 =
    packSparse (2 ^ 40) (upperRows 442) := by decide +kernel

theorem packed442 : packedProduct (lowerRows 442) packedUpper =
    packSparse (2 ^ 40) (targetRows 442) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 442) := by decide +kernel

theorem rowFacts442 : PackedRowFacts 442 := by
  constructor <;> decide +kernel

theorem upper443 : packedUpper 443 =
    packSparse (2 ^ 40) (upperRows 443) := by decide +kernel

theorem packed443 : packedProduct (lowerRows 443) packedUpper =
    packSparse (2 ^ 40) (targetRows 443) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 443) := by decide +kernel

theorem rowFacts443 : PackedRowFacts 443 := by
  constructor <;> decide +kernel

theorem upper444 : packedUpper 444 =
    packSparse (2 ^ 40) (upperRows 444) := by decide +kernel

theorem packed444 : packedProduct (lowerRows 444) packedUpper =
    packSparse (2 ^ 40) (targetRows 444) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 444) := by decide +kernel

theorem rowFacts444 : PackedRowFacts 444 := by
  constructor <;> decide +kernel

theorem upper445 : packedUpper 445 =
    packSparse (2 ^ 40) (upperRows 445) := by decide +kernel

theorem packed445 : packedProduct (lowerRows 445) packedUpper =
    packSparse (2 ^ 40) (targetRows 445) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 445) := by decide +kernel

theorem rowFacts445 : PackedRowFacts 445 := by
  constructor <;> decide +kernel

theorem upper446 : packedUpper 446 =
    packSparse (2 ^ 40) (upperRows 446) := by decide +kernel

theorem packed446 : packedProduct (lowerRows 446) packedUpper =
    packSparse (2 ^ 40) (targetRows 446) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 446) := by decide +kernel

theorem rowFacts446 : PackedRowFacts 446 := by
  constructor <;> decide +kernel

theorem upper447 : packedUpper 447 =
    packSparse (2 ^ 40) (upperRows 447) := by decide +kernel

theorem packed447 : packedProduct (lowerRows 447) packedUpper =
    packSparse (2 ^ 40) (targetRows 447) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 447) := by decide +kernel

theorem rowFacts447 : PackedRowFacts 447 := by
  constructor <;> decide +kernel

#print axioms packed447

end CertifiedRank.C2.PackedCertificate
