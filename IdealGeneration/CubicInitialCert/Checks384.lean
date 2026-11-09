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

theorem upper384 : packedUpper 384 =
    packSparse (2 ^ 40) (upperRows 384) := by decide +kernel

theorem packed384 : packedProduct (lowerRows 384) packedUpper =
    packSparse (2 ^ 40) (targetRows 384) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 384) := by decide +kernel

theorem rowFacts384 : PackedRowFacts 384 := by
  constructor <;> decide +kernel

theorem upper385 : packedUpper 385 =
    packSparse (2 ^ 40) (upperRows 385) := by decide +kernel

theorem packed385 : packedProduct (lowerRows 385) packedUpper =
    packSparse (2 ^ 40) (targetRows 385) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 385) := by decide +kernel

theorem rowFacts385 : PackedRowFacts 385 := by
  constructor <;> decide +kernel

theorem upper386 : packedUpper 386 =
    packSparse (2 ^ 40) (upperRows 386) := by decide +kernel

theorem packed386 : packedProduct (lowerRows 386) packedUpper =
    packSparse (2 ^ 40) (targetRows 386) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 386) := by decide +kernel

theorem rowFacts386 : PackedRowFacts 386 := by
  constructor <;> decide +kernel

theorem upper387 : packedUpper 387 =
    packSparse (2 ^ 40) (upperRows 387) := by decide +kernel

theorem packed387 : packedProduct (lowerRows 387) packedUpper =
    packSparse (2 ^ 40) (targetRows 387) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 387) := by decide +kernel

theorem rowFacts387 : PackedRowFacts 387 := by
  constructor <;> decide +kernel

theorem upper388 : packedUpper 388 =
    packSparse (2 ^ 40) (upperRows 388) := by decide +kernel

theorem packed388 : packedProduct (lowerRows 388) packedUpper =
    packSparse (2 ^ 40) (targetRows 388) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 388) := by decide +kernel

theorem rowFacts388 : PackedRowFacts 388 := by
  constructor <;> decide +kernel

theorem upper389 : packedUpper 389 =
    packSparse (2 ^ 40) (upperRows 389) := by decide +kernel

theorem packed389 : packedProduct (lowerRows 389) packedUpper =
    packSparse (2 ^ 40) (targetRows 389) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 389) := by decide +kernel

theorem rowFacts389 : PackedRowFacts 389 := by
  constructor <;> decide +kernel

theorem upper390 : packedUpper 390 =
    packSparse (2 ^ 40) (upperRows 390) := by decide +kernel

theorem packed390 : packedProduct (lowerRows 390) packedUpper =
    packSparse (2 ^ 40) (targetRows 390) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 390) := by decide +kernel

theorem rowFacts390 : PackedRowFacts 390 := by
  constructor <;> decide +kernel

theorem upper391 : packedUpper 391 =
    packSparse (2 ^ 40) (upperRows 391) := by decide +kernel

theorem packed391 : packedProduct (lowerRows 391) packedUpper =
    packSparse (2 ^ 40) (targetRows 391) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 391) := by decide +kernel

theorem rowFacts391 : PackedRowFacts 391 := by
  constructor <;> decide +kernel

theorem upper392 : packedUpper 392 =
    packSparse (2 ^ 40) (upperRows 392) := by decide +kernel

theorem packed392 : packedProduct (lowerRows 392) packedUpper =
    packSparse (2 ^ 40) (targetRows 392) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 392) := by decide +kernel

theorem rowFacts392 : PackedRowFacts 392 := by
  constructor <;> decide +kernel

theorem upper393 : packedUpper 393 =
    packSparse (2 ^ 40) (upperRows 393) := by decide +kernel

theorem packed393 : packedProduct (lowerRows 393) packedUpper =
    packSparse (2 ^ 40) (targetRows 393) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 393) := by decide +kernel

theorem rowFacts393 : PackedRowFacts 393 := by
  constructor <;> decide +kernel

theorem upper394 : packedUpper 394 =
    packSparse (2 ^ 40) (upperRows 394) := by decide +kernel

theorem packed394 : packedProduct (lowerRows 394) packedUpper =
    packSparse (2 ^ 40) (targetRows 394) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 394) := by decide +kernel

theorem rowFacts394 : PackedRowFacts 394 := by
  constructor <;> decide +kernel

theorem upper395 : packedUpper 395 =
    packSparse (2 ^ 40) (upperRows 395) := by decide +kernel

theorem packed395 : packedProduct (lowerRows 395) packedUpper =
    packSparse (2 ^ 40) (targetRows 395) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 395) := by decide +kernel

theorem rowFacts395 : PackedRowFacts 395 := by
  constructor <;> decide +kernel

theorem upper396 : packedUpper 396 =
    packSparse (2 ^ 40) (upperRows 396) := by decide +kernel

theorem packed396 : packedProduct (lowerRows 396) packedUpper =
    packSparse (2 ^ 40) (targetRows 396) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 396) := by decide +kernel

theorem rowFacts396 : PackedRowFacts 396 := by
  constructor <;> decide +kernel

theorem upper397 : packedUpper 397 =
    packSparse (2 ^ 40) (upperRows 397) := by decide +kernel

theorem packed397 : packedProduct (lowerRows 397) packedUpper =
    packSparse (2 ^ 40) (targetRows 397) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 397) := by decide +kernel

theorem rowFacts397 : PackedRowFacts 397 := by
  constructor <;> decide +kernel

theorem upper398 : packedUpper 398 =
    packSparse (2 ^ 40) (upperRows 398) := by decide +kernel

theorem packed398 : packedProduct (lowerRows 398) packedUpper =
    packSparse (2 ^ 40) (targetRows 398) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 398) := by decide +kernel

theorem rowFacts398 : PackedRowFacts 398 := by
  constructor <;> decide +kernel

theorem upper399 : packedUpper 399 =
    packSparse (2 ^ 40) (upperRows 399) := by decide +kernel

theorem packed399 : packedProduct (lowerRows 399) packedUpper =
    packSparse (2 ^ 40) (targetRows 399) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 399) := by decide +kernel

theorem rowFacts399 : PackedRowFacts 399 := by
  constructor <;> decide +kernel

theorem upper400 : packedUpper 400 =
    packSparse (2 ^ 40) (upperRows 400) := by decide +kernel

theorem packed400 : packedProduct (lowerRows 400) packedUpper =
    packSparse (2 ^ 40) (targetRows 400) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 400) := by decide +kernel

theorem rowFacts400 : PackedRowFacts 400 := by
  constructor <;> decide +kernel

theorem upper401 : packedUpper 401 =
    packSparse (2 ^ 40) (upperRows 401) := by decide +kernel

theorem packed401 : packedProduct (lowerRows 401) packedUpper =
    packSparse (2 ^ 40) (targetRows 401) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 401) := by decide +kernel

theorem rowFacts401 : PackedRowFacts 401 := by
  constructor <;> decide +kernel

theorem upper402 : packedUpper 402 =
    packSparse (2 ^ 40) (upperRows 402) := by decide +kernel

theorem packed402 : packedProduct (lowerRows 402) packedUpper =
    packSparse (2 ^ 40) (targetRows 402) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 402) := by decide +kernel

theorem rowFacts402 : PackedRowFacts 402 := by
  constructor <;> decide +kernel

theorem upper403 : packedUpper 403 =
    packSparse (2 ^ 40) (upperRows 403) := by decide +kernel

theorem packed403 : packedProduct (lowerRows 403) packedUpper =
    packSparse (2 ^ 40) (targetRows 403) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 403) := by decide +kernel

theorem rowFacts403 : PackedRowFacts 403 := by
  constructor <;> decide +kernel

theorem upper404 : packedUpper 404 =
    packSparse (2 ^ 40) (upperRows 404) := by decide +kernel

theorem packed404 : packedProduct (lowerRows 404) packedUpper =
    packSparse (2 ^ 40) (targetRows 404) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 404) := by decide +kernel

theorem rowFacts404 : PackedRowFacts 404 := by
  constructor <;> decide +kernel

theorem upper405 : packedUpper 405 =
    packSparse (2 ^ 40) (upperRows 405) := by decide +kernel

theorem packed405 : packedProduct (lowerRows 405) packedUpper =
    packSparse (2 ^ 40) (targetRows 405) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 405) := by decide +kernel

theorem rowFacts405 : PackedRowFacts 405 := by
  constructor <;> decide +kernel

theorem upper406 : packedUpper 406 =
    packSparse (2 ^ 40) (upperRows 406) := by decide +kernel

theorem packed406 : packedProduct (lowerRows 406) packedUpper =
    packSparse (2 ^ 40) (targetRows 406) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 406) := by decide +kernel

theorem rowFacts406 : PackedRowFacts 406 := by
  constructor <;> decide +kernel

theorem upper407 : packedUpper 407 =
    packSparse (2 ^ 40) (upperRows 407) := by decide +kernel

theorem packed407 : packedProduct (lowerRows 407) packedUpper =
    packSparse (2 ^ 40) (targetRows 407) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 407) := by decide +kernel

theorem rowFacts407 : PackedRowFacts 407 := by
  constructor <;> decide +kernel

theorem upper408 : packedUpper 408 =
    packSparse (2 ^ 40) (upperRows 408) := by decide +kernel

theorem packed408 : packedProduct (lowerRows 408) packedUpper =
    packSparse (2 ^ 40) (targetRows 408) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 408) := by decide +kernel

theorem rowFacts408 : PackedRowFacts 408 := by
  constructor <;> decide +kernel

theorem upper409 : packedUpper 409 =
    packSparse (2 ^ 40) (upperRows 409) := by decide +kernel

theorem packed409 : packedProduct (lowerRows 409) packedUpper =
    packSparse (2 ^ 40) (targetRows 409) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 409) := by decide +kernel

theorem rowFacts409 : PackedRowFacts 409 := by
  constructor <;> decide +kernel

theorem upper410 : packedUpper 410 =
    packSparse (2 ^ 40) (upperRows 410) := by decide +kernel

theorem packed410 : packedProduct (lowerRows 410) packedUpper =
    packSparse (2 ^ 40) (targetRows 410) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 410) := by decide +kernel

theorem rowFacts410 : PackedRowFacts 410 := by
  constructor <;> decide +kernel

theorem upper411 : packedUpper 411 =
    packSparse (2 ^ 40) (upperRows 411) := by decide +kernel

theorem packed411 : packedProduct (lowerRows 411) packedUpper =
    packSparse (2 ^ 40) (targetRows 411) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 411) := by decide +kernel

theorem rowFacts411 : PackedRowFacts 411 := by
  constructor <;> decide +kernel

theorem upper412 : packedUpper 412 =
    packSparse (2 ^ 40) (upperRows 412) := by decide +kernel

theorem packed412 : packedProduct (lowerRows 412) packedUpper =
    packSparse (2 ^ 40) (targetRows 412) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 412) := by decide +kernel

theorem rowFacts412 : PackedRowFacts 412 := by
  constructor <;> decide +kernel

theorem upper413 : packedUpper 413 =
    packSparse (2 ^ 40) (upperRows 413) := by decide +kernel

theorem packed413 : packedProduct (lowerRows 413) packedUpper =
    packSparse (2 ^ 40) (targetRows 413) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 413) := by decide +kernel

theorem rowFacts413 : PackedRowFacts 413 := by
  constructor <;> decide +kernel

theorem upper414 : packedUpper 414 =
    packSparse (2 ^ 40) (upperRows 414) := by decide +kernel

theorem packed414 : packedProduct (lowerRows 414) packedUpper =
    packSparse (2 ^ 40) (targetRows 414) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 414) := by decide +kernel

theorem rowFacts414 : PackedRowFacts 414 := by
  constructor <;> decide +kernel

theorem upper415 : packedUpper 415 =
    packSparse (2 ^ 40) (upperRows 415) := by decide +kernel

theorem packed415 : packedProduct (lowerRows 415) packedUpper =
    packSparse (2 ^ 40) (targetRows 415) +
      1009 * Nat.ofDigits (2 ^ 40) (quotientRows 415) := by decide +kernel

theorem rowFacts415 : PackedRowFacts 415 := by
  constructor <;> decide +kernel

#print axioms packed415

end CertifiedRank.C2.PackedCertificate
