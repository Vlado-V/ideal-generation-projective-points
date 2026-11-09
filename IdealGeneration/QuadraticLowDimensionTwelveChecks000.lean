module

public import IdealGeneration.QuadraticLowDimensionTwelveData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Exact arithmetic checks for rows 0–95 of the twelve-variable certificate. -/

noncomputable section
namespace IdealGeneration.QuadraticLowDimension
open CertifiedRank
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024


theorem twelve_packed_row_0 :
    twelvePackedRows 0 = packedMinorResidueRow twelveMinor 2 1024 0 := by rfl

theorem twelve_packed_product_0 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 0) twelvePackedRows =
      1024 ^ (0 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 0) := by rfl

theorem twelve_packed_row_1 :
    twelvePackedRows 1 = packedMinorResidueRow twelveMinor 2 1024 1 := by rfl

theorem twelve_packed_product_1 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 1) twelvePackedRows =
      1024 ^ (1 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 1) := by rfl

theorem twelve_packed_row_2 :
    twelvePackedRows 2 = packedMinorResidueRow twelveMinor 2 1024 2 := by rfl

theorem twelve_packed_product_2 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 2) twelvePackedRows =
      1024 ^ (2 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 2) := by rfl

theorem twelve_packed_row_3 :
    twelvePackedRows 3 = packedMinorResidueRow twelveMinor 2 1024 3 := by rfl

theorem twelve_packed_product_3 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 3) twelvePackedRows =
      1024 ^ (3 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 3) := by rfl

theorem twelve_packed_row_4 :
    twelvePackedRows 4 = packedMinorResidueRow twelveMinor 2 1024 4 := by rfl

theorem twelve_packed_product_4 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 4) twelvePackedRows =
      1024 ^ (4 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 4) := by rfl

theorem twelve_packed_row_5 :
    twelvePackedRows 5 = packedMinorResidueRow twelveMinor 2 1024 5 := by rfl

theorem twelve_packed_product_5 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 5) twelvePackedRows =
      1024 ^ (5 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 5) := by rfl

theorem twelve_packed_row_6 :
    twelvePackedRows 6 = packedMinorResidueRow twelveMinor 2 1024 6 := by rfl

theorem twelve_packed_product_6 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 6) twelvePackedRows =
      1024 ^ (6 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 6) := by rfl

theorem twelve_packed_row_7 :
    twelvePackedRows 7 = packedMinorResidueRow twelveMinor 2 1024 7 := by rfl

theorem twelve_packed_product_7 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 7) twelvePackedRows =
      1024 ^ (7 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 7) := by rfl

theorem twelve_packed_row_8 :
    twelvePackedRows 8 = packedMinorResidueRow twelveMinor 2 1024 8 := by rfl

theorem twelve_packed_product_8 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 8) twelvePackedRows =
      1024 ^ (8 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 8) := by rfl

theorem twelve_packed_row_9 :
    twelvePackedRows 9 = packedMinorResidueRow twelveMinor 2 1024 9 := by rfl

theorem twelve_packed_product_9 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 9) twelvePackedRows =
      1024 ^ (9 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 9) := by rfl

theorem twelve_packed_row_10 :
    twelvePackedRows 10 = packedMinorResidueRow twelveMinor 2 1024 10 := by rfl

theorem twelve_packed_product_10 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 10) twelvePackedRows =
      1024 ^ (10 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 10) := by rfl

theorem twelve_packed_row_11 :
    twelvePackedRows 11 = packedMinorResidueRow twelveMinor 2 1024 11 := by rfl

theorem twelve_packed_product_11 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 11) twelvePackedRows =
      1024 ^ (11 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 11) := by rfl

theorem twelve_packed_row_12 :
    twelvePackedRows 12 = packedMinorResidueRow twelveMinor 2 1024 12 := by rfl

theorem twelve_packed_product_12 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 12) twelvePackedRows =
      1024 ^ (12 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 12) := by rfl

theorem twelve_packed_row_13 :
    twelvePackedRows 13 = packedMinorResidueRow twelveMinor 2 1024 13 := by rfl

theorem twelve_packed_product_13 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 13) twelvePackedRows =
      1024 ^ (13 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 13) := by rfl

theorem twelve_packed_row_14 :
    twelvePackedRows 14 = packedMinorResidueRow twelveMinor 2 1024 14 := by rfl

theorem twelve_packed_product_14 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 14) twelvePackedRows =
      1024 ^ (14 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 14) := by rfl

theorem twelve_packed_row_15 :
    twelvePackedRows 15 = packedMinorResidueRow twelveMinor 2 1024 15 := by rfl

theorem twelve_packed_product_15 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 15) twelvePackedRows =
      1024 ^ (15 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 15) := by rfl

theorem twelve_packed_row_16 :
    twelvePackedRows 16 = packedMinorResidueRow twelveMinor 2 1024 16 := by rfl

theorem twelve_packed_product_16 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 16) twelvePackedRows =
      1024 ^ (16 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 16) := by rfl

theorem twelve_packed_row_17 :
    twelvePackedRows 17 = packedMinorResidueRow twelveMinor 2 1024 17 := by rfl

theorem twelve_packed_product_17 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 17) twelvePackedRows =
      1024 ^ (17 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 17) := by rfl

theorem twelve_packed_row_18 :
    twelvePackedRows 18 = packedMinorResidueRow twelveMinor 2 1024 18 := by rfl

theorem twelve_packed_product_18 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 18) twelvePackedRows =
      1024 ^ (18 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 18) := by rfl

theorem twelve_packed_row_19 :
    twelvePackedRows 19 = packedMinorResidueRow twelveMinor 2 1024 19 := by rfl

theorem twelve_packed_product_19 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 19) twelvePackedRows =
      1024 ^ (19 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 19) := by rfl

theorem twelve_packed_row_20 :
    twelvePackedRows 20 = packedMinorResidueRow twelveMinor 2 1024 20 := by rfl

theorem twelve_packed_product_20 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 20) twelvePackedRows =
      1024 ^ (20 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 20) := by rfl

theorem twelve_packed_row_21 :
    twelvePackedRows 21 = packedMinorResidueRow twelveMinor 2 1024 21 := by rfl

theorem twelve_packed_product_21 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 21) twelvePackedRows =
      1024 ^ (21 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 21) := by rfl

theorem twelve_packed_row_22 :
    twelvePackedRows 22 = packedMinorResidueRow twelveMinor 2 1024 22 := by rfl

theorem twelve_packed_product_22 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 22) twelvePackedRows =
      1024 ^ (22 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 22) := by rfl

theorem twelve_packed_row_23 :
    twelvePackedRows 23 = packedMinorResidueRow twelveMinor 2 1024 23 := by rfl

theorem twelve_packed_product_23 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 23) twelvePackedRows =
      1024 ^ (23 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 23) := by rfl

theorem twelve_packed_row_24 :
    twelvePackedRows 24 = packedMinorResidueRow twelveMinor 2 1024 24 := by rfl

theorem twelve_packed_product_24 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 24) twelvePackedRows =
      1024 ^ (24 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 24) := by rfl

theorem twelve_packed_row_25 :
    twelvePackedRows 25 = packedMinorResidueRow twelveMinor 2 1024 25 := by rfl

theorem twelve_packed_product_25 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 25) twelvePackedRows =
      1024 ^ (25 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 25) := by rfl

theorem twelve_packed_row_26 :
    twelvePackedRows 26 = packedMinorResidueRow twelveMinor 2 1024 26 := by rfl

theorem twelve_packed_product_26 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 26) twelvePackedRows =
      1024 ^ (26 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 26) := by rfl

theorem twelve_packed_row_27 :
    twelvePackedRows 27 = packedMinorResidueRow twelveMinor 2 1024 27 := by rfl

theorem twelve_packed_product_27 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 27) twelvePackedRows =
      1024 ^ (27 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 27) := by rfl

theorem twelve_packed_row_28 :
    twelvePackedRows 28 = packedMinorResidueRow twelveMinor 2 1024 28 := by rfl

theorem twelve_packed_product_28 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 28) twelvePackedRows =
      1024 ^ (28 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 28) := by rfl

theorem twelve_packed_row_29 :
    twelvePackedRows 29 = packedMinorResidueRow twelveMinor 2 1024 29 := by rfl

theorem twelve_packed_product_29 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 29) twelvePackedRows =
      1024 ^ (29 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 29) := by rfl

theorem twelve_packed_row_30 :
    twelvePackedRows 30 = packedMinorResidueRow twelveMinor 2 1024 30 := by rfl

theorem twelve_packed_product_30 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 30) twelvePackedRows =
      1024 ^ (30 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 30) := by rfl

theorem twelve_packed_row_31 :
    twelvePackedRows 31 = packedMinorResidueRow twelveMinor 2 1024 31 := by rfl

theorem twelve_packed_product_31 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 31) twelvePackedRows =
      1024 ^ (31 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 31) := by rfl

theorem twelve_packed_row_32 :
    twelvePackedRows 32 = packedMinorResidueRow twelveMinor 2 1024 32 := by rfl

theorem twelve_packed_product_32 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 32) twelvePackedRows =
      1024 ^ (32 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 32) := by rfl

theorem twelve_packed_row_33 :
    twelvePackedRows 33 = packedMinorResidueRow twelveMinor 2 1024 33 := by rfl

theorem twelve_packed_product_33 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 33) twelvePackedRows =
      1024 ^ (33 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 33) := by rfl

theorem twelve_packed_row_34 :
    twelvePackedRows 34 = packedMinorResidueRow twelveMinor 2 1024 34 := by rfl

theorem twelve_packed_product_34 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 34) twelvePackedRows =
      1024 ^ (34 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 34) := by rfl

theorem twelve_packed_row_35 :
    twelvePackedRows 35 = packedMinorResidueRow twelveMinor 2 1024 35 := by rfl

theorem twelve_packed_product_35 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 35) twelvePackedRows =
      1024 ^ (35 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 35) := by rfl

theorem twelve_packed_row_36 :
    twelvePackedRows 36 = packedMinorResidueRow twelveMinor 2 1024 36 := by rfl

theorem twelve_packed_product_36 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 36) twelvePackedRows =
      1024 ^ (36 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 36) := by rfl

theorem twelve_packed_row_37 :
    twelvePackedRows 37 = packedMinorResidueRow twelveMinor 2 1024 37 := by rfl

theorem twelve_packed_product_37 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 37) twelvePackedRows =
      1024 ^ (37 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 37) := by rfl

theorem twelve_packed_row_38 :
    twelvePackedRows 38 = packedMinorResidueRow twelveMinor 2 1024 38 := by rfl

theorem twelve_packed_product_38 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 38) twelvePackedRows =
      1024 ^ (38 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 38) := by rfl

theorem twelve_packed_row_39 :
    twelvePackedRows 39 = packedMinorResidueRow twelveMinor 2 1024 39 := by rfl

theorem twelve_packed_product_39 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 39) twelvePackedRows =
      1024 ^ (39 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 39) := by rfl

theorem twelve_packed_row_40 :
    twelvePackedRows 40 = packedMinorResidueRow twelveMinor 2 1024 40 := by rfl

theorem twelve_packed_product_40 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 40) twelvePackedRows =
      1024 ^ (40 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 40) := by rfl

theorem twelve_packed_row_41 :
    twelvePackedRows 41 = packedMinorResidueRow twelveMinor 2 1024 41 := by rfl

theorem twelve_packed_product_41 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 41) twelvePackedRows =
      1024 ^ (41 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 41) := by rfl

theorem twelve_packed_row_42 :
    twelvePackedRows 42 = packedMinorResidueRow twelveMinor 2 1024 42 := by rfl

theorem twelve_packed_product_42 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 42) twelvePackedRows =
      1024 ^ (42 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 42) := by rfl

theorem twelve_packed_row_43 :
    twelvePackedRows 43 = packedMinorResidueRow twelveMinor 2 1024 43 := by rfl

theorem twelve_packed_product_43 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 43) twelvePackedRows =
      1024 ^ (43 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 43) := by rfl

theorem twelve_packed_row_44 :
    twelvePackedRows 44 = packedMinorResidueRow twelveMinor 2 1024 44 := by rfl

theorem twelve_packed_product_44 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 44) twelvePackedRows =
      1024 ^ (44 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 44) := by rfl

theorem twelve_packed_row_45 :
    twelvePackedRows 45 = packedMinorResidueRow twelveMinor 2 1024 45 := by rfl

theorem twelve_packed_product_45 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 45) twelvePackedRows =
      1024 ^ (45 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 45) := by rfl

theorem twelve_packed_row_46 :
    twelvePackedRows 46 = packedMinorResidueRow twelveMinor 2 1024 46 := by rfl

theorem twelve_packed_product_46 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 46) twelvePackedRows =
      1024 ^ (46 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 46) := by rfl

theorem twelve_packed_row_47 :
    twelvePackedRows 47 = packedMinorResidueRow twelveMinor 2 1024 47 := by rfl

theorem twelve_packed_product_47 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 47) twelvePackedRows =
      1024 ^ (47 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 47) := by rfl

theorem twelve_packed_row_48 :
    twelvePackedRows 48 = packedMinorResidueRow twelveMinor 2 1024 48 := by rfl

theorem twelve_packed_product_48 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 48) twelvePackedRows =
      1024 ^ (48 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 48) := by rfl

theorem twelve_packed_row_49 :
    twelvePackedRows 49 = packedMinorResidueRow twelveMinor 2 1024 49 := by rfl

theorem twelve_packed_product_49 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 49) twelvePackedRows =
      1024 ^ (49 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 49) := by rfl

theorem twelve_packed_row_50 :
    twelvePackedRows 50 = packedMinorResidueRow twelveMinor 2 1024 50 := by rfl

theorem twelve_packed_product_50 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 50) twelvePackedRows =
      1024 ^ (50 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 50) := by rfl

theorem twelve_packed_row_51 :
    twelvePackedRows 51 = packedMinorResidueRow twelveMinor 2 1024 51 := by rfl

theorem twelve_packed_product_51 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 51) twelvePackedRows =
      1024 ^ (51 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 51) := by rfl

theorem twelve_packed_row_52 :
    twelvePackedRows 52 = packedMinorResidueRow twelveMinor 2 1024 52 := by rfl

theorem twelve_packed_product_52 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 52) twelvePackedRows =
      1024 ^ (52 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 52) := by rfl

theorem twelve_packed_row_53 :
    twelvePackedRows 53 = packedMinorResidueRow twelveMinor 2 1024 53 := by rfl

theorem twelve_packed_product_53 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 53) twelvePackedRows =
      1024 ^ (53 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 53) := by rfl

theorem twelve_packed_row_54 :
    twelvePackedRows 54 = packedMinorResidueRow twelveMinor 2 1024 54 := by rfl

theorem twelve_packed_product_54 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 54) twelvePackedRows =
      1024 ^ (54 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 54) := by rfl

theorem twelve_packed_row_55 :
    twelvePackedRows 55 = packedMinorResidueRow twelveMinor 2 1024 55 := by rfl

theorem twelve_packed_product_55 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 55) twelvePackedRows =
      1024 ^ (55 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 55) := by rfl

theorem twelve_packed_row_56 :
    twelvePackedRows 56 = packedMinorResidueRow twelveMinor 2 1024 56 := by rfl

theorem twelve_packed_product_56 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 56) twelvePackedRows =
      1024 ^ (56 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 56) := by rfl

theorem twelve_packed_row_57 :
    twelvePackedRows 57 = packedMinorResidueRow twelveMinor 2 1024 57 := by rfl

theorem twelve_packed_product_57 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 57) twelvePackedRows =
      1024 ^ (57 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 57) := by rfl

theorem twelve_packed_row_58 :
    twelvePackedRows 58 = packedMinorResidueRow twelveMinor 2 1024 58 := by rfl

theorem twelve_packed_product_58 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 58) twelvePackedRows =
      1024 ^ (58 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 58) := by rfl

theorem twelve_packed_row_59 :
    twelvePackedRows 59 = packedMinorResidueRow twelveMinor 2 1024 59 := by rfl

theorem twelve_packed_product_59 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 59) twelvePackedRows =
      1024 ^ (59 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 59) := by rfl

theorem twelve_packed_row_60 :
    twelvePackedRows 60 = packedMinorResidueRow twelveMinor 2 1024 60 := by rfl

theorem twelve_packed_product_60 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 60) twelvePackedRows =
      1024 ^ (60 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 60) := by rfl

theorem twelve_packed_row_61 :
    twelvePackedRows 61 = packedMinorResidueRow twelveMinor 2 1024 61 := by rfl

theorem twelve_packed_product_61 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 61) twelvePackedRows =
      1024 ^ (61 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 61) := by rfl

theorem twelve_packed_row_62 :
    twelvePackedRows 62 = packedMinorResidueRow twelveMinor 2 1024 62 := by rfl

theorem twelve_packed_product_62 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 62) twelvePackedRows =
      1024 ^ (62 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 62) := by rfl

theorem twelve_packed_row_63 :
    twelvePackedRows 63 = packedMinorResidueRow twelveMinor 2 1024 63 := by rfl

theorem twelve_packed_product_63 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 63) twelvePackedRows =
      1024 ^ (63 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 63) := by rfl

theorem twelve_packed_row_64 :
    twelvePackedRows 64 = packedMinorResidueRow twelveMinor 2 1024 64 := by rfl

theorem twelve_packed_product_64 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 64) twelvePackedRows =
      1024 ^ (64 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 64) := by rfl

theorem twelve_packed_row_65 :
    twelvePackedRows 65 = packedMinorResidueRow twelveMinor 2 1024 65 := by rfl

theorem twelve_packed_product_65 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 65) twelvePackedRows =
      1024 ^ (65 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 65) := by rfl

theorem twelve_packed_row_66 :
    twelvePackedRows 66 = packedMinorResidueRow twelveMinor 2 1024 66 := by rfl

theorem twelve_packed_product_66 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 66) twelvePackedRows =
      1024 ^ (66 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 66) := by rfl

theorem twelve_packed_row_67 :
    twelvePackedRows 67 = packedMinorResidueRow twelveMinor 2 1024 67 := by rfl

theorem twelve_packed_product_67 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 67) twelvePackedRows =
      1024 ^ (67 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 67) := by rfl

theorem twelve_packed_row_68 :
    twelvePackedRows 68 = packedMinorResidueRow twelveMinor 2 1024 68 := by rfl

theorem twelve_packed_product_68 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 68) twelvePackedRows =
      1024 ^ (68 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 68) := by rfl

theorem twelve_packed_row_69 :
    twelvePackedRows 69 = packedMinorResidueRow twelveMinor 2 1024 69 := by rfl

theorem twelve_packed_product_69 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 69) twelvePackedRows =
      1024 ^ (69 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 69) := by rfl

theorem twelve_packed_row_70 :
    twelvePackedRows 70 = packedMinorResidueRow twelveMinor 2 1024 70 := by rfl

theorem twelve_packed_product_70 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 70) twelvePackedRows =
      1024 ^ (70 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 70) := by rfl

theorem twelve_packed_row_71 :
    twelvePackedRows 71 = packedMinorResidueRow twelveMinor 2 1024 71 := by rfl

theorem twelve_packed_product_71 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 71) twelvePackedRows =
      1024 ^ (71 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 71) := by rfl

theorem twelve_packed_row_72 :
    twelvePackedRows 72 = packedMinorResidueRow twelveMinor 2 1024 72 := by rfl

theorem twelve_packed_product_72 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 72) twelvePackedRows =
      1024 ^ (72 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 72) := by rfl

theorem twelve_packed_row_73 :
    twelvePackedRows 73 = packedMinorResidueRow twelveMinor 2 1024 73 := by rfl

theorem twelve_packed_product_73 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 73) twelvePackedRows =
      1024 ^ (73 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 73) := by rfl

theorem twelve_packed_row_74 :
    twelvePackedRows 74 = packedMinorResidueRow twelveMinor 2 1024 74 := by rfl

theorem twelve_packed_product_74 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 74) twelvePackedRows =
      1024 ^ (74 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 74) := by rfl

theorem twelve_packed_row_75 :
    twelvePackedRows 75 = packedMinorResidueRow twelveMinor 2 1024 75 := by rfl

theorem twelve_packed_product_75 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 75) twelvePackedRows =
      1024 ^ (75 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 75) := by rfl

theorem twelve_packed_row_76 :
    twelvePackedRows 76 = packedMinorResidueRow twelveMinor 2 1024 76 := by rfl

theorem twelve_packed_product_76 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 76) twelvePackedRows =
      1024 ^ (76 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 76) := by rfl

theorem twelve_packed_row_77 :
    twelvePackedRows 77 = packedMinorResidueRow twelveMinor 2 1024 77 := by rfl

theorem twelve_packed_product_77 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 77) twelvePackedRows =
      1024 ^ (77 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 77) := by rfl

theorem twelve_packed_row_78 :
    twelvePackedRows 78 = packedMinorResidueRow twelveMinor 2 1024 78 := by rfl

theorem twelve_packed_product_78 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 78) twelvePackedRows =
      1024 ^ (78 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 78) := by rfl

theorem twelve_packed_row_79 :
    twelvePackedRows 79 = packedMinorResidueRow twelveMinor 2 1024 79 := by rfl

theorem twelve_packed_product_79 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 79) twelvePackedRows =
      1024 ^ (79 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 79) := by rfl

theorem twelve_packed_row_80 :
    twelvePackedRows 80 = packedMinorResidueRow twelveMinor 2 1024 80 := by rfl

theorem twelve_packed_product_80 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 80) twelvePackedRows =
      1024 ^ (80 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 80) := by rfl

theorem twelve_packed_row_81 :
    twelvePackedRows 81 = packedMinorResidueRow twelveMinor 2 1024 81 := by rfl

theorem twelve_packed_product_81 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 81) twelvePackedRows =
      1024 ^ (81 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 81) := by rfl

theorem twelve_packed_row_82 :
    twelvePackedRows 82 = packedMinorResidueRow twelveMinor 2 1024 82 := by rfl

theorem twelve_packed_product_82 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 82) twelvePackedRows =
      1024 ^ (82 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 82) := by rfl

theorem twelve_packed_row_83 :
    twelvePackedRows 83 = packedMinorResidueRow twelveMinor 2 1024 83 := by rfl

theorem twelve_packed_product_83 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 83) twelvePackedRows =
      1024 ^ (83 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 83) := by rfl

theorem twelve_packed_row_84 :
    twelvePackedRows 84 = packedMinorResidueRow twelveMinor 2 1024 84 := by rfl

theorem twelve_packed_product_84 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 84) twelvePackedRows =
      1024 ^ (84 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 84) := by rfl

theorem twelve_packed_row_85 :
    twelvePackedRows 85 = packedMinorResidueRow twelveMinor 2 1024 85 := by rfl

theorem twelve_packed_product_85 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 85) twelvePackedRows =
      1024 ^ (85 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 85) := by rfl

theorem twelve_packed_row_86 :
    twelvePackedRows 86 = packedMinorResidueRow twelveMinor 2 1024 86 := by rfl

theorem twelve_packed_product_86 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 86) twelvePackedRows =
      1024 ^ (86 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 86) := by rfl

theorem twelve_packed_row_87 :
    twelvePackedRows 87 = packedMinorResidueRow twelveMinor 2 1024 87 := by rfl

theorem twelve_packed_product_87 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 87) twelvePackedRows =
      1024 ^ (87 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 87) := by rfl

theorem twelve_packed_row_88 :
    twelvePackedRows 88 = packedMinorResidueRow twelveMinor 2 1024 88 := by rfl

theorem twelve_packed_product_88 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 88) twelvePackedRows =
      1024 ^ (88 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 88) := by rfl

theorem twelve_packed_row_89 :
    twelvePackedRows 89 = packedMinorResidueRow twelveMinor 2 1024 89 := by rfl

theorem twelve_packed_product_89 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 89) twelvePackedRows =
      1024 ^ (89 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 89) := by rfl

theorem twelve_packed_row_90 :
    twelvePackedRows 90 = packedMinorResidueRow twelveMinor 2 1024 90 := by rfl

theorem twelve_packed_product_90 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 90) twelvePackedRows =
      1024 ^ (90 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 90) := by rfl

theorem twelve_packed_row_91 :
    twelvePackedRows 91 = packedMinorResidueRow twelveMinor 2 1024 91 := by rfl

theorem twelve_packed_product_91 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 91) twelvePackedRows =
      1024 ^ (91 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 91) := by rfl

theorem twelve_packed_row_92 :
    twelvePackedRows 92 = packedMinorResidueRow twelveMinor 2 1024 92 := by rfl

theorem twelve_packed_product_92 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 92) twelvePackedRows =
      1024 ^ (92 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 92) := by rfl

theorem twelve_packed_row_93 :
    twelvePackedRows 93 = packedMinorResidueRow twelveMinor 2 1024 93 := by rfl

theorem twelve_packed_product_93 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 93) twelvePackedRows =
      1024 ^ (93 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 93) := by rfl

theorem twelve_packed_row_94 :
    twelvePackedRows 94 = packedMinorResidueRow twelveMinor 2 1024 94 := by rfl

theorem twelve_packed_product_94 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 94) twelvePackedRows =
      1024 ^ (94 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 94) := by rfl

theorem twelve_packed_row_95 :
    twelvePackedRows 95 = packedMinorResidueRow twelveMinor 2 1024 95 := by rfl

theorem twelve_packed_product_95 :
    packedProduct (inverseSparseRow 2 twelvePackedInverse 95) twelvePackedRows =
      1024 ^ (95 : Fin 572).val + 2 * Nat.ofDigits 1024
        (inverseQuotientRow 32 twelvePackedQuotients 95) := by rfl

end IdealGeneration.QuadraticLowDimension
