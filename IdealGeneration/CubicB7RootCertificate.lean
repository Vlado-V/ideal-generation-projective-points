module

public import IdealGeneration.CubicB7RootCert.Checks0_000
public import IdealGeneration.CubicB7RootCert.Checks0_024
public import IdealGeneration.CubicB7RootCert.Checks0_048
public import IdealGeneration.CubicB7RootCert.Checks0_072
public import IdealGeneration.CubicB7RootCert.Checks1_000
public import IdealGeneration.CubicB7RootCert.Checks1_024
public import IdealGeneration.CubicB7RootCert.Checks1_048
public import IdealGeneration.CubicB7RootCert.Checks1_072
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace IdealGeneration.CubicSupported.B7RootCertificate

open CertifiedRank Matrix

private instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

private theorem inverse0_row_checks : ∀ i : Fin 86,
    InverseRowCertificate block0Rows inverse0Rows packedInverse0 quotient0Code i := by
  refine forall_fin_of_rows (n := 86) ?_
  exact ⟨
    cert0_000, cert0_001, cert0_002, cert0_003, cert0_004, cert0_005, cert0_006, cert0_007,
    cert0_008, cert0_009, cert0_010, cert0_011, cert0_012, cert0_013, cert0_014, cert0_015,
    cert0_016, cert0_017, cert0_018, cert0_019, cert0_020, cert0_021, cert0_022, cert0_023,
    cert0_024, cert0_025, cert0_026, cert0_027, cert0_028, cert0_029, cert0_030, cert0_031,
    cert0_032, cert0_033, cert0_034, cert0_035, cert0_036, cert0_037, cert0_038, cert0_039,
    cert0_040, cert0_041, cert0_042, cert0_043, cert0_044, cert0_045, cert0_046, cert0_047,
    cert0_048, cert0_049, cert0_050, cert0_051, cert0_052, cert0_053, cert0_054, cert0_055,
    cert0_056, cert0_057, cert0_058, cert0_059, cert0_060, cert0_061, cert0_062, cert0_063,
    cert0_064, cert0_065, cert0_066, cert0_067, cert0_068, cert0_069, cert0_070, cert0_071,
    cert0_072, cert0_073, cert0_074, cert0_075, cert0_076, cert0_077, cert0_078, cert0_079,
    cert0_080, cert0_081, cert0_082, cert0_083, cert0_084, cert0_085
  ⟩

theorem block0_mul_inverse : block0 * residueMatrix 1009 inverse0Rows = 1 :=
  checked_right_inverse block0Rows inverse0Rows packedInverse0 quotient0Code
    (by decide +kernel) inverse0_row_checks

/-- The listed B.7 root block is nonsingular over the residue field. -/
theorem block0_det_ne_zero : block0.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse block0_mul_inverse

theorem block0_rank : block0.rank = 86 := by
  simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero block0_det_ne_zero

#print axioms block0_det_ne_zero
#print axioms block0_rank

private theorem inverse1_row_checks : ∀ i : Fin 74,
    InverseRowCertificate block1Rows inverse1Rows packedInverse1 quotient1Code i := by
  refine forall_fin_of_rows (n := 74) ?_
  exact ⟨
    cert1_000, cert1_001, cert1_002, cert1_003, cert1_004, cert1_005, cert1_006, cert1_007,
    cert1_008, cert1_009, cert1_010, cert1_011, cert1_012, cert1_013, cert1_014, cert1_015,
    cert1_016, cert1_017, cert1_018, cert1_019, cert1_020, cert1_021, cert1_022, cert1_023,
    cert1_024, cert1_025, cert1_026, cert1_027, cert1_028, cert1_029, cert1_030, cert1_031,
    cert1_032, cert1_033, cert1_034, cert1_035, cert1_036, cert1_037, cert1_038, cert1_039,
    cert1_040, cert1_041, cert1_042, cert1_043, cert1_044, cert1_045, cert1_046, cert1_047,
    cert1_048, cert1_049, cert1_050, cert1_051, cert1_052, cert1_053, cert1_054, cert1_055,
    cert1_056, cert1_057, cert1_058, cert1_059, cert1_060, cert1_061, cert1_062, cert1_063,
    cert1_064, cert1_065, cert1_066, cert1_067, cert1_068, cert1_069, cert1_070, cert1_071,
    cert1_072, cert1_073
  ⟩

theorem block1_mul_inverse : block1 * residueMatrix 1009 inverse1Rows = 1 :=
  checked_right_inverse block1Rows inverse1Rows packedInverse1 quotient1Code
    (by decide +kernel) inverse1_row_checks

/-- The listed B.7 root block is nonsingular over the residue field. -/
theorem block1_det_ne_zero : block1.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse block1_mul_inverse

theorem block1_rank : block1.rank = 74 := by
  simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero block1_det_ne_zero

#print axioms block1_det_ne_zero
#print axioms block1_rank


end IdealGeneration.CubicSupported.B7RootCertificate
