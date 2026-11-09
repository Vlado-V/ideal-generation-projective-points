module

public import IdealGeneration.CubicInitialMiddleFacts
public import IdealGeneration.CubicInitialSparseComparison

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 2048

namespace IdealGeneration.CubicInitial
open ConeMonomialChart CertifiedRank

theorem middleRowCertificate640 : MiddleRowCertificate 640 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate641 : MiddleRowCertificate 641 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate642 : MiddleRowCertificate 642 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate643 : MiddleRowCertificate 643 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate644 : MiddleRowCertificate 644 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate645 : MiddleRowCertificate 645 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate646 : MiddleRowCertificate 646 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate647 : MiddleRowCertificate 647 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate648 : MiddleRowCertificate 648 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl

theorem middleRowCertificate649 : MiddleRowCertificate 649 := by
  constructor
  · decide +kernel
  · decide +kernel
  · rw [rawMiddleRow_eq_sparse]
    rfl


end IdealGeneration.CubicInitial
