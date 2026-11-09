module

public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows000
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows008
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows016
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows024
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows032
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows040
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows048
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows056
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows064
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows072
public import IdealGeneration.CubicB7RootFormulaChecks.Block0Rows080
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows000
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows008
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows016
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows024
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows032
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows040
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows048
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows056
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows064
public import IdealGeneration.CubicB7RootFormulaChecks.Block1Rows072

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicSupported.B7Root

open B7RootCertificate CubicRationalFormula
local instance : Fact (Nat.Prime 1009) := ⟨by decide +kernel⟩

theorem formula0_eq_mod :
    evalMatrix (fun _ => (0 : ZMod 1009)) formula0 = block0 := by
  ext i j
  rw [block0_apply]
  change (formula0 i j).eval _ = _
  by_cases h0 : i.val < 8
  · let t : Fin 8 := ⟨i.val - 0, by omega⟩
    have ht : (⟨0 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows000_eq t j
  by_cases h8 : i.val < 16
  · let t : Fin 8 := ⟨i.val - 8, by omega⟩
    have ht : (⟨8 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows008_eq t j
  by_cases h16 : i.val < 24
  · let t : Fin 8 := ⟨i.val - 16, by omega⟩
    have ht : (⟨16 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows016_eq t j
  by_cases h24 : i.val < 32
  · let t : Fin 8 := ⟨i.val - 24, by omega⟩
    have ht : (⟨24 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows024_eq t j
  by_cases h32 : i.val < 40
  · let t : Fin 8 := ⟨i.val - 32, by omega⟩
    have ht : (⟨32 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows032_eq t j
  by_cases h40 : i.val < 48
  · let t : Fin 8 := ⟨i.val - 40, by omega⟩
    have ht : (⟨40 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows040_eq t j
  by_cases h48 : i.val < 56
  · let t : Fin 8 := ⟨i.val - 48, by omega⟩
    have ht : (⟨48 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows048_eq t j
  by_cases h56 : i.val < 64
  · let t : Fin 8 := ⟨i.val - 56, by omega⟩
    have ht : (⟨56 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows056_eq t j
  by_cases h64 : i.val < 72
  · let t : Fin 8 := ⟨i.val - 64, by omega⟩
    have ht : (⟨64 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows064_eq t j
  by_cases h72 : i.val < 80
  · let t : Fin 8 := ⟨i.val - 72, by omega⟩
    have ht : (⟨72 + t.val, by omega⟩ : Fin 86) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block0Rows072_eq t j
  let t : Fin 6 := ⟨i.val - 80, by omega⟩
  have ht : (⟨80 + t.val, by omega⟩ : Fin 86) = i := by
    apply Fin.ext
    dsimp [t]
    omega
  simpa only [ht] using block0Rows080_eq t j

theorem formula1_eq_mod :
    evalMatrix (fun _ => (0 : ZMod 1009)) formula1 = block1 := by
  ext i j
  rw [block1_apply]
  change (formula1 i j).eval _ = _
  by_cases h0 : i.val < 8
  · let t : Fin 8 := ⟨i.val - 0, by omega⟩
    have ht : (⟨0 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows000_eq t j
  by_cases h8 : i.val < 16
  · let t : Fin 8 := ⟨i.val - 8, by omega⟩
    have ht : (⟨8 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows008_eq t j
  by_cases h16 : i.val < 24
  · let t : Fin 8 := ⟨i.val - 16, by omega⟩
    have ht : (⟨16 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows016_eq t j
  by_cases h24 : i.val < 32
  · let t : Fin 8 := ⟨i.val - 24, by omega⟩
    have ht : (⟨24 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows024_eq t j
  by_cases h32 : i.val < 40
  · let t : Fin 8 := ⟨i.val - 32, by omega⟩
    have ht : (⟨32 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows032_eq t j
  by_cases h40 : i.val < 48
  · let t : Fin 8 := ⟨i.val - 40, by omega⟩
    have ht : (⟨40 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows040_eq t j
  by_cases h48 : i.val < 56
  · let t : Fin 8 := ⟨i.val - 48, by omega⟩
    have ht : (⟨48 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows048_eq t j
  by_cases h56 : i.val < 64
  · let t : Fin 8 := ⟨i.val - 56, by omega⟩
    have ht : (⟨56 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows056_eq t j
  by_cases h64 : i.val < 72
  · let t : Fin 8 := ⟨i.val - 64, by omega⟩
    have ht : (⟨64 + t.val, by omega⟩ : Fin 74) = i := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa only [ht] using block1Rows064_eq t j
  let t : Fin 2 := ⟨i.val - 72, by omega⟩
  have ht : (⟨72 + t.val, by omega⟩ : Fin 74) = i := by
    apply Fin.ext
    dsimp [t]
    omega
  simpa only [ht] using block1Rows072_eq t j

end IdealGeneration.CubicSupported.B7Root
