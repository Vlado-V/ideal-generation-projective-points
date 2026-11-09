module

public import IdealGeneration.CubicInitialNormalChecks000
public import IdealGeneration.CubicInitialNormalChecks024
public import IdealGeneration.CubicInitialNormalChecks048
public import IdealGeneration.CubicInitialNormalChecks072
public import IdealGeneration.CubicInitialNormalChecks096
public import IdealGeneration.CubicInitialNormalChecks120
public import IdealGeneration.CertifiedFinCases

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 2048

namespace IdealGeneration.CubicInitial
open CertifiedRank Matrix

private theorem normalPackAll : ∀ i, NormalPackCertificate i := by
  refine forall_fin_of_rows (n := 144) ?_
  exact ⟨
    normalPack000, normalPack001, normalPack002, normalPack003, normalPack004, normalPack005,
    normalPack006, normalPack007, normalPack008, normalPack009, normalPack010, normalPack011,
    normalPack012, normalPack013, normalPack014, normalPack015, normalPack016, normalPack017,
    normalPack018, normalPack019, normalPack020, normalPack021, normalPack022, normalPack023,
    normalPack024, normalPack025, normalPack026, normalPack027, normalPack028, normalPack029,
    normalPack030, normalPack031, normalPack032, normalPack033, normalPack034, normalPack035,
    normalPack036, normalPack037, normalPack038, normalPack039, normalPack040, normalPack041,
    normalPack042, normalPack043, normalPack044, normalPack045, normalPack046, normalPack047,
    normalPack048, normalPack049, normalPack050, normalPack051, normalPack052, normalPack053,
    normalPack054, normalPack055, normalPack056, normalPack057, normalPack058, normalPack059,
    normalPack060, normalPack061, normalPack062, normalPack063, normalPack064, normalPack065,
    normalPack066, normalPack067, normalPack068, normalPack069, normalPack070, normalPack071,
    normalPack072, normalPack073, normalPack074, normalPack075, normalPack076, normalPack077,
    normalPack078, normalPack079, normalPack080, normalPack081, normalPack082, normalPack083,
    normalPack084, normalPack085, normalPack086, normalPack087, normalPack088, normalPack089,
    normalPack090, normalPack091, normalPack092, normalPack093, normalPack094, normalPack095,
    normalPack096, normalPack097, normalPack098, normalPack099, normalPack100, normalPack101,
    normalPack102, normalPack103, normalPack104, normalPack105, normalPack106, normalPack107,
    normalPack108, normalPack109, normalPack110, normalPack111, normalPack112, normalPack113,
    normalPack114, normalPack115, normalPack116, normalPack117, normalPack118, normalPack119,
    normalPack120, normalPack121, normalPack122, normalPack123, normalPack124, normalPack125,
    normalPack126, normalPack127, normalPack128, normalPack129, normalPack130, normalPack131,
    normalPack132, normalPack133, normalPack134, normalPack135, normalPack136, normalPack137,
    normalPack138, normalPack139, normalPack140, normalPack141, normalPack142, normalPack143
  ⟩

private theorem normalProductAll : ∀ i, NormalProductCertificate i := by
  refine forall_fin_of_rows (n := 108) ?_
  exact ⟨
    normalProduct000, normalProduct001, normalProduct002, normalProduct003, normalProduct004,
    normalProduct005, normalProduct006, normalProduct007, normalProduct008, normalProduct009,
    normalProduct010, normalProduct011, normalProduct012, normalProduct013, normalProduct014,
    normalProduct015, normalProduct016, normalProduct017, normalProduct018, normalProduct019,
    normalProduct020, normalProduct021, normalProduct022, normalProduct023, normalProduct024,
    normalProduct025, normalProduct026, normalProduct027, normalProduct028, normalProduct029,
    normalProduct030, normalProduct031, normalProduct032, normalProduct033, normalProduct034,
    normalProduct035, normalProduct036, normalProduct037, normalProduct038, normalProduct039,
    normalProduct040, normalProduct041, normalProduct042, normalProduct043, normalProduct044,
    normalProduct045, normalProduct046, normalProduct047, normalProduct048, normalProduct049,
    normalProduct050, normalProduct051, normalProduct052, normalProduct053, normalProduct054,
    normalProduct055, normalProduct056, normalProduct057, normalProduct058, normalProduct059,
    normalProduct060, normalProduct061, normalProduct062, normalProduct063, normalProduct064,
    normalProduct065, normalProduct066, normalProduct067, normalProduct068, normalProduct069,
    normalProduct070, normalProduct071, normalProduct072, normalProduct073, normalProduct074,
    normalProduct075, normalProduct076, normalProduct077, normalProduct078, normalProduct079,
    normalProduct080, normalProduct081, normalProduct082, normalProduct083, normalProduct084,
    normalProduct085, normalProduct086, normalProduct087, normalProduct088, normalProduct089,
    normalProduct090, normalProduct091, normalProduct092, normalProduct093, normalProduct094,
    normalProduct095, normalProduct096, normalProduct097, normalProduct098, normalProduct099,
    normalProduct100, normalProduct101, normalProduct102, normalProduct103, normalProduct104,
    normalProduct105, normalProduct106, normalProduct107
  ⟩

/-- Actual normal evaluation times the two-block coefficient chart. -/
theorem normalEvaluation_factorization :
    normalResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) *
      normalFactor.map (Nat.castRingHom (ZMod 1009)) =
        Matrix.map normalIdentityBlock (Nat.castRingHom (ZMod 1009)) := by
  apply checked_dense_product 1009 (2 ^ 40) (2 ^ 20)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ _ normalResidueEvaluation_lt ?_ ?_ normalPacked normalQuotient
    (fun i => (normalPackAll i).checked) (fun i => (normalProductAll i).checked)
  · intro i j
    exact Fin.addCases (motive := fun j : Fin (108 + 36) => normalFactor i j < 1009)
      (fun a => by
        rw [normalFactor, Fin.addCases_left]
        exact Nat.mod_lt _ (by decide))
      (fun b => by
        rw [normalFactor, Fin.addCases_right]
        exact Nat.mod_lt _ (by decide)) j
  · intro i j
    unfold normalIdentityBlock
    split <;> decide

end IdealGeneration.CubicInitial
