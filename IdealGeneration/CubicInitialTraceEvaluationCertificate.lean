module

public import IdealGeneration.CubicInitialTraceChecks000
public import IdealGeneration.CubicInitialTraceChecks024
public import IdealGeneration.CubicInitialTraceChecks048
public import IdealGeneration.CubicInitialTraceChecks072
public import IdealGeneration.CubicInitialTraceChecks096
public import IdealGeneration.CubicInitialTraceChecks120
public import IdealGeneration.CubicInitialTraceChecks144
public import IdealGeneration.CubicInitialTraceChecks168
public import IdealGeneration.CubicInitialTraceChecks192
public import IdealGeneration.CubicInitialTraceChecks216
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

private theorem tracePackAll : ∀ i, TracePackCertificate i := by
  refine forall_fin_of_rows (n := 220) ?_
  exact ⟨
    tracePack000, tracePack001, tracePack002, tracePack003, tracePack004, tracePack005,
    tracePack006, tracePack007, tracePack008, tracePack009, tracePack010, tracePack011,
    tracePack012, tracePack013, tracePack014, tracePack015, tracePack016, tracePack017,
    tracePack018, tracePack019, tracePack020, tracePack021, tracePack022, tracePack023,
    tracePack024, tracePack025, tracePack026, tracePack027, tracePack028, tracePack029,
    tracePack030, tracePack031, tracePack032, tracePack033, tracePack034, tracePack035,
    tracePack036, tracePack037, tracePack038, tracePack039, tracePack040, tracePack041,
    tracePack042, tracePack043, tracePack044, tracePack045, tracePack046, tracePack047,
    tracePack048, tracePack049, tracePack050, tracePack051, tracePack052, tracePack053,
    tracePack054, tracePack055, tracePack056, tracePack057, tracePack058, tracePack059,
    tracePack060, tracePack061, tracePack062, tracePack063, tracePack064, tracePack065,
    tracePack066, tracePack067, tracePack068, tracePack069, tracePack070, tracePack071,
    tracePack072, tracePack073, tracePack074, tracePack075, tracePack076, tracePack077,
    tracePack078, tracePack079, tracePack080, tracePack081, tracePack082, tracePack083,
    tracePack084, tracePack085, tracePack086, tracePack087, tracePack088, tracePack089,
    tracePack090, tracePack091, tracePack092, tracePack093, tracePack094, tracePack095,
    tracePack096, tracePack097, tracePack098, tracePack099, tracePack100, tracePack101,
    tracePack102, tracePack103, tracePack104, tracePack105, tracePack106, tracePack107,
    tracePack108, tracePack109, tracePack110, tracePack111, tracePack112, tracePack113,
    tracePack114, tracePack115, tracePack116, tracePack117, tracePack118, tracePack119,
    tracePack120, tracePack121, tracePack122, tracePack123, tracePack124, tracePack125,
    tracePack126, tracePack127, tracePack128, tracePack129, tracePack130, tracePack131,
    tracePack132, tracePack133, tracePack134, tracePack135, tracePack136, tracePack137,
    tracePack138, tracePack139, tracePack140, tracePack141, tracePack142, tracePack143,
    tracePack144, tracePack145, tracePack146, tracePack147, tracePack148, tracePack149,
    tracePack150, tracePack151, tracePack152, tracePack153, tracePack154, tracePack155,
    tracePack156, tracePack157, tracePack158, tracePack159, tracePack160, tracePack161,
    tracePack162, tracePack163, tracePack164, tracePack165, tracePack166, tracePack167,
    tracePack168, tracePack169, tracePack170, tracePack171, tracePack172, tracePack173,
    tracePack174, tracePack175, tracePack176, tracePack177, tracePack178, tracePack179,
    tracePack180, tracePack181, tracePack182, tracePack183, tracePack184, tracePack185,
    tracePack186, tracePack187, tracePack188, tracePack189, tracePack190, tracePack191,
    tracePack192, tracePack193, tracePack194, tracePack195, tracePack196, tracePack197,
    tracePack198, tracePack199, tracePack200, tracePack201, tracePack202, tracePack203,
    tracePack204, tracePack205, tracePack206, tracePack207, tracePack208, tracePack209,
    tracePack210, tracePack211, tracePack212, tracePack213, tracePack214, tracePack215,
    tracePack216, tracePack217, tracePack218, tracePack219
  ⟩

private theorem traceProductAll : ∀ i, TraceProductCertificate i := by
  refine forall_fin_of_rows (n := 165) ?_
  exact ⟨
    traceProduct000, traceProduct001, traceProduct002, traceProduct003, traceProduct004,
    traceProduct005, traceProduct006, traceProduct007, traceProduct008, traceProduct009,
    traceProduct010, traceProduct011, traceProduct012, traceProduct013, traceProduct014,
    traceProduct015, traceProduct016, traceProduct017, traceProduct018, traceProduct019,
    traceProduct020, traceProduct021, traceProduct022, traceProduct023, traceProduct024,
    traceProduct025, traceProduct026, traceProduct027, traceProduct028, traceProduct029,
    traceProduct030, traceProduct031, traceProduct032, traceProduct033, traceProduct034,
    traceProduct035, traceProduct036, traceProduct037, traceProduct038, traceProduct039,
    traceProduct040, traceProduct041, traceProduct042, traceProduct043, traceProduct044,
    traceProduct045, traceProduct046, traceProduct047, traceProduct048, traceProduct049,
    traceProduct050, traceProduct051, traceProduct052, traceProduct053, traceProduct054,
    traceProduct055, traceProduct056, traceProduct057, traceProduct058, traceProduct059,
    traceProduct060, traceProduct061, traceProduct062, traceProduct063, traceProduct064,
    traceProduct065, traceProduct066, traceProduct067, traceProduct068, traceProduct069,
    traceProduct070, traceProduct071, traceProduct072, traceProduct073, traceProduct074,
    traceProduct075, traceProduct076, traceProduct077, traceProduct078, traceProduct079,
    traceProduct080, traceProduct081, traceProduct082, traceProduct083, traceProduct084,
    traceProduct085, traceProduct086, traceProduct087, traceProduct088, traceProduct089,
    traceProduct090, traceProduct091, traceProduct092, traceProduct093, traceProduct094,
    traceProduct095, traceProduct096, traceProduct097, traceProduct098, traceProduct099,
    traceProduct100, traceProduct101, traceProduct102, traceProduct103, traceProduct104,
    traceProduct105, traceProduct106, traceProduct107, traceProduct108, traceProduct109,
    traceProduct110, traceProduct111, traceProduct112, traceProduct113, traceProduct114,
    traceProduct115, traceProduct116, traceProduct117, traceProduct118, traceProduct119,
    traceProduct120, traceProduct121, traceProduct122, traceProduct123, traceProduct124,
    traceProduct125, traceProduct126, traceProduct127, traceProduct128, traceProduct129,
    traceProduct130, traceProduct131, traceProduct132, traceProduct133, traceProduct134,
    traceProduct135, traceProduct136, traceProduct137, traceProduct138, traceProduct139,
    traceProduct140, traceProduct141, traceProduct142, traceProduct143, traceProduct144,
    traceProduct145, traceProduct146, traceProduct147, traceProduct148, traceProduct149,
    traceProduct150, traceProduct151, traceProduct152, traceProduct153, traceProduct154,
    traceProduct155, traceProduct156, traceProduct157, traceProduct158, traceProduct159,
    traceProduct160, traceProduct161, traceProduct162, traceProduct163, traceProduct164
  ⟩

/-- Actual trace evaluation times the two-block coefficient chart. -/
theorem traceEvaluation_factorization :
    traceResidueEvaluation.map (Nat.castRingHom (ZMod 1009)) *
      traceFactor.map (Nat.castRingHom (ZMod 1009)) =
        Matrix.map traceIdentityBlock (Nat.castRingHom (ZMod 1009)) := by
  apply checked_dense_product 1009 (2 ^ 40) (2 ^ 20)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ _ traceResidueEvaluation_lt ?_ ?_ tracePacked traceQuotient
    (fun i => (tracePackAll i).checked) (fun i => (traceProductAll i).checked)
  · intro i j
    exact Fin.addCases (motive := fun j : Fin (165 + 55) => traceFactor i j < 1009)
      (fun a => by
        rw [traceFactor, Fin.addCases_left]
        exact Nat.mod_lt _ (by decide))
      (fun b => by
        rw [traceFactor, Fin.addCases_right]
        exact Nat.mod_lt _ (by decide)) j
  · intro i j
    unfold traceIdentityBlock
    split <;> decide

end IdealGeneration.CubicInitial
