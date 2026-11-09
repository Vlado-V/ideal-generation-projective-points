module

public import IdealGeneration.CubicExtendedCert.Data

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

namespace IdealGeneration.CubicExtended

theorem evaluationRow000 : EvaluationRowAgrees 0 :=
  ⟨by decide +kernel⟩

theorem evaluationRow001 : EvaluationRowAgrees 1 :=
  ⟨by decide +kernel⟩

theorem evaluationRow002 : EvaluationRowAgrees 2 :=
  ⟨by decide +kernel⟩

theorem evaluationRow003 : EvaluationRowAgrees 3 :=
  ⟨by decide +kernel⟩

theorem evaluationRow004 : EvaluationRowAgrees 4 :=
  ⟨by decide +kernel⟩

theorem evaluationRow005 : EvaluationRowAgrees 5 :=
  ⟨by decide +kernel⟩

theorem evaluationRow006 : EvaluationRowAgrees 6 :=
  ⟨by decide +kernel⟩

theorem evaluationRow007 : EvaluationRowAgrees 7 :=
  ⟨by decide +kernel⟩

theorem evaluationRow008 : EvaluationRowAgrees 8 :=
  ⟨by decide +kernel⟩

theorem evaluationRow009 : EvaluationRowAgrees 9 :=
  ⟨by decide +kernel⟩

theorem evaluationRow010 : EvaluationRowAgrees 10 :=
  ⟨by decide +kernel⟩

theorem evaluationRow011 : EvaluationRowAgrees 11 :=
  ⟨by decide +kernel⟩

theorem evaluationRow012 : EvaluationRowAgrees 12 :=
  ⟨by decide +kernel⟩

theorem evaluationRow013 : EvaluationRowAgrees 13 :=
  ⟨by decide +kernel⟩

theorem evaluationRow014 : EvaluationRowAgrees 14 :=
  ⟨by decide +kernel⟩

theorem evaluationRow015 : EvaluationRowAgrees 15 :=
  ⟨by decide +kernel⟩

theorem evaluationRow016 : EvaluationRowAgrees 16 :=
  ⟨by decide +kernel⟩

theorem evaluationRow017 : EvaluationRowAgrees 17 :=
  ⟨by decide +kernel⟩

theorem evaluationRow018 : EvaluationRowAgrees 18 :=
  ⟨by decide +kernel⟩

theorem evaluationRow019 : EvaluationRowAgrees 19 :=
  ⟨by decide +kernel⟩

theorem evaluationRow020 : EvaluationRowAgrees 20 :=
  ⟨by decide +kernel⟩

end IdealGeneration.CubicExtended
