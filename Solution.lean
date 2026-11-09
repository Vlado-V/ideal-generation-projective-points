module

public import IdealGeneration.PalomarBridge
public import IdealGeneration.TheoremOneOne

@[expose] public section

namespace IdealGenerationPaper

/-- Theorem 1.1 for an algebraically closed field of characteristic zero. -/
theorem main_result {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    PalomarModel.IdealGeneration.TheoremOneOne K := by
  change _root_.IdealGeneration.TheoremOneOne K
  exact _root_.IdealGeneration.theorem_one_one

end IdealGenerationPaper
