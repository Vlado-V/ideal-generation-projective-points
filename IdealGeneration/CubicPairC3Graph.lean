module

public import IdealGeneration.CubicPairCoreSamples
public import IdealGeneration.CubicSupportedC3

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The induced C.3 graph inside a B.5 pair. -/

namespace IdealGeneration.CubicSupported.B5

variable {k : ℕ}

/-- Transfer an increasing edge of the C.3 graph to the enlarged trace space. -/
def pairC3Edge (j : Fin k) (e : Edge 7) : Edge ((10 + 2 * k) + 2) :=
  ⟨(pairC3Ambient j e.val.1, pairC3Ambient j e.val.2), pairC3Ambient_strictMono j e.property⟩

set_option maxHeartbeats 1300000 in
/-- The induced graph has precisely the two C.3 single edges. -/
theorem pairC3Edge_single (j : Fin k) (e : Edge 7) :
    single (pairC3Edge j e) = c3Parameters.single e := by
  have hj := j.isLt
  obtain ⟨⟨a, b⟩, hab⟩ := e
  change a.val < b.val at hab
  fin_cases a <;> fin_cases b
  all_goals norm_num at hab
  all_goals simp [pairC3Edge, single, c3Parameters, CubicPair.singleEdge,
    pairC3Ambient, pairC3Trace, Fin.addCases, singleLabels, pairA, pairB]
  all_goals omega

@[simp] theorem pairC3Edge_one (j : Fin k) :
    pairC3Edge j c3PairEdgeOne = newSlopeEdge 0 (activePairVertex j 0) := rfl

@[simp] theorem pairC3Edge_two (j : Fin k) :
    pairC3Edge j c3PairEdgeTwo = newSlopeEdge 1 (activePairVertex j 1) := rfl

end IdealGeneration.CubicSupported.B5
