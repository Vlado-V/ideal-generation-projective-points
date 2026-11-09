module

public import IdealGeneration.CubicPairCoreSamples

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Canonical pair-block data from the freely chosen local C.3 samples. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open QuadraticTraceRestriction

variable {K : Type*} [Field K] {k : ℕ}

/-- Read the thirteen shared seven-coordinate samples in the canonical C.3 order. -/
def pairBlockDataOfLocalSamples (j : Fin k) (sample : Fin 13 × Fin 7 → K)
    (faceParameter : PairFullFace k j → K) (hface : ∀ F, faceParameter F ≠ 0) : PairBlockData K k j where
  point r := extendPoint K (pairC3TraceEmbedding j) (fun i => sample (r, Fin.castAdd 2 i))
  weight r b := sample (r, Fin.natAdd 5 b)
  supported r i hi := by
    apply extendPoint_off
    rintro ⟨a, rfl⟩
    exact hi (pairC3Trace_mem_pairSupport j a)
  coreColumn := canonicalPairCoreColumn j
  coreOwner := canonicalPairCoreColumn_owner j
  faceParameter := faceParameter
  faceParameter_ne := hface

@[simp] theorem pairC3Point_pairBlockDataOfLocalSamples (j : Fin k) (sample : Fin 13 × Fin 7 → K)
    (faceParameter : PairFullFace k j → K) (hface : ∀ F, faceParameter F ≠ 0) (r : Fin 13) (i : Fin 7) :
    pairC3Point j ((pairBlockDataOfLocalSamples j sample faceParameter hface).point r)
      ((pairBlockDataOfLocalSamples j sample faceParameter hface).weight r) i = sample (r, i) := by
  refine Fin.addCases (m := 5) (n := 2) (fun a => ?_) (fun b => ?_) i
  · rw [pairC3Point, Fin.addCases_left]
    exact extendPoint_embedded K (pairC3TraceEmbedding j) _ a
  · simp [pairC3Point, pairBlockDataOfLocalSamples]

end IdealGeneration.CubicSupported.B5
