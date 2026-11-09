module

public import IdealGeneration.CubicPairCoreMatch
public import IdealGeneration.QuadraticTraceRestriction
public import Mathlib.Order.Fin.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Placing the checked C.3 samples on the five coordinates of each pair. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicPair QuadraticTraceRestriction

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

/-- The local trace coordinates occur in their increasing C.3 order. -/
theorem pairC3Trace_strictMono (j : Fin k) : StrictMono (pairC3Trace j) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> simp [pairC3Trace, Fin.lt_def, pairA, pairB]
  all_goals omega

/-- The coordinate embedding for the C.3 pair samples. -/
def pairC3TraceEmbedding (j : Fin k) : Fin 5 ↪ Fin (10 + 2 * k) :=
  ⟨pairC3Trace j, (pairC3Trace_strictMono j).injective⟩

/-- The seven C.3 coordinates inside the ambient trace space after the pair addition. -/
def pairC3Ambient (j : Fin k) : Fin 7 → Fin ((10 + 2 * k) + 2) :=
  fun i => @Fin.addCases 5 2 (fun _ => Fin ((10 + 2 * k) + 2))
    (fun l => (pairC3Trace j l).castAdd 2) (Fin.natAdd (10 + 2 * k)) i

/-- The ambient coordinate map preserves the orientation of each edge. -/
theorem pairC3Ambient_strictMono (j : Fin k) : StrictMono (pairC3Ambient j) := by
  have hj := j.isLt
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> simp [pairC3Ambient, pairC3Trace, Fin.addCases, Fin.lt_def, pairA, pairB]
  all_goals omega

/-- The increasing embedding of the C.3 graph into the enlarged graph. -/
def pairC3AmbientEmbedding (j : Fin k) : Fin 7 ↪ Fin ((10 + 2 * k) + 2) :=
  ⟨pairC3Ambient j, (pairC3Ambient_strictMono j).injective⟩

@[simp] theorem pairC3Ambient_old (j : Fin k) (i : Fin 5) :
    pairC3Ambient j (Fin.castAdd 2 i) = (pairC3Trace j i).castAdd 2 := by
  rw [pairC3Ambient, Fin.addCases_left]

@[simp] theorem pairC3Ambient_new (j : Fin k) (b : Fin 2) :
    pairC3Ambient j (Fin.natAdd 5 b) = Fin.natAdd (10 + 2 * k) b := by
  rw [pairC3Ambient, Fin.addCases_right]

theorem pairC3Trace_mem_pairSupport (j : Fin k) (i : Fin 5) : pairC3Trace j i ∈ pairSupport j := by
  fin_cases i <;> simp [pairC3Trace, pairA, pairB]

/-- The literal C.3 rows, extended by zero outside the five-coordinate support. -/
def c3PairBlockData (K : Type*) [Field K] [CharZero K] (j : Fin k)
    (faceParameter : PairFullFace k j → K) (hface : ∀ F, faceParameter F ≠ 0) : PairBlockData K k j where
  point r := extendPoint K (pairC3TraceEmbedding j)
    (fun i : Fin 5 => (RationalConstruction.samplePointsQ r (Fin.castAdd 2 i) : K))
  weight r b := (RationalConstruction.samplePointsQ r (Fin.natAdd 5 b) : K)
  supported r i hi := by
    apply extendPoint_off
    rintro ⟨l, rfl⟩
    exact hi (pairC3Trace_mem_pairSupport j l)
  coreColumn := canonicalPairCoreColumn j
  coreOwner := canonicalPairCoreColumn_owner j
  faceParameter := faceParameter
  faceParameter_ne := hface

/-- Packing an extended C.3 probe recovers its original seven coordinates. -/
theorem pairC3Point_c3PairBlockData (j : Fin k)
    (faceParameter : PairFullFace k j → K) (hface : ∀ F, faceParameter F ≠ 0)
    (r : Fin 13) (i : Fin 7) :
    pairC3Point j ((c3PairBlockData K j faceParameter hface).point r)
      ((c3PairBlockData K j faceParameter hface).weight r) i =
      (RationalConstruction.samplePointsQ r i : K) := by
  refine Fin.addCases (m := 5) (n := 2) (fun l => ?_) (fun b => ?_) i
  · rw [pairC3Point, Fin.addCases_left]
    exact extendPoint_embedded K (pairC3TraceEmbedding j) _ l
  · simp [pairC3Point, c3PairBlockData]

/-- For the prescribed C.3 samples, only the actual lift factors and slopes
remain to be matched to the rational witness. -/
theorem c3PairBlockData_det_ne_zero
    (P : B7Data K (10 + 2 * k)) (j : Fin k)
    (faceParameter : PairFullFace k j → K) (hface : ∀ F, faceParameter F ≠ 0)
    (h : let D := c3PairBlockData K j faceParameter hface
      ∀ i r, PairC3LiftValues P j
        (fun a q l t => (RationalConstruction.restrictedLiftCoefficientsQ a q l t : K))
        (D.point i) (D.weight i) r)
    (h0 : pairC3Slope P j 0 = 810) (h1 : pairC3Slope P j 1 = 479) :
    (pairCoreMatrix P (c3PairBlockData K j faceParameter hface)).det ≠ 0 :=
  pairCoreMatrix_det_ne_zero_of_c3 P _ rfl h h0 h1 (pairC3Point_c3PairBlockData j faceParameter hface)

end IdealGeneration.CubicSupported.B5
