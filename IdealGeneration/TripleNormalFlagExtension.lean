module

public import IdealGeneration.TripleNormalFlags
public import IdealGeneration.TripleNormalNormalExtension

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The conic specialization of the flag extension -/

noncomputable section
namespace IdealGeneration.TripleNormal

open SupportedQuadrics Matrix ConeParameterSpace ConeMiddleFamily
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

variable {K : Type*} [Field K] {ω : K} {h : ℕ}

/-- The actual normal rows at a new conic pair have full row rank. -/
theorem newConicRows_surjective (hω : IsPrimitiveRoot ω 3) (u : Fin 3 → K)
    (b : Fin 3) (hu : u b ≠ 0) :
    Function.Surjective (newNormalRowMap (fun j => baseNormal ω (u j)) b) := by
  let s : Fin 2 → K := ![thetaPlus ω, thetaMinus ω]
  have hω₀ := hω.ne_zero (by decide : 3 ≠ 0)
  have hs (i : Fin 2) : s i ≠ 0 := by
    fin_cases i <;> simp [s, thetaPlus, thetaMinus, hω₀]
  intro y
  obtain ⟨x, hx⟩ := baseNormalMatrix_mulVec_surjective ω (u b) hω hu (fun i => y i / s i)
  refine ⟨x, ?_⟩
  funext i
  have hscale : newNormalRowMap (fun j => baseNormal ω (u j)) b x i =
      s i * (baseNormalMatrix ω (u b)).mulVec x i := by
    rw [newNormalRowMap_apply]
    fin_cases i <;>
      simp [s, baseNormal, baseNormalMatrix, Matrix.mulVec, smul_dotProduct, smul_eq_mul]
  rw [hscale, congrFun hx i]
  field_simp [hs i]

/-- For a conic flag the old scalar rank automatically extends to the new
cone points. Only the trace scalar and middle ranks remain to be supplied. -/
def FlagWitness.extend_of_trace_and_middle (F : FlagWitness K ω h) (hh : 6 ≤ h)
    (u : Fin 3 → K) (a : Fin (2 * h + 5) × Fin (h + 3) → K) (η : Fin 4 → K)
    (ht : ∀ i, Fin.append F.t u i ≠ 0)
    (htinj : Function.Injective (Fin.append F.t u))
    (hchord : ∀ i j, i ≠ j → chordFactor (Fin.append F.t u i) (Fin.append F.t u j) ≠ 0)
    (htrace : Function.Surjective (representativeEvaluation K (F.extendedCone u a η).trace 2))
    (hmiddle : Function.Injective ((F.extendedCone u a η).middleMultiplication 2)) :
    FlagWitness K ω (h + 3) := by
  have hu (b : Fin 3) : u b ≠ 0 := by
    simpa only [Fin.append_right] using ht (b.natAdd h)
  have hnormal := supportedExtension_normalEvaluation_surjective F.cone a η
    (fun j => baseNormal ω (u j)) F.normal_surjective
    (fun b => newConicRows_surjective F.primitive u b (hu b))
  exact F.extend hh u a η ht htinj hchord hnormal htrace hmiddle

end IdealGeneration.TripleNormal
