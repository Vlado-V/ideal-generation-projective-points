module

public import IdealGeneration.TripleNormalSupportedPattern
public import IdealGeneration.TripleNormalInitialPattern
public import IdealGeneration.ConeMiddleFamily
public import IdealGeneration.RepresentativeGeneric

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The supported quadratic flags in Appendix A.4 -/

noncomputable section
namespace IdealGeneration.TripleNormal

open ConeParameterSpace ConeMiddleFamily SupportedQuadrics
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- The number of cone points in the three-normal flag. -/
abbrev flagConeCount (h : ℕ) := 2 * h + 12

/-- The number of trace points in the three-normal flag. -/
abbrev flagTraceCount (h : ℕ) := (h + 4) * (h + 5) / 3

/-- The actual supported data retained during an enlargement. -/
structure FlagData (K : Type*) [Field K] (ω : K) (h p q : ℕ) where
  cone : ConeConfiguration K 3 (h + 4) p q
  t : Fin h → K
  layerNormals : Layer.Normals K
  layerHeights : Layer.Heights K
  primitive : IsPrimitiveRoot ω 3
  pattern : PointPattern cone ω t layerNormals layerHeights (Layer.baseSupport K h)
  base_nonzero : ∀ i, t i ≠ 0
  base_injective : Function.Injective t
  chord_nonzero : ∀ i j, i ≠ j → chordFactor (t i) (t j) ≠ 0
  layer_det : ∀ j, (Layer.normalMatrix layerNormals j).det ≠ 0
  layer_nonzero : ∀ j ν, layerHeights j ν ≠ 0
  height_nonzero : ∀ i, cone.height i ≠ 0
  normal_surjective : Function.Surjective (normalEvaluation cone.support (encode cone) 2)
  trace_surjective : Function.Surjective (representativeEvaluation K cone.trace 2)
  middle_injective : Function.Injective (cone.middleMultiplication 2)

/-- A supported flag with the exact two counts of the paper. -/
abbrev FlagWitness (K : Type*) [Field K] (ω : K) (h : ℕ) :=
  FlagData K ω h (flagConeCount h) (flagTraceCount h)

variable {K : Type*} [Field K] {ω : K} {h : ℕ}

theorem flagConeCount_add_three (h : ℕ) : flagConeCount (h + 3) = flagConeCount h + 6 := by
  unfold flagConeCount
  omega

theorem flagTraceCount_add_three (h : ℕ) :
    flagTraceCount (h + 3) = flagTraceCount h + (3 + ((2 * h + 5) + 4)) := by
  unfold flagTraceCount
  have he : (h + 3 + 4) * (h + 3 + 5) = (h + 4) * (h + 5) + 3 * (2 * h + 12) := by ring
  rw [he]
  omega

/-- The actual cone on the next flag, before rewriting the two point counts. -/
abbrev FlagWitness.extendedCone (F : FlagWitness K ω h) (u : Fin 3 → K)
    (a : Fin (2 * h + 5) × Fin (h + 3) → K) (η : Fin 4 → K) :=
  supportedExtension F.cone a η (fun j => baseNormal ω (u j))

/-- A new parameter choice with the required scalar and middle ranks gives
a flag at the next level, retaining the old layer data. -/
def FlagWitness.extend (F : FlagWitness K ω h) (hh : 6 ≤ h)
    (u : Fin 3 → K) (a : Fin (2 * h + 5) × Fin (h + 3) → K) (η : Fin 4 → K)
    (ht : ∀ i, Fin.append F.t u i ≠ 0)
    (htinj : Function.Injective (Fin.append F.t u))
    (hchord : ∀ i j, i ≠ j → chordFactor (Fin.append F.t u i) (Fin.append F.t u j) ≠ 0)
    (hnormal : Function.Surjective (normalEvaluation (F.extendedCone u a η).support
      (encode (F.extendedCone u a η)) 2))
    (htrace : Function.Surjective (representativeEvaluation K (F.extendedCone u a η).trace 2))
    (hmiddle : Function.Injective ((F.extendedCone u a η).middleMultiplication 2)) :
    FlagWitness K ω (h + 3) := by
  let C := F.extendedCone u a η
  have hheight (i : Fin (flagConeCount h + 6)) : C.height i ≠ 0 := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · change (supportedExtension F.cone a η (fun j => baseNormal ω (u j))).height
        (i.castAdd 6) ≠ 0
      rw [supportedExtension_height_old]
      exact F.height_nonzero i
    · change Fin.append F.cone.height (fun _ : Fin 6 => (1 : K)) (j.natAdd (flagConeCount h)) ≠ 0
      rw [Fin.append_right]
      exact one_ne_zero
  let G : FlagData K ω (h + 3) (flagConeCount h + 6)
      (flagTraceCount h + (3 + ((2 * h + 5) + 4))) :=
    { cone := C
      t := Fin.append F.t u
      layerNormals := F.layerNormals
      layerHeights := F.layerHeights
      primitive := F.primitive
      pattern := supportedExtension_pointPattern F.cone a η ω F.t u F.layerNormals
        F.layerHeights hh F.pattern
      base_nonzero := ht
      base_injective := htinj
      chord_nonzero := hchord
      layer_det := F.layer_det
      layer_nonzero := F.layer_nonzero
      height_nonzero := hheight
      normal_surjective := hnormal
      trace_surjective := htrace
      middle_injective := hmiddle }
  change FlagData K ω (h + 3) (flagConeCount (h + 3)) (flagTraceCount (h + 3))
  rw [flagConeCount_add_three, flagTraceCount_add_three]
  exact G

/-- The h=8 table data supply the actual first flag once its three finite
rank calculations have been checked. -/
def flagEight_of_ranks [CharZero K] (ω : K) (hω : IsPrimitiveRoot ω 3)
    (hnormal : Function.Surjective (normalEvaluation (TripleNormalInitial.configuration ω).support
      (encode (TripleNormalInitial.configuration ω)) 2))
    (htrace : Function.Surjective (representativeEvaluation K (TripleNormalInitial.configuration ω).trace 2))
    (hmiddle : Function.Injective ((TripleNormalInitial.configuration ω).middleMultiplication 2)) :
    FlagWitness K ω 8 where
  cone := TripleNormalInitial.configuration ω
  t := TripleNormalInitial.baseParameters K
  layerNormals := TripleNormalInitial.layerNormals K
  layerHeights := TripleNormalInitial.layerHeights K
  primitive := hω
  pattern := TripleNormalInitial.initialPointPattern ω
  base_nonzero := TripleNormalInitial.baseParameters_ne_zero
  base_injective := TripleNormalInitial.baseParameters_injective
  chord_nonzero := TripleNormalInitial.initial_chordFactor_ne_zero
  layer_det := TripleNormalInitial.layerNormalMatrix_det_ne_zero
  layer_nonzero := TripleNormalInitial.layerHeights_ne_zero
  height_nonzero := fun _ => one_ne_zero
  normal_surjective := hnormal
  trace_surjective := htrace
  middle_injective := hmiddle

end IdealGeneration.TripleNormal
