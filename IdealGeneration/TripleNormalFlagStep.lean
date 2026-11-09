module

public import IdealGeneration.TripleNormalFlags
public import IdealGeneration.TripleNormalConicRows
public import IdealGeneration.TripleNormalMiddleKernel
public import IdealGeneration.TripleNormalExtensionKernel
public import IdealGeneration.TripleNormalNewBlockKernel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The actual three-normal flag enlargement from its base evaluation rank. -/

noncomputable section
namespace IdealGeneration.TripleNormal

open ConeParameterSpace ConeMiddleFamily SupportedQuadrics

variable {K : Type*} [Field K] {ω : K} {h : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The old square, new base rank, and scalar trace rank give the next
supported flag with its actual middle multiplication injective. -/
def FlagWitness.extend_of_newBaseRank (F : FlagWitness K ω h) (hh : 6 ≤ h)
    (u : Fin 3 → K) (free : Fin (2 * h + 5) × Fin (h + 3) → K) (η : Fin 4 → K)
    (ht : ∀ i, Fin.append F.t u i ≠ 0)
    (htinj : Function.Injective (Fin.append F.t u))
    (hchord : ∀ i j, i ≠ j → chordFactor (Fin.append F.t u i) (Fin.append F.t u j) ≠ 0)
    (hη : ∀ j, η j ≠ 0) (hbase : NewBaseRank ω F.t u free)
    (htrace : Function.Surjective (representativeEvaluation K (F.extendedCone u free η).trace 2)) :
    FlagWitness K ω (h + 3) := by
  let normal := fun j => baseNormal ω (u j)
  let C' := F.extendedCone u free η
  let P' := supportedExtension_pointPattern F.cone free η ω F.t u F.layerNormals
    F.layerHeights hh F.pattern
  let L := pureLift F.cone ω F.t F.layerNormals F.layerHeights (Layer.baseSupport K h)
    F.pattern F.primitive F.base_nonzero F.layer_det F.layer_nonzero
  let L' := pureLift C' ω (Fin.append F.t u) F.layerNormals F.layerHeights
    (Layer.baseSupport K (h + 3)) P' F.primitive ht F.layer_det F.layer_nonzero
  have hL (Q : Forms K 3 2) : quadraticRestriction F.cone (L Q) = Q :=
    pureRestrict_pureLift F.cone ω F.t F.layerNormals F.layerHeights (Layer.baseSupport K h)
      F.pattern F.primitive F.base_nonzero F.layer_det F.layer_nonzero Q
  have hL' (Q : Forms K 3 2) : quadraticRestriction C' (L' Q) = Q :=
    pureRestrict_pureLift C' ω (Fin.append F.t u) F.layerNormals F.layerHeights
      (Layer.baseSupport K (h + 3)) P' F.primitive ht F.layer_det F.layer_nonzero Q
  have hcompat (Q : Forms K 3 2) :
      supportedExtensionResidualRestriction F.cone free η normal 2 (L' Q) = L Q :=
    residualRestriction_pureLift F.cone free η normal ω F.t u F.layerNormals F.layerHeights
      F.pattern P' F.primitive F.base_nonzero ht F.layer_det F.layer_nonzero hh Q
  have hheight (i : Fin (flagConeCount h + 6)) : C'.height i ≠ 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (supportedExtension F.cone free η normal).height (j.castAdd 6) ≠ 0
      rw [supportedExtension_height_old]
      exact F.height_nonzero j
    · change Fin.append F.cone.height (fun _ : Fin 6 => (1 : K))
        (j.natAdd (flagConeCount h)) ≠ 0
      rw [Fin.append_right]
      exact one_ne_zero
  have hu : Function.Injective u := by
    intro i j he
    apply (Fin.natAdd_inj h).mp
    apply htinj
    simpa only [Fin.append_right] using he
  have hnormal : Function.Surjective (normalEvaluation C'.support (encode C') 2) :=
    supportedExtension_normalEvaluation_surjective F.cone free η normal F.normal_surjective
      (fun b => newNormalRowMap_conic_surjective ω u F.primitive b
        (by simpa only [Fin.append_right] using ht (b.natAdd h)))
  have hold := (middle_injective_iff_allowedEvaluation F.cone L hL F.height_nonzero).mp
    F.middle_injective
  have hnew : Function.Injective (allowedEvaluationMap C' L' hL' hheight) :=
    supportedExtension_allowedEvaluation_injective F.cone free η normal L L' hcompat hL hL'
      F.height_nonzero hheight hold
      (fun x hR hD => supportedExtension_newBlock_zero F.cone free η normal ω F.t u
        F.layerNormals F.layerHeights F.pattern P' F.primitive F.base_nonzero ht F.layer_det
        F.layer_nonzero hh hu hη hheight hbase x hR hD)
  have hmiddle := (middle_injective_iff_allowedEvaluation C' L' hL' hheight).mpr hnew
  exact F.extend hh u free η ht htinj hchord hnormal htrace hmiddle

end IdealGeneration.TripleNormal
