module

public import IdealGeneration.TripleNormalInitialPattern
public import IdealGeneration.TripleNormalConicRows
public import IdealGeneration.TripleNormalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Independent allowed-value constraints in the initial three-normal configuration. -/

noncomputable section
namespace IdealGeneration.TripleNormalInitial

open TripleNormal TripleNormal.SupportedQuadrics Matrix
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

private def assembleTraceValues (base : Fin 8 → Fin 3 → K) (layer : Fin 4 → Fin 3 → K) :
    Fin 3 → Fin 52 → K :=
  fun a => Fin.append (fun i => base i a) (Fin.append (0 : Fin 24 → K)
    (Fin.append (fun r : Fin 16 =>
      layer ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm r).1 a) (0 : Fin 4 → K)))

/-- Prescribe the two base values using the conic rows and the three
layer values using their invertible matrix. The remaining trace labels are free. -/
theorem initial_valueConstraint_surjective (ω : K) (hω : IsPrimitiveRoot ω 3) :
    Function.Surjective (valueConstraint (configuration ω)) := by
  classical
  intro target
  have hb (i : Fin 8) : ∃ v : Fin 3 → K,
      newNormalRowMap (fun _ => baseNormal ω (baseParameters K i)) 0 v =
        fun μ => target (baseConeIndex i μ) :=
    newNormalRowMap_conic_surjective ω (fun _ => baseParameters K i) hω 0
      (baseParameters_ne_zero i) _
  have hl (j : Fin 4) : ∃ v : Fin 3 → K,
      (Layer.normalMatrix (layerNormals K) j).mulVec v = fun ν => target (layerConeIndex j ν) :=
    (LinearMap.surjective_of_injective
      (f := (Layer.normalMatrix (layerNormals K) j).mulVecLin)
      (Matrix.mulVec_injective_of_det_ne_zero (layerNormalMatrix_det_ne_zero j))) _
  choose base hbase using hb
  choose layer hlayer using hl
  refine ⟨assembleTraceValues base layer, ?_⟩
  funext k
  change Fin (16 + 12) at k
  induction k using Fin.addCases with
  | left k =>
      obtain ⟨⟨i, μ⟩, rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin 16).surjective k
      change (∑ a, (configuration ω).normal (baseConeIndex i μ) a *
        assembleTraceValues base layer a (support (baseConeIndex i μ))) = target (baseConeIndex i μ)
      rw [configuration_normal_baseConeIndex, support_baseConeIndex]
      simpa only [assembleTraceValues, baseTraceIndex, Fin.append_left, newNormalRowMap_apply,
        dotProduct] using congrFun (hbase i) μ
  | right k =>
      obtain ⟨⟨j, ν⟩, rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).surjective k
      change (∑ a, (configuration ω).normal (layerConeIndex j ν) a *
        assembleTraceValues base layer a (support (layerConeIndex j ν))) = target (layerConeIndex j ν)
      rw [configuration_normal_layerConeIndex, support_layerConeIndex]
      simpa only [assembleTraceValues, layerTraceIndex, Fin.append_left, Fin.append_right,
        Equiv.symm_apply_apply, Matrix.mulVec, dotProduct, Layer.normalMatrix, Matrix.of_apply]
        using congrFun (hlayer j) ν

end IdealGeneration.TripleNormalInitial
