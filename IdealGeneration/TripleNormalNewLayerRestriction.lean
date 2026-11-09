module

public import IdealGeneration.TripleNormalNewLayerProducts
public import IdealGeneration.TripleNormalExtensionMaps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The twelve layer products lie in the kernel of the actual source restriction. -/

noncomputable section
namespace IdealGeneration.TripleNormal.NewLayerBlock
open SupportedQuadrics

variable {K : Type*} [Field K] {h p q r : ℕ}
variable (C : ConeConfiguration K 3 (h + 4) p q)
  (a : Fin r × Fin (h + 3) → K) (ζnew : Fin 4 → K) (nnew : Fin 3 → Fin 2 → Fin 3 → K)

variable (ω : K) (t : Fin h → K) (u : Fin 3 → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
  (points : PointPattern (supportedExtension C a ζnew nnew) ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)))
  (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, Fin.append t u i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)

local notation "H" => mixedEquiv (supportedExtension C a ζnew nnew) ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)) points hω ht hdet hζ
local notation "R" => supportedExtensionMixedRestriction C a ζnew nnew
local notation "Scol" => layerColumnSource (supportedExtension C a ζnew nnew) ω t u n ζ points hω ht hdet hζ
local notation "S" => layerMixedSource (supportedExtension C a ζnew nnew) ω t u n ζ points hω ht hdet hζ

include points in
theorem mixedRestriction_newMixed (hh : 6 ≤ h) (b : Fin 3) :
    R (H (Pi.single (b.natAdd h) 1)) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change extensionAmbientRestriction h
    (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
      (0, Pi.single (b.natAdd h) 1)).val = 0
  exact congrArg Subtype.val (restrict_newMixedForm ω t u n ζ hh b)

include points in
private theorem mixedRestriction_layerColumn (hh : 6 ≤ h) (b : Fin 3) (j : Fin 4)
    (k : Fin (h + 3 + 4)) : R (Scol b j k) = 0 := by
  by_cases hk : k = layerVariable h j
  · subst k
    simp [layerColumnSource, mixedRestriction_newMixed C a ζnew nnew ω t u n ζ points hω ht hdet hζ hh]
  · simp [layerColumnSource, Pi.single_eq_of_ne hk]

include points in
/-- The actual reduced-source restriction annihilates the new layer block. -/
theorem sourceRestriction_layerMixedSource (hh : 6 ≤ h) (c : Fin 4 → Fin 3 → K) :
    supportedExtensionEvaluationSourceRestriction C a ζnew nnew (0, S c) = 0 := by
  apply Prod.ext
  · change supportedExtensionOmegaRestriction C a ζnew nnew 0 = 0
    exact map_zero _
  · funext i
    change R (S c (oldTraceIndex h i)) = 0
    simp only [layerMixedSource, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
      Pi.smul_apply, map_sum, map_smul,
      mixedRestriction_layerColumn C a ζnew nnew ω t u n ζ points hω ht hdet hζ hh,
      smul_zero, Finset.sum_const_zero]

end IdealGeneration.TripleNormal.NewLayerBlock
