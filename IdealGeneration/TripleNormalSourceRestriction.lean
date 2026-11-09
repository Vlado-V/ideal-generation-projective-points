module

public import IdealGeneration.TripleNormalSourceCoordinates
public import IdealGeneration.TripleNormalExtensionMaps
public import IdealGeneration.TripleNormalResidualRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # The supported source restriction in the conic and layer coordinates -/

noncomputable section
namespace IdealGeneration.TripleNormal.SupportedQuadrics
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

variable {K : Type*} [Field K] {h p q r : ℕ}
  (C : ConeConfiguration K 3 (h + 4) p q)
  (a : Fin r × Fin (h + 3) → K) (η : Fin 4 → K)
  (normal : Fin 3 → Fin 2 → Fin 3 → K)
  (ω : K) (t : Fin h → K) (u : Fin 3 → K)
  (n : Layer.Normals K) (ζ : Layer.Heights K)
  (oldPoints : PointPattern C ω t n ζ (Layer.baseSupport K h))
  (newPoints : PointPattern (supportedExtension C a η normal) ω (Fin.append t u)
    n ζ (Layer.baseSupport K (h + 3)))
  (hω : IsPrimitiveRoot ω 3)
  (ht : ∀ i, t i ≠ 0) (htu : ∀ i, Fin.append t u i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0)
  (hζ : ∀ j ν, ζ j ν ≠ 0) (hh : 6 ≤ h)

local notation "Cnew" => supportedExtension C a η normal
local notation "Eold" => residualEquiv C ω t n ζ (Layer.baseSupport K h)
  oldPoints hω ht hdet hζ
local notation "Enew" => residualEquiv Cnew ω (Fin.append t u)
  n ζ (Layer.baseSupport K (h + 3)) newPoints hω htu hdet hζ
local notation "hEold" => residualEquiv_fst C ω t n ζ (Layer.baseSupport K h)
  oldPoints hω ht hdet hζ
local notation "hEnew" => residualEquiv_fst Cnew ω (Fin.append t u)
  n ζ (Layer.baseSupport K (h + 3)) newPoints hω htu hdet hζ
local notation "Esource" => evaluationSourceCoordinatesEquiv C Eold hEold
local notation "EsourceNew" => evaluationSourceCoordinatesEquiv Cnew Enew hEnew
local notation "R₂" => supportedExtensionResidualRestriction C a η normal 2
local notation "R" => supportedExtensionEvaluationSourceRestriction C a η normal

include hh in
/-- Restricting the actual lifted source deletes exactly the five new blocks. -/
theorem supportedEvaluationSourceRestriction_coordinates (x : EvaluationSource Cnew) :
    Esource (R x) = sourceCoordinateRestriction h (EsourceNew x) :=
  evaluationSourceRestriction_coordinates R₂ R Eold Enew hEold hEnew
    (residualEquiv_residualRestriction C a η normal ω t u n ζ oldPoints newPoints
      hω ht htu hdet hζ hh) (fun _ _ => rfl) (fun _ _ => rfl) x

local notation "hcoords" => supportedEvaluationSourceRestriction_coordinates
  C a η normal ω t u n ζ oldPoints newPoints hω ht htu hdet hζ hh

include oldPoints newPoints hω ht htu hdet hζ hh in
/-- The A.4 supported source restriction is onto for the actual lifts. -/
theorem supportedEvaluationSourceRestriction_surjective : Function.Surjective R :=
  evaluationSourceRestriction_surjective R Esource EsourceNew hcoords

/-- The A.4 supported restriction kernel in the actual conic and layer coordinates. -/
def supportedEvaluationSourceRestrictionKernelEquiv :
    (R).ker ≃ₗ[K] NewSourceCoordinates K h :=
  evaluationSourceRestrictionKernelEquiv R Esource EsourceNew hcoords

include oldPoints newPoints hω ht htu hdet hζ hh in
/-- The five blocks of the supported restriction kernel have the dimension
of the new coefficient system in the enlargement. -/
theorem finrank_supportedEvaluationSourceRestriction_ker :
    Module.finrank K (R).ker = 6 * h + 30 :=
  finrank_evaluationSourceRestriction_ker R Esource EsourceNew hcoords

end IdealGeneration.TripleNormal.SupportedQuadrics
