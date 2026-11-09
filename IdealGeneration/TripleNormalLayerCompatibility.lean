module

public import IdealGeneration.TripleNormalLayerLift
public import IdealGeneration.TripleNormalExtensionRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The layer-corrected quadratic lift commutes with deleting the new base coordinates. -/

noncomputable section
namespace IdealGeneration.TripleNormal.Layer

open MvPolynomial NormalDegree

variable {K : Type*} [Field K] {h : ℕ}

@[simp] private theorem restrict_X_base (i : Fin h) :
    extensionAmbientRestriction (K := K) h (X (((i.castAdd 3).castAdd 4).natAdd 3)) =
      X ((i.castAdd 4).natAdd 3) := by
  simpa only [oldAmbientIndex, Fin.addCases_right, oldTraceIndex_base] using
    extensionAmbientRestriction_X_old (K := K) (h := h) ((i.castAdd 4).natAdd 3)

@[simp] private theorem restrict_X_layer (j : Fin 4) :
    extensionAmbientRestriction (K := K) h (X ((j.natAdd (h + 3)).natAdd 3)) =
      X ((j.natAdd h).natAdd 3) := by
  simpa only [oldAmbientIndex, Fin.addCases_right, oldTraceIndex_layer] using
    extensionAmbientRestriction_X_old (K := K) (h := h) ((j.natAdd h).natAdd 3)

/-- The enlarged lift restricts to the original lift whenever the old base
coefficients are preserved. -/
theorem restrict_quadratic (n : Normals K) (ζ : Heights K) (hh : 6 ≤ h)
    (Q : Forms K 3 2) (A : Fin h → Fin 3 → K) (A' : Fin (h + 3) → Fin 3 → K)
    (hA : ∀ i : Fin h, A' (i.castAdd 3) = A i) :
    extensionAmbientRestrictionForm h 2 (quadratic n ζ (baseSupport K (h + 3)) (Q, A')) =
      quadratic n ζ (baseSupport K h) (Q, A) := by
  apply Subtype.ext
  change extensionAmbientRestriction h (quadratic n ζ (baseSupport K (h + 3)) (Q, A')).val = _
  simp only [quadratic, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    Submodule.coe_add, map_add, traceLinearProduct_val, map_sum, map_mul, pureExtendForm,
    LinearMap.coe_mk, AddHom.coe_mk, extensionAmbientRestriction_pureExtend]
  simp [Fin.sum_univ_add, hA, ← correction_baseSupport_castAdd n ζ hh Q A A' hA]

end IdealGeneration.TripleNormal.Layer
