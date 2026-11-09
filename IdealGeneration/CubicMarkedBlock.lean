module

public import IdealGeneration.CubicParameterRestriction
public import IdealGeneration.CubicAllowedValues

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Actual allowed rows and the block reduction for a supported cubic pair extension. -/

noncomputable section
namespace IdealGeneration.CubicSupported

open MvPolynomial CubicMiddle

variable {K : Type*} [Field K] {m f g : ℕ}

namespace Parameters

variable (P : Parameters K m) (free : Fin f → Fin m → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- The scalar-coordinate model of the allowed values. -/
abbrev AllowedCoordinates := (P.SingleEdge → K) × (Fin f → Fin 2 → K)

private theorem coneHeight_ne_zero (i : Fin (Fintype.card P.ConeLabel)) :
    (P.toConeConfiguration free).height i ≠ 0 := by
  change P.coneHeight (P.coneLabelEquiv.symm i) ≠ 0
  cases P.coneLabelEquiv.symm i with
  | inl v => exact P.vertexHeight_ne v.1 v.2
  | inr e => exact P.edgeHeight_ne e.val.1 e.val.2

/-- The actual middle evaluation in independent source and target coordinates. -/
def markedEvaluation : P.EliminatedParameters →ₗ[K] P.AllowedCoordinates (f := f) :=
  (P.allowedValuesEquiv free).toLinearMap.comp
    (P.parameterEvaluation free h₂ h₆ (P.coneHeight_ne_zero free))

theorem markedEvaluation_singleEdge (x : P.EliminatedParameters) (e : P.SingleEdge) :
    (P.markedEvaluation free h₂ h₆ x).1 e =
      -eval (edgeSupport e.val 1 (P.edgeLambda e.val)) (P.parameterPhi free h₂ h₆ x 1).val := by
  change -eval ((P.toConeConfiguration free).trace (traceLabelEquiv m f (.inl (.inr e.val))))
    (P.parameterPhi free h₂ h₆ x 1).val = _
  rw [P.toConeConfiguration_trace]
  rfl

theorem markedEvaluation_free (x : P.EliminatedParameters) (i : Fin f) (k : Fin 2) :
    (P.markedEvaluation free h₂ h₆ x).2 i k =
      eval (free i) (P.parameterPhi free h₂ h₆ x k).val := by
  change eval ((P.toConeConfiguration free).trace (traceLabelEquiv m f (.inr i)))
    (P.parameterPhi free h₂ h₆ x k).val = _
  rw [P.toConeConfiguration_trace]
  rfl

/-- Injectivity in the explicit coordinates is exactly injectivity of the middle map. -/
theorem middleMultiplication_injective_iff_markedEvaluation :
    Function.Injective ((P.toConeConfiguration free).middleMultiplication 3) ↔
      Function.Injective (P.markedEvaluation free h₂ h₆) := by
  rw [P.middleMultiplication_injective_iff_parameterEvaluation free h₂ h₆ (P.coneHeight_ne_zero free)]
  constructor
  · intro h
    exact (P.allowedValuesEquiv free).injective.comp h
  · intro h x y hxy
    apply h
    exact congrArg (P.allowedValuesEquiv free) hxy

end Parameters

namespace Compatible

variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)
variable (e : Fin f ↪ Fin g) (free : Fin f → Fin m → K) (free' : Fin g → Fin (m + 2) → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- Restrict the allowed coordinates to the old supported and free labels. -/
def restrictAllowedCoordinates : Q.AllowedCoordinates (f := g) →ₗ[K] P.AllowedCoordinates (f := f) where
  toFun a := (fun b => a.1 (h.singleEdge b), fun i => a.2 (e i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem extendTrace_edgeSupport (b : Edge m) (lam : K) :
    extendTrace (edgeSupport b 1 lam) = edgeSupport (oldEdge m b) 1 lam := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [extendTrace_old]
    change vertexSupport b.val.1 1 i + vertexSupport b.val.2 (1 * lam) i =
      vertexSupport (Fin.castAdd 2 b.val.1) 1 (Fin.castAdd 2 i) +
        vertexSupport (Fin.castAdd 2 b.val.2) (1 * lam) (Fin.castAdd 2 i)
    simp [vertexSupport]
  · have hne (a : Fin m) : Fin.natAdd m j ≠ Fin.castAdd 2 a := by
      intro h
      have he := congrArg Fin.val h
      change m + j.val = a.val at he
      omega
    rw [extendTrace_new]
    change 0 = vertexSupport (Fin.castAdd 2 b.val.1) 1 (Fin.natAdd m j) +
      vertexSupport (Fin.castAdd 2 b.val.2) (1 * lam) (Fin.natAdd m j)
    simp [vertexSupport, hne]

/-- The upper blocks of the new evaluation restrict to the actual old evaluation. -/
theorem markedEvaluation_restrict (hfree : ∀ i, free' (e i) = extendTrace (free i))
    (x : Q.EliminatedParameters) :
    h.restrictAllowedCoordinates e (Q.markedEvaluation free' h₂ h₆ x) =
      P.markedEvaluation free h₂ h₆ (h.restrictParameters x) := by
  apply Prod.ext
  · funext b
    change (Q.markedEvaluation free' h₂ h₆ x).1 (h.singleEdge b) = _
    rw [Q.markedEvaluation_singleEdge, P.markedEvaluation_singleEdge]
    change -eval (edgeSupport (oldEdge m b.val) 1 (Q.edgeLambda (oldEdge m b.val)))
        (Q.parameterPhi free' h₂ h₆ x 1).val = _
    rw [h.edgeLambda_eq, ← extendTrace_edgeSupport, h.parameterPhi_eval_extendTrace free free' h₂ h₆]
  · funext i k
    change (Q.markedEvaluation free' h₂ h₆ x).2 (e i) k = _
    rw [Q.markedEvaluation_free, P.markedEvaluation_free, hfree,
      h.parameterPhi_eval_extendTrace free free' h₂ h₆]

/-- Retain the rows indexed by the new single edges and new free supports. -/
def newRowRestriction : Q.AllowedCoordinates (f := g) →ₗ[K]
    (({b : Q.SingleEdge // b ∉ Set.range h.singleEdge} → K) ×
      ({i : Fin g // i ∉ Set.range e} → Fin 2 → K)) where
  toFun a := (fun b => a.1 b.val, fun i => a.2 i.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The new scalar rows on the kernel of restriction, with old rows removed. -/
def newMarkedEvaluation : h.restrictParameters.ker →ₗ[K]
    (({b : Q.SingleEdge // b ∉ Set.range h.singleEdge} → K) ×
      ({i : Fin g // i ∉ Set.range e} → Fin 2 → K)) :=
  (h.newRowRestriction e).comp
    ((Q.markedEvaluation free' h₂ h₆).comp h.restrictParameters.ker.subtype)

/-- Injectivity of the old and new diagonal blocks implies injectivity of the actual enlarged map. -/
theorem markedEvaluation_injective_of_blocks
    (hfree : ∀ i, free' (e i) = extendTrace (free i))
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (hnew : Function.Injective (h.newMarkedEvaluation e free' h₂ h₆)) :
    Function.Injective (Q.markedEvaluation free' h₂ h₆) := by
  apply (linearMap_injective_iff_kernel_subsingleton (Q.markedEvaluation free' h₂ h₆)).mpr
  have hz (x : (Q.markedEvaluation free' h₂ h₆).ker) : x = 0 := by
    have hx := LinearMap.mem_ker.mp x.property
    have hres : h.restrictParameters x.val = 0 := by
      apply hold
      rw [← h.markedEvaluation_restrict e free free' h₂ h₆ hfree, hx,
        (h.restrictAllowedCoordinates e).map_zero, (P.markedEvaluation free h₂ h₆).map_zero]
    let z : h.restrictParameters.ker := ⟨x.val, LinearMap.mem_ker.mpr hres⟩
    have hz' : z = 0 := by
      apply hnew
      rw [(h.newMarkedEvaluation e free' h₂ h₆).map_zero]
      change h.newRowRestriction e (Q.markedEvaluation free' h₂ h₆ x.val) = 0
      rw [hx, (h.newRowRestriction e).map_zero]
    exact Subtype.ext (congrArg (fun w : h.restrictParameters.ker => w.val) hz')
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end Compatible
end IdealGeneration.CubicSupported
