module

public import IdealGeneration.TripleNormalSupportedQuadrics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restricting a supported quadratic keeps its pure form and its old conic coefficients. -/

noncomputable section
namespace IdealGeneration.TripleNormal.SupportedQuadrics

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
  (hζ : ∀ j ν, ζ j ν ≠ 0)

local notation "E" => liftEquiv C ω t n ζ (Layer.baseSupport K h)
  oldPoints hω ht hdet hζ
local notation "E'" => liftEquiv (supportedExtension C a η normal) ω (Fin.append t u)
  n ζ (Layer.baseSupport K (h + 3)) newPoints hω htu hdet hζ
local notation "R" => supportedExtensionResidualRestriction C a η normal 2

/-- The restriction of the lift discards the three new conic coefficients. -/
theorem residualRestriction_liftEquiv_append (hh : 6 ≤ h) (Q : Forms K 3 2)
    (γ : Fin h → K) (δ : Fin 3 → K) :
    R (E' (Q, Fin.append γ δ)) = E (Q, γ) := by
  apply Subtype.ext
  change extensionAmbientRestrictionForm h 2
      (liftForm ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3))
        (Q, Fin.append γ δ)) =
    liftForm ω t n ζ (Layer.baseSupport K h) (Q, γ)
  exact restrict_liftForm_append ω t u n ζ hh Q γ δ

/-- The pure-normal section uses zero conic coefficients, so its restriction
is the old pure-normal section. -/
theorem residualRestriction_pureLift (hh : 6 ≤ h) (Q : Forms K 3 2) :
    R (pureLift (supportedExtension C a η normal) ω (Fin.append t u) n ζ
      (Layer.baseSupport K (h + 3)) newPoints hω htu hdet hζ Q) =
    pureLift C ω t n ζ (Layer.baseSupport K h) oldPoints hω ht hdet hζ Q := by
  have hzero : Fin.append (0 : Fin h → K) (0 : Fin 3 → K) = 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  change R (E' (Q, 0)) = E (Q, 0)
  simpa only [hzero] using
    residualRestriction_liftEquiv_append C a η normal ω t u n ζ oldPoints newPoints
      hω ht htu hdet hζ hh Q 0 0

/-- In the exact residual coordinates, actual restriction is projection onto
the old mixed coefficients together with the unchanged pure quadric. -/
theorem residualEquiv_residualRestriction (hh : 6 ≤ h)
    (f : (supportedExtension C a η normal).residualPiece 2) :
    (E).symm (R f) = (((E').symm f).1, fun i => ((E').symm f).2 (i.castAdd 3)) := by
  let v := (E').symm f
  let γ : Fin h → K := fun i => v.2 (i.castAdd 3)
  let δ : Fin 3 → K := fun i => v.2 (i.natAdd h)
  have hsplit : Fin.append γ δ = v.2 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  have hnew : E' (v.1, Fin.append γ δ) = f := by
    rw [hsplit]
    exact (E').apply_symm_apply f
  have h := residualRestriction_liftEquiv_append C a η normal ω t u n ζ oldPoints newPoints
    hω ht htu hdet hζ hh v.1 γ δ
  rw [hnew] at h
  change (E).symm (R f) = (v.1, γ)
  rw [h, LinearEquiv.symm_apply_apply]

end IdealGeneration.TripleNormal.SupportedQuadrics
