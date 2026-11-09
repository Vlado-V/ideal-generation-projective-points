module

public import IdealGeneration.TripleNormalExtensionRestriction
public import IdealGeneration.TripleNormalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restriction maps on the coefficient-space source and allowed value space. -/
noncomputable section
namespace IdealGeneration.TripleNormal

variable {K : Type*} [Field K] {h p q r : ℕ}
  (C : ConeConfiguration K 3 (h + 4) p q) (a : Fin r × Fin (h + 3) → K)
  (ζ : Fin 4 → K) (n : Fin 3 → Fin 2 → Fin 3 → K)

local notation "Cnew" => supportedExtension C a ζ n
local notation "R₂" => supportedExtensionResidualRestriction C a ζ n 2

private theorem restriction_quadraticRestriction (f : (Cnew).residualPiece 2) :
    quadraticRestriction C (R₂ f) = quadraticRestriction Cnew f :=
  supportedExtensionResidualRestriction_pureRestrict C a ζ n 2 f

/-- Restriction of the mixed quadratic kernels. -/
def supportedExtensionMixedRestriction : MixedKernel Cnew →ₗ[K] MixedKernel C where
  toFun f := ⟨R₂ f.val, (restriction_quadraticRestriction C a ζ n f.val).trans f.property⟩
  map_add' f g := Subtype.ext (map_add R₂ f.val g.val)
  map_smul' k f := Subtype.ext (map_smul R₂ k f.val)

/-- Restriction of compatible triples of residual quadrics. -/
def supportedExtensionOmegaRestriction : Omega Cnew →ₗ[K] Omega C where
  toFun f := ⟨fun i => R₂ (f.val i), by
    change tripleNormalConstraint (K := K) (V := C.residualPiece 2)
      (quadraticRestriction C) (fun i => R₂ (f.val i)) = 0
    rw [tripleNormalConstraint_apply]
    have he : (fun i : Fin 3 => quadraticRestriction C (R₂ (f.val i))) =
        (fun i => quadraticRestriction Cnew (f.val i)) :=
      funext fun i => restriction_quadraticRestriction C a ζ n (f.val i)
    rw [he]
    exact f.property⟩
  map_add' f g := Subtype.ext (funext fun i => map_add R₂ (f.val i) (g.val i))
  map_smul' k f := Subtype.ext (funext fun i => map_smul R₂ k (f.val i))

/-- Restriction of the two summands in the source of the square map. -/
def supportedExtensionEvaluationSourceRestriction : EvaluationSource Cnew →ₗ[K] EvaluationSource C where
  toFun f := (supportedExtensionOmegaRestriction C a ζ n f.1,
    fun i => supportedExtensionMixedRestriction C a ζ n (f.2 (oldTraceIndex h i)))
  map_add' f g := Prod.ext
    (map_add (supportedExtensionOmegaRestriction C a ζ n) f.1 g.1)
    (funext fun i => map_add (supportedExtensionMixedRestriction C a ζ n)
      (f.2 (oldTraceIndex h i)) (g.2 (oldTraceIndex h i)))
  map_smul' k f := Prod.ext
    (map_smul (supportedExtensionOmegaRestriction C a ζ n) k f.1)
    (funext fun i => map_smul (supportedExtensionMixedRestriction C a ζ n) k
      (f.2 (oldTraceIndex h i)))

/-- Restriction of allowed values to the old trace rows. -/
def supportedExtensionAllowedRestriction : AllowedValues Cnew →ₗ[K] AllowedValues C :=
  let F : AllowedValues Cnew →ₗ[K] (Fin 3 → Fin q → K) :=
    { toFun := fun v i j => v.val i (j.castAdd (3 + (r + 4)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  F.codRestrict _ (by
    intro v
    funext i
    have he := congrFun v.property (i.castAdd 6)
    change (∑ b : Fin 3, (Cnew).normal (i.castAdd 6) b *
      v.val b ((Cnew).support (i.castAdd 6))) = 0 at he
    change (∑ b : Fin 3, C.normal i b * v.val b ((C.support i).castAdd (3 + (r + 4)))) = 0
    simpa only [supportedExtension_normal_old, supportedExtension_support_old] using he)

end IdealGeneration.TripleNormal
