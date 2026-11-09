module

public import IdealGeneration.TripleNormalNewLayerProducts
public import IdealGeneration.TripleNormalSourceCoordinates

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The layer products occupy exactly the new-layer coefficient group. -/

noncomputable section
namespace IdealGeneration.TripleNormal.NewLayerBlock
open SupportedQuadrics

variable {K : Type*} [Field K] {h p q : ℕ}
variable (C : ConeConfiguration K 3 (h + 3 + 4) p q)
  (ω : K) (t : Fin h → K) (u : Fin 3 → K) (n : Layer.Normals K) (ζ : Layer.Heights K)
  (points : PointPattern C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)))
  (hω : IsPrimitiveRoot ω 3) (ht : ∀ i, Fin.append t u i ≠ 0)
  (hdet : ∀ j, (Layer.normalMatrix n j).det ≠ 0) (hζ : ∀ j ν, ζ j ν ≠ 0)

local notation "H" => mixedEquiv C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)) points hω ht hdet hζ
local notation "F" => liftEquiv C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)) points hω ht hdet hζ
local notation "hF" => residualEquiv_fst C ω (Fin.append t u) n ζ (Layer.baseSupport K (h + 3)) points hω ht hdet hζ
local notation "E" => mixedKernelCoordinatesEquiv C (LinearEquiv.symm F) hF
local notation "S" => layerMixedSource C ω t u n ζ points hω ht hdet hζ
local notation "Scol" => layerColumnSource C ω t u n ζ points hω ht hdet hζ

theorem mixedKernelCoordinates_mixedEquiv (a : Fin (h + 3) → K) : E (H a) = a :=
  congrArg Prod.snd ((F).symm_apply_apply (0, a))

private theorem mixedKernelCoordinates_layerColumn (b : Fin 3) (j : Fin 4) (k : Fin (h + 3 + 4)) :
    E (Scol b j k) = (Pi.single (layerVariable h j)
      (Pi.single (b.natAdd h) (1 : K)) : Fin (h + 3 + 4) → Fin (h + 3) → K) k := by
  by_cases hk : k = layerVariable h j
  · subst k
    simp [layerColumnSource, mixedKernelCoordinates_mixedEquiv]
  · simp [layerColumnSource, Pi.single_eq_of_ne hk]

private theorem layerMixedSource_coordinates_sum (c : Fin 4 → Fin 3 → K) (k : Fin (h + 3 + 4)) :
    E (S c k) = ∑ j : Fin 4, ∑ b : Fin 3, c j b •
      (Pi.single (layerVariable h j) (Pi.single (b.natAdd h) (1 : K)) :
        Fin (h + 3 + 4) → Fin (h + 3) → K) k := by
  simp only [layerMixedSource, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
    map_sum, map_smul, mixedKernelCoordinates_layerColumn C ω t u n ζ points hω ht hdet hζ]

/-- There are no new-layer product coordinates over base multipliers. -/
theorem layerMixedSource_coordinates_base (c : Fin 4 → Fin 3 → K) (i : Fin (h + 3)) :
    E (S c (i.castAdd 4)) = 0 := by
  rw [layerMixedSource_coordinates_sum]
  have hne (j : Fin 4) : i.castAdd 4 ≠ layerVariable h j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = h + 3 + j.val at hv
    omega
  simp [hne]

/-- Over layer j, precisely the three new mixed coordinates are present. -/
theorem layerMixedSource_coordinates_layer (c : Fin 4 → Fin 3 → K) (j : Fin 4) :
    E (S c (layerVariable h j)) = Fin.append (0 : Fin h → K) (c j) := by
  rw [layerMixedSource_coordinates_sum, Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    funext i
    refine Fin.addCases (fun k => ?_) (fun b => ?_) i
    · have hne (b : Fin 3) : k.castAdd 3 ≠ b.natAdd h := by
        intro he
        have hv := congrArg Fin.val he
        change k.val = h + b.val at hv
        omega
      simp [Finset.sum_apply, hne]
    · simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  · intro k _ hk
    have hne : layerVariable h j ≠ layerVariable h k := by
      intro he
      apply hk
      apply Fin.ext
      have hv := congrArg Fin.val he
      change h + 3 + j.val = h + 3 + k.val at hv
      omega
    simp [hne]
  · simp

end IdealGeneration.TripleNormal.NewLayerBlock
