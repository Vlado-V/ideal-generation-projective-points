module

public import IdealGeneration.TripleNormalSupportedExtension
public import IdealGeneration.TripleNormalSupportedQuadrics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The supported quadratic pattern survives enlargement

The old layer supports use only the first six base coordinates. Adding
three more base coordinates keeps those layer points fixed and adds the
prescribed pair of conic normals over each new base coordinate.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open SupportedQuadrics

variable {K : Type*} [Field K] {h p q r : ℕ}

private theorem embedOldAmbient_layerPoint (n : Fin 3 → K) (x : Fin h → K) (z : Fin 4 → K) :
    embedOldAmbient (Layer.point n x z) = Layer.point n (Fin.append x (0 : Fin 3 → K)) z := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp [embedOldAmbient, Layer.point]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp [embedOldAmbient, embedOldTrace, Layer.point]

private theorem append_single_old (i : Fin h) :
    Fin.append (Pi.single i (1 : K)) (0 : Fin 3 → K) =
      Pi.single (i.castAdd 3) 1 := by
  classical
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Pi.single_apply]
  · have hne : j.natAdd h ≠ i.castAdd 3 := by
      intro he
      have hval := congrArg Fin.val he
      simp at hval
      omega
    simp [hne]

private theorem append_single_new (i : Fin 3) :
    Fin.append (0 : Fin h → K) (Pi.single i 1) = Pi.single (i.natAdd h) 1 := by
  classical
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have hne : j.castAdd 3 ≠ i.natAdd h := by
      intro he
      have hval := congrArg Fin.val he
      simp at hval
      omega
    simp [hne]
  · simp [Pi.single_apply]

private theorem append_baseSupport (hh : 6 ≤ h) (j : Fin 4) (ν : Fin 3) :
    Fin.append (Layer.baseSupport K h j ν) (0 : Fin 3 → K) = Layer.baseSupport K (h + 3) j ν := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp [Layer.baseSupport]
  · rw [Fin.append_right, Pi.zero_apply, Layer.baseSupport_eq_zero]
    simp
    omega

private theorem supportedExtension_point_new_conic
    (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (ω : K) (u : Fin 3 → K)
    (b : Fin 3) (μ : Fin 2) :
    (supportedExtension C a ζ (fun j => baseNormal ω (u j))).point
      ((finProdFinEquiv (b, μ)).natAdd p) =
      Layer.point (baseNormal ω (u b) μ) (Pi.single (b.natAdd h) 1) 0 := by
  rw [supportedExtension_point_new]
  have hx := append_single_new (K := K) (h := h) b
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [Layer.point]
  · simp only [Fin.append_right, Layer.point, Fin.addCases_right, extensionCoordinate, hx]
    rfl

/-- The genuine enlarged configuration has exactly the old and new base
cone pairs and the original twelve layer cone points. -/
theorem supportedExtension_pointPattern
    (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K)
    (ω : K) (t : Fin h → K) (u : Fin 3 → K)
    (n : Layer.Normals K) (heights : Layer.Heights K) (hh : 6 ≤ h)
    (hpattern : PointPattern C ω t n heights (Layer.baseSupport K h)) :
    PointPattern (supportedExtension C a ζ (fun j => baseNormal ω (u j)))
      ω (Fin.append t u) n heights (Layer.baseSupport K (h + 3)) := by
  have hbase (i : Fin h) (μ : Fin 2) (k : Fin p)
      (hk : C.point k = Layer.point (baseNormal ω (t i) μ) (Pi.single i 1) 0) :
      (supportedExtension C a ζ (fun j => baseNormal ω (u j))).point (k.castAdd 6) =
        Layer.point (baseNormal ω (Fin.append t u (i.castAdd 3)) μ)
          (Pi.single (i.castAdd 3) 1) 0 := by
    rw [supportedExtension_point_old, hk, embedOldAmbient_layerPoint, append_single_old,
      Fin.append_left]
  have hlayer (j : Fin 4) (ν : Fin 3) (k : Fin p)
      (hk : C.point k = Layer.point (n j ν) (Layer.baseSupport K h j ν)
        (Pi.single j (heights j ν))) :
      (supportedExtension C a ζ (fun j => baseNormal ω (u j))).point (k.castAdd 6) =
        Layer.point (n j ν) (Layer.baseSupport K (h + 3) j ν) (Pi.single j (heights j ν)) := by
    rw [supportedExtension_point_old, hk, embedOldAmbient_layerPoint, append_baseSupport hh]
  have hnew (b : Fin 3) (μ : Fin 2) :
      (supportedExtension C a ζ (fun j => baseNormal ω (u j))).point
        ((finProdFinEquiv (b, μ)).natAdd p) =
        Layer.point (baseNormal ω (Fin.append t u (b.natAdd h)) μ)
          (Pi.single (b.natAdd h) 1) 0 := by
    rw [Fin.append_right, supportedExtension_point_new_conic]
  constructor
  · intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rcases hpattern.exhaustive k with ⟨j, μ, hj⟩ | ⟨j, ν, hj⟩
      · exact Or.inl ⟨j.castAdd 3, μ, hbase j μ k hj⟩
      · exact Or.inr ⟨j, ν, hlayer j ν k hj⟩
    · let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
      obtain ⟨⟨b, μ⟩, rfl⟩ := e.surjective k
      exact Or.inl ⟨b.natAdd h, μ, hnew b μ⟩
  · intro i μ
    refine Fin.addCases (fun k => ?_) (fun b => ?_) i
    · obtain ⟨j, hj⟩ := hpattern.base k μ
      exact ⟨j.castAdd 6, hbase k μ j hj⟩
    · exact ⟨(finProdFinEquiv (b, μ)).natAdd p, hnew b μ⟩
  · intro j ν
    obtain ⟨k, hk⟩ := hpattern.layer j ν
    exact ⟨k.castAdd 6, hlayer j ν k hk⟩

end IdealGeneration.TripleNormal
