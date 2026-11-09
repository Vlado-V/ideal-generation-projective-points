module

public import IdealGeneration.TripleNormalExtensionRestriction
public import IdealGeneration.TripleNormalLayerLift
public import IdealGeneration.ConeMiddleFamily

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar normal-ideal evaluation under enlargement

The old normal-ideal forms extend to the enlarged space. At each of the
three new trace coordinates, the mixed quadrics correct the two new cone
values independently.
-/

noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial NormalDegree ConeParameterSpace ConeMiddleFamily
open scoped Matrix

variable {K : Type*} [Field K] {h p q r : ℕ}

private theorem coneRestrict_rename_oldAmbientIndex (f : Poly K (3 + (h + 4))) :
    coneRestrict K 3 (h + 3 + 4) (rename (oldAmbientIndex h) f) =
      rename (oldTraceIndex h) (coneRestrict K 3 (h + 4) f) := by
  have heq : (coneRestrict K 3 (h + 3 + 4)).comp (rename (oldAmbientIndex h)) =
      (rename (oldTraceIndex h)).comp (coneRestrict K 3 (h + 4)) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [oldAmbientIndex]
  exact DFunLike.congr_fun heq f

private def extendNormalQuadric (f : normalForms K 3 (h + 4) 2) :
    normalForms K 3 (h + 3 + 4) 2 :=
  ⟨⟨rename (oldAmbientIndex h) f.val.val, f.val.property.rename_isHomogeneous⟩, by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change coneRestrict K 3 (h + 3 + 4) (rename (oldAmbientIndex h) f.val.val) = 0
    rw [coneRestrict_rename_oldAmbientIndex]
    have hz : coneRestrict K 3 (h + 4) f.val.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp f.property)
    rw [hz, map_zero]⟩

private def normalCorrection (h : ℕ) (b : Fin 3) (v : Fin 3 → K) :
    normalForms K 3 (h + 3 + 4) 2 :=
  ⟨⟨X (((b.natAdd h).castAdd 4).natAdd 3) * pureExtend K 3 (h + 3 + 4)
      (Layer.normalForm v).val,
    (isHomogeneous_X K _).mul (pureExtendForm K 3 (h + 3 + 4) 1 (Layer.normalForm v)).property⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change coneRestrict K 3 (h + 3 + 4)
        (X (((b.natAdd h).castAdd 4).natAdd 3) *
          pureExtend K 3 (h + 3 + 4) (Layer.normalForm v).val) = 0
      simp [Layer.normalForm, pureExtend, map_sum, map_mul]⟩

private theorem eval_normalCorrection (x : Fin (3 + (h + 3 + 4)) → K)
    (b : Fin 3) (v : Fin 3 → K) :
    eval x (normalCorrection h b v).val.val =
      x (((b.natAdd h).castAdd 4).natAdd 3) * ((x ∘ Fin.castAdd (h + 3 + 4)) ⬝ᵥ v) := by
  change eval x (X (((b.natAdd h).castAdd 4).natAdd 3) *
    pureExtend K 3 (h + 3 + 4) (Layer.normalForm v).val) = _
  simp [pureExtend, eval_rename]

private theorem normalEvaluation_encode_apply {m p q : ℕ}
    (C : ConeConfiguration K 3 m p q) (f : normalForms K 3 m 2) (i : Fin p) :
    normalEvaluation C.support (encode C) 2 f i = eval (C.point i) f.val.val := by
  change eval ((configuration C.support (encode C)).point i) f.val.val = _
  rw [configuration_encode]

/-- The two normal constraints above one of the new coordinate points. -/
def newNormalRowMap (normal : Fin 3 → Fin 2 → Fin 3 → K) (b : Fin 3) :
    (Fin 3 → K) →ₗ[K] (Fin 2 → K) where
  toFun v k := normal b k ⬝ᵥ v
  map_add' v w := funext (fun k => dotProduct_add (normal b k) v w)
  map_smul' c v := by
    funext k
    exact dotProduct_smul c (normal b k) v

@[simp] theorem newNormalRowMap_apply (normal : Fin 3 → Fin 2 → Fin 3 → K)
    (b : Fin 3) (v : Fin 3 → K) (k : Fin 2) :
    newNormalRowMap normal b v k = normal b k ⬝ᵥ v := rfl

/-- The six new cone rows extend independent scalar normal-ideal evaluation
when the two normal directions at each new coordinate have full row rank. -/
theorem supportedExtension_normalEvaluation_surjective
    (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K)
    (normal : Fin 3 → Fin 2 → Fin 3 → K)
    (hOld : Function.Surjective (normalEvaluation C.support (encode C) 2))
    (hRows : ∀ b, Function.Surjective (newNormalRowMap normal b)) :
    Function.Surjective
      (normalEvaluation (supportedExtension C a ζ normal).support
        (encode (supportedExtension C a ζ normal)) 2) := by
  classical
  let C' := supportedExtension C a ζ normal
  let E := normalEvaluation C'.support (encode C') 2
  let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
  let idx (b : Fin 3) (k : Fin 2) := (e (b, k)).natAdd p
  change Function.Surjective E
  intro target
  obtain ⟨f, hf⟩ := hOld (fun i => target (i.castAdd 6))
  let F := extendNormalQuadric f
  choose u hu using fun b => hRows b (fun k => target (idx b k) - E F (idx b k))
  let G := F + ∑ b, normalCorrection h b (u b)
  have hF (i : Fin p) : E F (i.castAdd 6) = target (i.castAdd 6) := by
    change normalEvaluation C'.support (encode C') 2 F (i.castAdd 6) = _
    rw [normalEvaluation_encode_apply, supportedExtension_point_old C a ζ normal i]
    change eval (embedOldAmbient (C.point i)) (rename (oldAmbientIndex h) f.val.val) = _
    rw [eval_rename, embedOldAmbient_oldAmbientIndex, ← normalEvaluation_encode_apply]
    exact congrFun hf i
  have hOldCorrection (i : Fin p) (b : Fin 3) :
      E (normalCorrection h b (u b)) (i.castAdd 6) = 0 := by
    change normalEvaluation C'.support (encode C') 2 (normalCorrection h b (u b)) (i.castAdd 6) = 0
    rw [normalEvaluation_encode_apply, supportedExtension_point_old C a ζ normal i,
      eval_normalCorrection]
    simp [embedOldAmbient, embedOldTrace]
  have hNewCorrection (b : Fin 3) (k : Fin 2) (j : Fin 3) :
      E (normalCorrection h j (u j)) (idx b k) =
        if j = b then normal b k ⬝ᵥ u j else 0 := by
    change normalEvaluation C'.support (encode C') 2 (normalCorrection h j (u j))
      ((finProdFinEquiv (b, k)).natAdd p) = _
    rw [normalEvaluation_encode_apply, supportedExtension_point_new C a ζ normal b k,
      eval_normalCorrection]
    have hnorm : (Fin.append (normal b k) (extensionCoordinate h b)) ∘
        Fin.castAdd (h + 3 + 4) = normal b k := by
      funext i
      exact Fin.append_left _ _ i
    rw [hnorm]
    simp [extensionCoordinate, Pi.single_apply, ite_mul]
  refine ⟨G, ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [G, map_sum, Finset.sum_apply, hOldCorrection, hF]
  · obtain ⟨⟨b, k⟩, rfl⟩ := e.surjective j
    change E G (idx b k) = target (idx b k)
    have hval := congrFun (hu b) k
    change normal b k ⬝ᵥ u b = target (idx b k) - E F (idx b k) at hval
    simp [G, map_sum, Finset.sum_apply, hNewCorrection, hval]

/-- The number of cones is preserved in the required formula after the enlargement. -/
theorem extension_cone_count (h : ℕ) : (2 * h + 12) + 6 = 2 * (h + 3) + 12 := by omega

/-- Three new coordinates, the free points, and four new layer points give
the required enlarged trace count. -/
theorem extension_trace_count (h : ℕ) :
    (h + 4) * (h + 5) / 3 + (3 + ((2 * h + 5) + 4)) =
      (h + 3 + 4) * (h + 3 + 5) / 3 := by
  have hprod : (h + 3 + 4) * (h + 3 + 5) =
      (h + 4) * (h + 5) + 3 * (2 * h + 12) := by ring
  rw [hprod]
  omega

end IdealGeneration.TripleNormal
