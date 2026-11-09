module

public import IdealGeneration.TripleNormalNormalExtension
public import IdealGeneration.TripleNormalReduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Allowed values of the enlarged cone

The old trace constraints persist on the old rows. Each new coordinate
trace point has its own two normal constraints, while the new free and
layer trace points have arbitrary vector values.
-/

noncomputable section
namespace IdealGeneration.TripleNormal
open scoped Matrix

variable {K : Type*} [Field K] {h p q r : ℕ}

variable (C : ConeConfiguration K 3 (h + 4) p q)
  (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K)

local notation "C'" => supportedExtension C a ζ normal

/-- Old cone rows see exactly the old trace value columns. -/
theorem valueConstraint_supportedExtension_old
    (v : Fin 3 → Fin (q + (3 + (r + 4))) → K) (i : Fin p) :
    valueConstraint C' v (i.castAdd 6) =
      valueConstraint C (fun k j => v k (j.castAdd (3 + (r + 4)))) i := by
  change (∑ k, (C').normal (i.castAdd 6) k * v k ((C').support (i.castAdd 6))) = _
  rw [supportedExtension_normal_old, supportedExtension_support_old]
  rfl

/-- Each new cone row sees only the new coordinate point above which it lies. -/
theorem valueConstraint_supportedExtension_new
    (v : Fin 3 → Fin (q + (3 + (r + 4))) → K) (b : Fin 3) (k : Fin 2) :
    valueConstraint C' v ((finProdFinEquiv (b, k)).natAdd p) =
      newNormalRowMap normal b (fun j => v j ((b.castAdd (r + 4)).natAdd q)) k := by
  change (∑ j, (C').normal ((finProdFinEquiv (b, k)).natAdd p) j *
    v j ((C').support ((finProdFinEquiv (b, k)).natAdd p))) = _
  rw [supportedExtension_normal_new C a ζ normal b k, supportedExtension_support_new C a ζ normal b k]
  rfl

private def assembleAllowedRows
    (v : Fin 3 → Fin q → K) (w : Fin 3 → Fin 3 → K)
    (f : Fin r → Fin 3 → K) (l : Fin 4 → Fin 3 → K) :
    Fin 3 → Fin (q + (3 + (r + 4))) → K :=
  fun i => Fin.append (v i) (Fin.append (fun b => w b i)
    (Fin.append (fun j => f j i) (fun j => l j i)))

/-- Surjectivity of the old allowed-value constraints persists after
adding the three independent pairs of new normal constraints. -/
theorem supportedExtension_valueConstraint_surjective
    (hOld : Function.Surjective (valueConstraint C))
    (hRows : ∀ b, Function.Surjective (newNormalRowMap normal b)) :
    Function.Surjective (valueConstraint C') := by
  let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
  intro target
  obtain ⟨v, hv⟩ := hOld (fun i => target (i.castAdd 6))
  choose w hw using fun b => hRows b (fun k => target ((e (b, k)).natAdd p))
  refine ⟨assembleAllowedRows v w 0 0, ?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [valueConstraint_supportedExtension_old]
    simpa only [assembleAllowedRows, Fin.append_left] using congrFun hv j
  · obtain ⟨⟨b, k⟩, rfl⟩ := e.surjective j
    change valueConstraint C' (assembleAllowedRows v w 0 0)
      ((finProdFinEquiv (b, k)).natAdd p) = target ((e (b, k)).natAdd p)
    rw [valueConstraint_supportedExtension_new]
    simpa only [assembleAllowedRows, Fin.append_right, Fin.append_left] using congrFun (hw b) k

/-- The value column at a new coordinate lies in its two-row kernel. -/
abbrev NewCoordinateValues (normal : Fin 3 → Fin 2 → Fin 3 → K) :=
  (b : Fin 3) → (newNormalRowMap normal b).ker

private def oldAllowedRows (v : AllowedValues C') : AllowedValues C :=
  ⟨fun k j => v.val k (j.castAdd (3 + (r + 4))), by
    apply LinearMap.mem_ker.mpr
    funext i
    change valueConstraint C (fun k j => v.val k (j.castAdd (3 + (r + 4)))) i = 0
    rw [← valueConstraint_supportedExtension_old C a ζ normal v.val i]
    exact congrFun (LinearMap.mem_ker.mp v.property) (i.castAdd 6)⟩

private def newAllowedRows (v : AllowedValues C') : NewCoordinateValues normal :=
  fun b => ⟨fun j => v.val j ((b.castAdd (r + 4)).natAdd q), by
    apply LinearMap.mem_ker.mpr
    funext k
    change newNormalRowMap normal b (fun j => v.val j ((b.castAdd (r + 4)).natAdd q)) k = 0
    rw [← valueConstraint_supportedExtension_new C a ζ normal v.val b k]
    exact congrFun (LinearMap.mem_ker.mp v.property) ((finProdFinEquiv (b, k)).natAdd p)⟩

/-- Actual allowed values are the product of old allowed values, the three
new constrained columns, and the unrestricted free and layer columns. -/
def supportedExtensionAllowedValuesEquiv :
    AllowedValues C' ≃ₗ[K]
      (AllowedValues C × (NewCoordinateValues normal × ((Fin r → Fin 3 → K) ×
        (Fin 4 → Fin 3 → K)))) where
  toFun v := (oldAllowedRows C a ζ normal v, newAllowedRows C a ζ normal v,
    fun j k => v.val k (((j.castAdd 4).natAdd 3).natAdd q),
    fun j k => v.val k (((j.natAdd r).natAdd 3).natAdd q))
  invFun v := ⟨assembleAllowedRows v.1.val (fun b => (v.2.1 b).val) v.2.2.1 v.2.2.2, by
    apply LinearMap.mem_ker.mpr
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change valueConstraint C' (assembleAllowedRows v.1.val (fun b => (v.2.1 b).val)
        v.2.2.1 v.2.2.2) (j.castAdd 6) = 0
      rw [valueConstraint_supportedExtension_old]
      simpa only [assembleAllowedRows, Fin.append_left, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp v.1.property) j
    · let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
      obtain ⟨⟨b, k⟩, rfl⟩ := e.surjective j
      change valueConstraint C' (assembleAllowedRows v.1.val (fun b => (v.2.1 b).val)
        v.2.2.1 v.2.2.2) ((finProdFinEquiv (b, k)).natAdd p) = 0
      rw [valueConstraint_supportedExtension_new]
      simpa only [assembleAllowedRows, Fin.append_right, Fin.append_left, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp (v.2.1 b).property) k⟩
  left_inv v := by
    apply Subtype.ext
    funext k j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [assembleAllowedRows, oldAllowedRows]
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) i
      · simp [assembleAllowedRows, newAllowedRows]
      · refine Fin.addCases (fun t => ?_) (fun t => ?_) b <;> simp [assembleAllowedRows]
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      funext k j
      simp [assembleAllowedRows, oldAllowedRows]
    · apply Prod.ext
      · funext b
        apply Subtype.ext
        funext k
        simp [assembleAllowedRows, newAllowedRows]
      · apply Prod.ext <;> funext j k <;> simp [assembleAllowedRows]
  map_add' _ _ := Prod.ext (Subtype.ext rfl) (Prod.ext (funext fun _ => Subtype.ext rfl) rfl)
  map_smul' _ _ := Prod.ext (Subtype.ext rfl) (Prod.ext (funext fun _ => Subtype.ext rfl) rfl)

/-- The first component is restriction to the original trace columns. -/
@[simp] theorem supportedExtensionAllowedValuesEquiv_old (v : AllowedValues C')
    (k : Fin 3) (j : Fin q) :
    ((supportedExtensionAllowedValuesEquiv C a ζ normal) v).1.val k j =
      v.val k (j.castAdd (3 + (r + 4))) := rfl

/-- Every allowed vector on the old trace extends to the enlarged trace. -/
theorem exists_supportedExtensionAllowedValues (v : AllowedValues C) :
    ∃ w : AllowedValues C',
      ∀ k j, w.val k (j.castAdd (3 + (r + 4))) = v.val k j := by
  let e := supportedExtensionAllowedValuesEquiv C a ζ normal
  refine ⟨e.symm (v, 0, 0, 0), fun k j => ?_⟩
  rw [← supportedExtensionAllowedValuesEquiv_old C a ζ normal, show
    supportedExtensionAllowedValuesEquiv C a ζ normal (e.symm (v, 0, 0, 0)) =
      (v, 0, 0, 0) from e.apply_symm_apply _]

end IdealGeneration.TripleNormal
