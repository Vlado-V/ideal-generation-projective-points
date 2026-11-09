module

public import IdealGeneration.PointIdealReduced

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Splitting off the linear equations of a coordinate subspace. -/

noncomputable section
namespace IdealGeneration.CoordinateSubspace

open MvPolynomial

variable {K : Type*} [Field K] {n m p : ℕ} (e : Fin n ↪ Fin m)

/-- Extend the affine coordinate inclusion by retaining the homogenizing coordinate. -/
def variableEmbedding : Fin (n + 1) ↪ Fin (m + 1) where
  toFun := Fin.lastCases (Fin.last m) (fun j => (e j).castSucc)
  inj' := by
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;>
      refine Fin.lastCases ?_ (fun b => ?_) j <;>
      simp [Fin.castSucc_ne_last, Ne.symm, e.injective.eq_iff]

@[simp] theorem variableEmbedding_castSucc (j : Fin n) :
    variableEmbedding e j.castSucc = (e j).castSucc := by
  change Fin.lastCases (motive := fun _ => Fin (m + 1)) (Fin.last m)
    (fun j => (e j).castSucc) j.castSucc = _
  exact Fin.lastCases_castSucc j

@[simp] theorem variableEmbedding_last :
    variableEmbedding e (Fin.last n) = Fin.last m := by
  change Fin.lastCases (motive := fun _ => Fin (m + 1)) (Fin.last m)
    (fun j => (e j).castSucc) (Fin.last n) = _
  exact Fin.lastCases_last

private theorem castSucc_notMem_range (j : Fin m) (hj : j ∉ Set.range e) :
    j.castSucc ∉ Set.range (variableEmbedding e) := by
  rintro ⟨i, hi⟩
  revert hi
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa using (Fin.castSucc_ne_last j).symm
  · intro ha
    exact hj ⟨a, Fin.castSucc_injective _ (by simpa only [variableEmbedding_castSucc] using ha)⟩

/-- Add zero coordinates outside the chosen coordinate subspace. -/
def embedPoints (a : PointCoordinates K n p) : PointCoordinates K m p :=
  fun (i, j) => Function.extend e (fun u => a (i, u)) (fun _ => 0) j

@[simp] theorem embedPoints_apply_image (a : PointCoordinates K n p) (i : Fin p) (j : Fin n) :
    embedPoints e a (i, e j) = a (i, j) := by
  change Function.extend e (fun u => a (i, u)) (fun _ => 0) (e j) = _
  exact e.injective.extend_apply _ _ j

@[simp] theorem embedPoints_apply_unused (a : PointCoordinates K n p) (i : Fin p)
    (j : Fin m) (hj : j ∉ Set.range e) : embedPoints e a (i, j) = 0 := by
  change Function.extend e (fun u => a (i, u)) (fun _ => 0) j = 0
  exact Function.extend_apply' _ _ _ hj

/-- Lift polynomials from the smaller homogeneous ring by renaming variables. -/
def includePolynomials : Poly K (n + 1) →ₐ[K] Poly K (m + 1) :=
  rename (variableEmbedding e)

/-- Restrict to the subspace by setting the unused coordinates to zero. -/
def restrictPolynomials : Poly K (m + 1) →ₐ[K] Poly K (n + 1) :=
  aeval (Function.extend (variableEmbedding e) X (fun _ => 0))

@[simp] theorem includePolynomials_X (i : Fin (n + 1)) :
    includePolynomials (K := K) e (X i) = X (variableEmbedding e i) := by
  simp [includePolynomials]

@[simp] theorem restrictPolynomials_X_image (i : Fin (n + 1)) :
    restrictPolynomials (K := K) e (X (variableEmbedding e i)) = X i := by
  rw [restrictPolynomials, aeval_X, (variableEmbedding e).injective.extend_apply]

@[simp] theorem restrictPolynomials_X_unused (i : Fin (m + 1))
    (hi : i ∉ Set.range (variableEmbedding e)) :
    restrictPolynomials (K := K) e (X i) = 0 := by
  rw [restrictPolynomials, aeval_X, Function.extend_apply' _ _ _ hi]

private theorem restrict_comp_include :
    (restrictPolynomials (K := K) e).comp (includePolynomials e) = AlgHom.id K _ := by
  ext i
  simp

@[simp] theorem restrict_include (f : Poly K (n + 1)) :
    restrictPolynomials e (includePolynomials e f) = f :=
  congrArg (fun g : Poly K (n + 1) →ₐ[K] Poly K (n + 1) => g f) (restrict_comp_include e)

/-- The ambient linear variables that vanish identically on the subspace. -/
def unusedVariableIdeal : Ideal (Poly K (m + 1)) :=
  Ideal.span (X '' (Set.range (variableEmbedding e))ᶜ)

/-- The unused variables generate the entire kernel of restriction. -/
theorem ker_restrictPolynomials :
    RingHom.ker (restrictPolynomials (K := K) e).toRingHom = unusedVariableIdeal e := by
  apply le_antisymm
  · intro f hf
    let q := fun i => includePolynomials e (restrictPolynomials (K := K) e (X i))
    have hq : ∀ i, X i - q i ∈ unusedVariableIdeal e := by
      intro i
      by_cases hi : i ∈ Set.range (variableEmbedding e)
      · obtain ⟨j, rfl⟩ := hi
        simp [q]
      · simpa [q, hi, unusedVariableIdeal] using Ideal.subset_span (s := X '' (Set.range (variableEmbedding e))ᶜ)
          (a := (X i : Poly K (m + 1))) ⟨i, hi, rfl⟩
    have hcomp : (includePolynomials e).toRingHom.comp
        (restrictPolynomials (K := K) e).toRingHom = eval₂Hom C q := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [includePolynomials, restrictPolynomials]
      · intro i
        rw [RingHom.comp_apply, eval₂Hom_X']
        rfl
    have hs := sub_substitution_mem (unusedVariableIdeal e) q hq f
    change f - (eval₂Hom C q) f ∈ unusedVariableIdeal e at hs
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero, sub_zero] at hs
    exact hs
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact RingHom.mem_ker.mpr (restrictPolynomials_X_unused e i hi)

/-- Parametrizing an embedded point cone is restriction followed by its old parametrization. -/
private theorem singlePointConeParam_embedPoints (a : PointCoordinates K n p) (i : Fin p) :
    singlePointConeParam (fun j => embedPoints e a (i, j)) =
      (singlePointConeParam (fun j => a (i, j))).comp (restrictPolynomials e).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [singlePointConeParam, restrictPolynomials]
  · intro j
    change (singlePointConeParam fun j => embedPoints e a (i, j)) (X j) =
      (singlePointConeParam fun j => a (i, j)) (restrictPolynomials e (X j))
    refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [← variableEmbedding_last e, restrictPolynomials_X_image, variableEmbedding_last e]
      simp [singlePointConeParam]
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨u, rfl⟩ := hb
        rw [← variableEmbedding_castSucc e, restrictPolynomials_X_image, variableEmbedding_castSucc]
        simp [singlePointConeParam]
      · rw [restrictPolynomials_X_unused _ _ (castSucc_notMem_range e b hb), map_zero]
        simp [singlePointConeParam, hb]

/-- The ideal of the embedded configuration is the inverse image under restriction. -/
theorem pointIdeal_embedPoints_eq_comap (a : PointCoordinates K n p) :
    pointIdeal K (embedPoints e a) =
      (pointIdeal K a).comap (restrictPolynomials e).toRingHom := by
  unfold pointIdeal
  rw [Ideal.comap_iInf]
  congr 1
  funext i
  rw [singlePointIdeal_eq_ker, singlePointIdeal_eq_ker, singlePointConeParam_embedPoints]
  rfl

/-- Splitting off the linear equations gives the extension of the ideal in the subspace. -/
theorem pointIdeal_embedPoints (a : PointCoordinates K n p) :
    pointIdeal K (embedPoints e a) =
      (pointIdeal K a).map (includePolynomials e).toRingHom ⊔ unusedVariableIdeal e := by
  rw [pointIdeal_embedPoints_eq_comap, ← ker_restrictPolynomials]
  have hsurj : Function.Surjective (restrictPolynomials (K := K) e).toRingHom :=
    fun f => ⟨includePolynomials e f, restrict_include e f⟩
  have hmap : ((pointIdeal K a).map (includePolynomials e).toRingHom).map
      (restrictPolynomials e).toRingHom = pointIdeal K a := by
    change ((pointIdeal K a).map (includePolynomials e)).map (restrictPolynomials e) = _
    rw [Ideal.map_mapₐ, restrict_comp_include, Ideal.map_idₐ]
  calc
    _ = Ideal.comap (restrictPolynomials e).toRingHom
        (((pointIdeal K a).map (includePolynomials e).toRingHom).map
          (restrictPolynomials e).toRingHom) :=
      congrArg (Ideal.comap (restrictPolynomials e).toRingHom) hmap.symm
    _ = _ := Ideal.comap_map_of_surjective _ hsurj _

end IdealGeneration.CoordinateSubspace
