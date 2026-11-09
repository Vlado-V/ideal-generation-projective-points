module

public import IdealGeneration.TripleNormalReduction
public import IdealGeneration.TripleNormalScalarExtension

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! # Source coordinates for the three-variable enlargement -/

noncomputable section
namespace IdealGeneration.TripleNormal
open Module
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

/-- The pure-normal part of the source of the reduced coefficient map. -/
abbrev PureOmega (K : Type*) [Field K] := (formMultiplication K 3 2).ker

/-- Coordinates on the reduced source with h base variables and four layers. -/
abbrev SourceCoordinates (K : Type*) [Field K] (h : ℕ) :=
  (PureOmega K × (Fin 3 → Fin h → K)) × (Fin (h + 4) → Fin h → K)

/-- The nine new normal motions, the three groups of products involving
new base variables, and the twelve products of new kernel vectors with layers. -/
abbrev NewSourceCoordinates (K : Type*) (h : ℕ) :=
  (Fin 3 → Fin 3 → K) ×
    ((Fin 3 → Fin h → K) ×
      ((Fin h → Fin 3 → K) × ((Fin 3 → Fin 3 → K) × (Fin 4 → Fin 3 → K))))

variable {K : Type*} [Field K]

private theorem oldTraceIndex_on_base (h : ℕ) (i : Fin h) :
    oldTraceIndex h (i.castAdd 4) = (i.castAdd 3).castAdd 4 := by
  simp only [oldTraceIndex, Fin.addCases_left]
  rfl

private theorem oldTraceIndex_on_layer (h : ℕ) (j : Fin 4) :
    oldTraceIndex h (j.natAdd h) = j.natAdd (h + 3) := by
  simp only [oldTraceIndex, Fin.addCases_right]
  rfl

/-- Separate the retained coefficients and the five groups of new coefficients. -/
def splitSourceCoordinates (h : ℕ) :
    SourceCoordinates K (h + 3) ≃ₗ[K] SourceCoordinates K h × NewSourceCoordinates K h where
  toFun x :=
    (((x.1.1, fun a i => x.1.2 a (i.castAdd 3)),
      fun j i => x.2 (oldTraceIndex h j) (i.castAdd 3)),
      (fun a b => x.1.2 a (b.natAdd h),
        fun b i => x.2 ((b.natAdd h).castAdd 4) (i.castAdd 3),
        fun j b => x.2 ((j.castAdd 3).castAdd 4) (b.natAdd h),
        fun j b => x.2 ((j.natAdd h).castAdd 4) (b.natAdd h),
        fun j b => x.2 (j.natAdd (h + 3)) (b.natAdd h)))
  invFun x :=
    let (motions, oldHNewY, newHOldY, newHNewY, newHZ) := x.2
    ((x.1.1.1, fun a => Fin.append (x.1.1.2 a) (motions a)),
      Fin.addCases
        (Fin.addCases
          (fun j : Fin h => Fin.append (x.1.2 (j.castAdd 4)) (newHOldY j))
          (fun j : Fin 3 => Fin.append (oldHNewY j) (newHNewY j)))
        (fun j : Fin 4 => Fin.append (x.1.2 (j.natAdd h)) (newHZ j)))
  left_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext a i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    · funext j i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
            simp [oldTraceIndex_on_base]
        · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp [oldTraceIndex_on_layer]
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext a i
          simp
      · funext j i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp [oldTraceIndex_on_base]
        · simp [oldTraceIndex_on_layer]
    · apply Prod.ext
      · funext a b
        simp
      · apply Prod.ext
        · funext b i
          simp
        · apply Prod.ext
          · funext j b
            simp
          · apply Prod.ext
            · funext j b
              simp
            · funext j b
              simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction retains the pure block, the old motions, and products whose
two indices are old. The old trace index includes all four layers. -/
def sourceCoordinateRestriction (h : ℕ) :
    SourceCoordinates K (h + 3) →ₗ[K] SourceCoordinates K h :=
  (LinearMap.fst K _ _).comp (splitSourceCoordinates (K := K) h).toLinearMap

@[simp] theorem sourceCoordinateRestriction_apply (h : ℕ) (x : SourceCoordinates K (h + 3)) :
    sourceCoordinateRestriction h x =
      ((x.1.1, fun a i => x.1.2 a (i.castAdd 3)),
        fun j i => x.2 (oldTraceIndex h j) (i.castAdd 3)) := rfl

/-- Every old source coordinate tuple extends by setting the five new blocks to zero. -/
theorem sourceCoordinateRestriction_surjective (h : ℕ) :
    Function.Surjective (sourceCoordinateRestriction (K := K) h) := by
  intro x
  let e := splitSourceCoordinates (K := K) h
  refine ⟨e.symm (x, 0), ?_⟩
  change (e (e.symm (x, 0))).1 = x
  rw [LinearEquiv.apply_symm_apply]

/-- The kernel of coordinate restriction is exactly the five new blocks. -/
def sourceCoordinateRestrictionKernelEquiv (h : ℕ) :
    (sourceCoordinateRestriction (K := K) h).ker ≃ₗ[K] NewSourceCoordinates K h := by
  let e := splitSourceCoordinates (K := K) h
  exact
    { toFun := fun x => (e x.val).2
      invFun := fun x => ⟨e.symm (0, x), by
        change (e (e.symm (0, x))).1 = 0
        rw [LinearEquiv.apply_symm_apply]⟩
      left_inv := fun x => Subtype.ext (e.injective (by
        rw [LinearEquiv.apply_symm_apply]
        exact Prod.ext (LinearMap.mem_ker.mp x.property).symm rfl))
      right_inv := fun x => by simp
      map_add' := fun x y => congrArg Prod.snd (e.map_add x.val y.val)
      map_smul' := fun c x => congrArg Prod.snd (e.map_smul c x.val) }

/-- The new source block consists of 6h+30 independent coordinates. -/
theorem finrank_sourceCoordinateRestriction_ker (h : ℕ) :
    finrank K (sourceCoordinateRestriction (K := K) h).ker = 6 * h + 30 := by
  rw [(sourceCoordinateRestrictionKernelEquiv (K := K) h).finrank_eq]
  simp [NewSourceCoordinates, Module.finrank_prod, Module.finrank_pi_fintype]
  omega

section ActualSource

variable {h p q : ℕ} (C : ConeConfiguration K 3 (h + 4) p q)
variable (e : C.residualPiece 2 ≃ₗ[K] Forms K 3 2 × (Fin h → K))
variable (he : ∀ F, (e F).1 = quadraticRestriction C F)

/-- The second coordinates of a split residual quadratic give coordinates
on the actual mixed kernel. -/
def mixedKernelCoordinatesEquiv : MixedKernel C ≃ₗ[K] (Fin h → K) where
  toFun F := (e F.val).2
  invFun a := ⟨e.symm (0, a), by
    apply LinearMap.mem_ker.mpr
    rw [← he, LinearEquiv.apply_symm_apply]⟩
  left_inv F := by
    apply Subtype.ext
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · rw [he]
      exact (LinearMap.mem_ker.mp F.property).symm
    · rfl
  right_inv a := congrArg Prod.snd (e.apply_symm_apply (0, a))
  map_add' F G := congrArg Prod.snd (e.map_add F.val G.val)
  map_smul' a F := congrArg Prod.snd (e.map_smul a F.val)

/-- The actual cubic constraint uses only the first coordinates of the
three split residual quadratics. Their other coordinates are free. -/
def omegaCoordinatesEquiv : Omega C ≃ₗ[K] PureOmega K × (Fin 3 → Fin h → K) where
  toFun F :=
    (⟨fun a => (e (F.val a)).1, by
      change formMultiplication K 3 2 (fun a => (e (F.val a)).1) = 0
      simp only [he]
      exact F.property⟩,
      fun a => (e (F.val a)).2)
  invFun x := ⟨fun a => e.symm (x.1.val a, x.2 a), by
    change formMultiplication K 3 2 (fun a =>
      quadraticRestriction C (e.symm (x.1.val a, x.2 a))) = 0
    simp only [← he, LinearEquiv.apply_symm_apply]
    exact x.1.property⟩
  left_inv F := by
    apply Subtype.ext
    funext a
    exact e.symm_apply_apply (F.val a)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext a
      exact congrArg Prod.fst (e.apply_symm_apply (x.1.val a, x.2 a))
    · funext a
      exact congrArg Prod.snd (e.apply_symm_apply (x.1.val a, x.2 a))
  map_add' F G := by
    apply Prod.ext
    · apply Subtype.ext
      funext a
      exact congrArg Prod.fst (e.map_add (F.val a) (G.val a))
    · funext a
      exact congrArg Prod.snd (e.map_add (F.val a) (G.val a))
  map_smul' c F := by
    apply Prod.ext
    · apply Subtype.ext
      funext a
      exact congrArg Prod.fst (e.map_smul c (F.val a))
    · funext a
      exact congrArg Prod.snd (e.map_smul c (F.val a))

/-- A compatible quadratic splitting gives coordinates on the full source
of the actual reduced evaluation map. -/
def evaluationSourceCoordinatesEquiv : EvaluationSource C ≃ₗ[K] SourceCoordinates K h :=
  (omegaCoordinatesEquiv C e he).prodCongr
    (LinearEquiv.piCongrRight (fun _ => mixedKernelCoordinatesEquiv C e he))

end ActualSource

section Compatibility

variable {h p q p' q' : ℕ}
  {C : ConeConfiguration K 3 (h + 4) p q}
  {C' : ConeConfiguration K 3 (h + 3 + 4) p' q'}

/-- Compatibility of residual quadratic coordinates implies compatibility
of both summands in the actual reduced source. -/
theorem evaluationSourceRestriction_coordinates
    (r : C'.residualPiece 2 →ₗ[K] C.residualPiece 2)
    (R : EvaluationSource C' →ₗ[K] EvaluationSource C)
    (e : C.residualPiece 2 ≃ₗ[K] Forms K 3 2 × (Fin h → K))
    (e' : C'.residualPiece 2 ≃ₗ[K] Forms K 3 2 × (Fin (h + 3) → K))
    (he : ∀ F, (e F).1 = quadraticRestriction C F)
    (he' : ∀ F, (e' F).1 = quadraticRestriction C' F)
    (hr : ∀ F, e (r F) = ((e' F).1, fun i : Fin h => (e' F).2 (i.castAdd 3)))
    (hOmega : ∀ x a, (R x).1.val a = r (x.1.val a))
    (hMixed : ∀ x j, ((R x).2 j).val = r ((x.2 (oldTraceIndex h j)).val))
    (x : EvaluationSource C') :
    evaluationSourceCoordinatesEquiv C e he (R x) =
      sourceCoordinateRestriction h (evaluationSourceCoordinatesEquiv C' e' he' x) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      funext a
      change (e ((R x).1.val a)).1 = (e' (x.1.val a)).1
      rw [hOmega, hr]
    · funext a i
      change (e ((R x).1.val a)).2 i = (e' (x.1.val a)).2 (i.castAdd 3)
      rw [hOmega, hr]
  · funext j i
    change (e (((R x).2 j).val)).2 i = (e' ((x.2 (oldTraceIndex h j)).val)).2 (i.castAdd 3)
    rw [hMixed, hr]

end Compatibility

section ActualRestriction

variable {h p q p' q' : ℕ}
  {C : ConeConfiguration K 3 (h + 4) p q}
  {C' : ConeConfiguration K 3 (h + 3 + 4) p' q'}
  (R : EvaluationSource C' →ₗ[K] EvaluationSource C)
  (e : EvaluationSource C ≃ₗ[K] SourceCoordinates K h)
  (e' : EvaluationSource C' ≃ₗ[K] SourceCoordinates K (h + 3))
  (hR : ∀ x, e (R x) = sourceCoordinateRestriction h (e' x))

include hR in
/-- A restriction compatible with the source coordinates is onto. -/
theorem evaluationSourceRestriction_surjective : Function.Surjective R := by
  intro x
  obtain ⟨y, hy⟩ := sourceCoordinateRestriction_surjective h (e x)
  refine ⟨e'.symm y, e.injective ?_⟩
  rw [hR, LinearEquiv.apply_symm_apply, hy]

/-- A restriction compatible with the source coordinates has the five
new blocks as its actual linear kernel. -/
def evaluationSourceRestrictionKernelEquiv :
    R.ker ≃ₗ[K] NewSourceCoordinates K h := by
  let U := sourceCoordinateRestriction (K := K) h
  have hmap : R.ker.map e'.toLinearMap = U.ker := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      apply LinearMap.mem_ker.mpr
      change sourceCoordinateRestriction h (e' v) = 0
      rw [← hR, LinearMap.mem_ker.mp hv, e.map_zero]
    · intro hu
      refine ⟨e'.symm u, LinearMap.mem_ker.mpr ?_, e'.apply_symm_apply u⟩
      apply e.injective
      rw [hR, LinearEquiv.apply_symm_apply, e.map_zero]
      exact LinearMap.mem_ker.mp hu
  exact (e'.ofSubmodules R.ker U.ker hmap).trans (sourceCoordinateRestrictionKernelEquiv h)

include hR in
/-- The actual restriction kernel has the dimension required by the new rows. -/
theorem finrank_evaluationSourceRestriction_ker :
    finrank K R.ker = 6 * h + 30 := by
  rw [(evaluationSourceRestrictionKernelEquiv R e e' hR).finrank_eq,
    ← (sourceCoordinateRestrictionKernelEquiv (K := K) h).finrank_eq,
    finrank_sourceCoordinateRestriction_ker]

end ActualRestriction

end IdealGeneration.TripleNormal
