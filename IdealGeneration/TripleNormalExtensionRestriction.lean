module

public import IdealGeneration.TripleNormalSupportedExtension
public import IdealGeneration.NormalDegree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Restriction of equations under the three-variable enlargement

Setting the three new base variables to zero recovers the old trace and
old cone equations. It commutes with both pure trace and pure normal
restriction.
-/

noncomputable section
namespace IdealGeneration.TripleNormal
open MvPolynomial NormalDegree

variable {K : Type*} [Field K] {h p q r : ℕ}

private def traceExtensionSubstitution (h : ℕ) :
    Fin (h + 3 + 4) → Poly K (h + 4) :=
  Fin.addCases
    (Fin.addCases (fun i : Fin h => X (i.castAdd 4)) (fun _ : Fin 3 => 0))
    (fun j : Fin 4 => X (j.natAdd h))

/-- Set the three new base variables to zero on the trace. -/
def extensionTraceRestriction (h : ℕ) : Poly K (h + 3 + 4) →ₐ[K] Poly K (h + 4) :=
  aeval (traceExtensionSubstitution h)

private def ambientExtensionSubstitution (h : ℕ) :
    Fin (3 + (h + 3 + 4)) → Poly K (3 + (h + 4)) :=
  Fin.addCases (fun j : Fin 3 => X (j.castAdd (h + 4)))
    (fun j : Fin (h + 3 + 4) => coneExtend K 3 (h + 4) (traceExtensionSubstitution h j))

/-- Set the three new base variables to zero in the ambient ring. -/
def extensionAmbientRestriction (h : ℕ) :
    Poly K (3 + (h + 3 + 4)) →ₐ[K] Poly K (3 + (h + 4)) :=
  aeval (ambientExtensionSubstitution h)

private theorem traceExtensionSubstitution_homogeneous (j : Fin (h + 3 + 4)) :
    (traceExtensionSubstitution (K := K) h j).IsHomogeneous 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [traceExtensionSubstitution, Fin.addCases_left] using
        isHomogeneous_X K (k.castAdd 4)
    · simpa only [traceExtensionSubstitution, Fin.addCases_left, Fin.addCases_right] using
        (isHomogeneous_zero (σ := Fin (h + 4)) (R := K) 1)
  · simpa only [traceExtensionSubstitution, Fin.addCases_right] using
      isHomogeneous_X K (i.natAdd h)

private theorem ambientExtensionSubstitution_homogeneous (j : Fin (3 + (h + 3 + 4))) :
    (ambientExtensionSubstitution (K := K) h j).IsHomogeneous 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [ambientExtensionSubstitution, Fin.addCases_left] using
      isHomogeneous_X K (i.castAdd (h + 4))
  · simpa only [ambientExtensionSubstitution, Fin.addCases_right, coneExtend] using
      (traceExtensionSubstitution_homogeneous (K := K) i).rename_isHomogeneous
        (f := Fin.natAdd 3)

/-- The restriction of a homogeneous trace form has the same degree. -/
def extensionTraceRestrictionForm (h d : ℕ) : Forms K (h + 3 + 4) d →ₗ[K] Forms K (h + 4) d where
  toFun f := ⟨extensionTraceRestriction h f.val, by
    change (extensionTraceRestriction h f.val).IsHomogeneous d
    simpa only [extensionTraceRestriction, one_mul] using
      f.property.aeval (n := 1) (traceExtensionSubstitution h)
        traceExtensionSubstitution_homogeneous⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The restriction of a homogeneous ambient form has the same degree. -/
def extensionAmbientRestrictionForm (h d : ℕ) :
    Forms K (3 + (h + 3 + 4)) d →ₗ[K] Forms K (3 + (h + 4)) d where
  toFun f := ⟨extensionAmbientRestriction h f.val, by
    change (extensionAmbientRestriction h f.val).IsHomogeneous d
    simpa only [extensionAmbientRestriction, one_mul] using
      f.property.aeval (n := 1) (ambientExtensionSubstitution h)
        ambientExtensionSubstitution_homogeneous⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Evaluating a trace restriction agrees with evaluation at the zero-extended point. -/
theorem eval_extensionTraceRestriction (x : Fin (h + 4) → K) (f : Poly K (h + 3 + 4)) :
    eval x (extensionTraceRestriction h f) = eval (embedOldTrace x) f := by
  have heq : (eval x).comp (extensionTraceRestriction h).toRingHom = eval (embedOldTrace x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [extensionTraceRestriction]
    · intro j
      change eval x (extensionTraceRestriction h (X j)) = eval (embedOldTrace x) (X j)
      rw [extensionTraceRestriction, aeval_X, eval_X]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
          simp [traceExtensionSubstitution, embedOldTrace]
      · simp [traceExtensionSubstitution, embedOldTrace]
  exact DFunLike.congr_fun heq f

/-- Evaluating an ambient restriction agrees with evaluation at the zero-extended point. -/
theorem eval_extensionAmbientRestriction (x : Fin (3 + (h + 4)) → K)
    (f : Poly K (3 + (h + 3 + 4))) :
    eval x (extensionAmbientRestriction h f) = eval (embedOldAmbient x) f := by
  have heq : (eval x).comp (extensionAmbientRestriction h).toRingHom =
      eval (embedOldAmbient x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [extensionAmbientRestriction]
    · intro j
      change eval x (extensionAmbientRestriction h (X j)) = eval (embedOldAmbient x) (X j)
      rw [extensionAmbientRestriction, aeval_X, eval_X]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [ambientExtensionSubstitution, embedOldAmbient]
      · simp only [ambientExtensionSubstitution, Fin.addCases_right, embedOldAmbient,
          Fin.append_right, coneExtend, eval_rename]
        simpa only [extensionTraceRestriction, aeval_X, eval_X, Function.comp_def] using
          eval_extensionTraceRestriction (x ∘ Fin.natAdd 3) (X i)
  exact DFunLike.congr_fun heq f

/-- The pure-trace restriction commutes with deleting the new base variables. -/
theorem coneRestrict_extensionAmbientRestriction (f : Poly K (3 + (h + 3 + 4))) :
    coneRestrict K 3 (h + 4) (extensionAmbientRestriction h f) =
      extensionTraceRestriction h (coneRestrict K 3 (h + 3 + 4) f) := by
  have heq : (coneRestrict K 3 (h + 4)).comp (extensionAmbientRestriction h) =
      (extensionTraceRestriction h).comp (coneRestrict K 3 (h + 3 + 4)) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [extensionAmbientRestriction, ambientExtensionSubstitution]
    · simp [extensionAmbientRestriction, ambientExtensionSubstitution, extensionTraceRestriction]
  exact DFunLike.congr_fun heq f

/-- Deleting new base variables leaves the pure-normal part unchanged. -/
theorem pureRestrict_extensionAmbientRestriction (f : Poly K (3 + (h + 3 + 4))) :
    pureRestrict K 3 (h + 4) (extensionAmbientRestriction h f) =
      pureRestrict K 3 (h + 3 + 4) f := by
  have heq : (pureRestrict K 3 (h + 4)).comp (extensionAmbientRestriction h) =
      pureRestrict K 3 (h + 3 + 4) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [extensionAmbientRestriction, ambientExtensionSubstitution]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) k <;>
          simp [extensionAmbientRestriction, ambientExtensionSubstitution,
            traceExtensionSubstitution]
      · simp [extensionAmbientRestriction, ambientExtensionSubstitution,
          traceExtensionSubstitution]
  exact DFunLike.congr_fun heq f

/-- Restrict an enlarged cone equation in the normal ideal to the old cone. -/
def supportedExtensionResidualRestriction (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K)
    (d : ℕ) :
    (supportedExtension C a ζ normal).residualPiece d →ₗ[K] C.residualPiece d :=
  ((extensionAmbientRestrictionForm h d).comp
    ((supportedExtension C a ζ normal).residualPiece d).subtype).codRestrict _ (by
    intro f
    refine ⟨?_, ?_⟩
    · apply (C.mem_conePiece _).mpr
      intro i
      change eval (C.point i) (extensionAmbientRestriction h f.val.val) = 0
      rw [eval_extensionAmbientRestriction, ← supportedExtension_point_old C a ζ normal i]
      exact ((supportedExtension C a ζ normal).mem_conePiece f.val).mp f.property.1 (i.castAdd 6)
    · apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change coneRestrict K 3 (h + 4) (extensionAmbientRestriction h f.val.val) = 0
      rw [coneRestrict_extensionAmbientRestriction]
      have hzero : coneRestrict K 3 (h + 3 + 4) f.val.val = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp f.property.2)
      rw [hzero, map_zero])

/-- Restrict an equation of the enlarged trace to the old trace. -/
def supportedExtensionTraceRestriction (C : ConeConfiguration K 3 (h + 4) p q)
    (a : Fin r × Fin (h + 3) → K) (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K)
    (d : ℕ) :
    (supportedExtension C a ζ normal).tracePiece d →ₗ[K] C.tracePiece d :=
  ((extensionTraceRestrictionForm h d).comp
    ((supportedExtension C a ζ normal).tracePiece d).subtype).codRestrict _ (by
    intro f
    apply (C.mem_tracePiece _).mpr
    intro i
    change eval (C.trace i) (extensionTraceRestriction h f.val.val) = 0
    rw [eval_extensionTraceRestriction, ← supportedExtension_trace_old C a ζ normal i]
    exact ((supportedExtension C a ζ normal).mem_tracePiece f.val).mp f.property
      (i.castAdd (3 + (r + 4))))

/-- Restricting an enlarged residual form leaves its pure normal form unchanged. -/
theorem supportedExtensionResidualRestriction_pureRestrict
    (C : ConeConfiguration K 3 (h + 4) p q) (a : Fin r × Fin (h + 3) → K)
    (ζ : Fin 4 → K) (normal : Fin 3 → Fin 2 → Fin 3 → K) (d : ℕ)
    (f : (supportedExtension C a ζ normal).residualPiece d) :
    pureRestrictForm K 3 (h + 4) d (supportedExtensionResidualRestriction C a ζ normal d f).val =
      pureRestrictForm K 3 (h + 3 + 4) d f.val := by
  apply Subtype.ext
  exact pureRestrict_extensionAmbientRestriction f.val.val

@[simp] theorem oldTraceIndex_base (i : Fin h) :
    oldTraceIndex h (i.castAdd 4) = (i.castAdd 3).castAdd 4 := by
  simp only [oldTraceIndex, Fin.addCases_left]
  rfl

@[simp] theorem oldTraceIndex_layer (j : Fin 4) :
    oldTraceIndex h (j.natAdd h) = j.natAdd (h + 3) := by
  simp only [oldTraceIndex, Fin.addCases_right]
  rfl

/-- Each original ambient coordinate variable survives restriction. -/
@[simp] theorem extensionAmbientRestriction_X_old (j : Fin (3 + (h + 4))) :
    extensionAmbientRestriction (K := K) h (X (oldAmbientIndex h j)) = X j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [extensionAmbientRestriction, ambientExtensionSubstitution, oldAmbientIndex]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp [extensionAmbientRestriction, ambientExtensionSubstitution,
        traceExtensionSubstitution, oldAmbientIndex]

/-- Each new base coordinate variable restricts to zero. -/
@[simp] theorem extensionAmbientRestriction_X_new (b : Fin 3) :
    extensionAmbientRestriction (K := K) h (X (((b.natAdd h).castAdd 4).natAdd 3)) = 0 := by
  simp [extensionAmbientRestriction, ambientExtensionSubstitution, traceExtensionSubstitution]

/-- Restricting coordinate multiplication gives the old multiplication
on the surviving coefficients, with each coefficient restricted in degree. -/
theorem extensionAmbientRestrictionForm_multiplication (d : ℕ)
    (f : Fin (3 + (h + 3 + 4)) → Forms K (3 + (h + 3 + 4)) d) :
    extensionAmbientRestrictionForm h (d + 1) (formMultiplication K (3 + (h + 3 + 4)) d f) =
      formMultiplication K (3 + (h + 4)) d
        (fun j => extensionAmbientRestrictionForm h d (f (oldAmbientIndex h j))) := by
  apply Subtype.ext
  change extensionAmbientRestriction h (∑ j, X j * (f j).val) =
    ∑ j, X j * extensionAmbientRestriction h (f (oldAmbientIndex h j)).val
  simp only [map_add, map_sum, map_mul, Fin.sum_univ_add, oldAmbientIndex, Fin.addCases_left,
    Fin.addCases_right, oldTraceIndex_base, oldTraceIndex_layer, extensionAmbientRestriction,
    aeval_X, ambientExtensionSubstitution, traceExtensionSubstitution,
    coneExtend_X, map_zero, zero_mul, Finset.sum_const_zero, add_zero]

/-- The old and new pure-normal extensions agree after restriction. -/
theorem extensionAmbientRestriction_pureExtend (f : Poly K 3) :
    extensionAmbientRestriction h (pureExtend K 3 (h + 3 + 4) f) =
      pureExtend K 3 (h + 4) f := by
  have heq : (extensionAmbientRestriction h).comp (pureExtend K 3 (h + 3 + 4)) =
      pureExtend K 3 (h + 4) := by
    apply MvPolynomial.algHom_ext
    intro j
    change extensionAmbientRestriction h (pureExtend K 3 (h + 3 + 4) (X j)) =
      pureExtend K 3 (h + 4) (X j)
    rw [pureExtend_X, pureExtend_X]
    simpa only [oldAmbientIndex, Fin.addCases_left] using
      (extensionAmbientRestriction_X_old (K := K) (h := h) (j.castAdd (h + 4)))
  exact DFunLike.congr_fun heq f

/-- Extending a trace form and then restricting agrees with restricting
on the trace first. -/
theorem extensionAmbientRestriction_coneExtend (f : Poly K (h + 3 + 4)) :
    extensionAmbientRestriction h (coneExtend K 3 (h + 3 + 4) f) =
      coneExtend K 3 (h + 4) (extensionTraceRestriction h f) := by
  have heq : (extensionAmbientRestriction h).comp (coneExtend K 3 (h + 3 + 4)) =
      (coneExtend K 3 (h + 4)).comp (extensionTraceRestriction h) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [extensionAmbientRestriction, ambientExtensionSubstitution, extensionTraceRestriction]
  exact DFunLike.congr_fun heq f

end IdealGeneration.TripleNormal
