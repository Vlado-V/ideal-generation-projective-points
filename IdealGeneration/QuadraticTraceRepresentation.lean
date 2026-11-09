module

public import IdealGeneration.QuadraticAugmentedEvaluation
public import IdealGeneration.QuadraticTracePostulation
public import IdealGeneration.QuadraticVariableTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The trace equations in native flag coordinates and ambient cone coordinates. -/

noncomputable section
namespace IdealGeneration.QuadraticTraceRepresentation
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticTracePostulation
  QuadraticVariableTransport

variable {K T U P J E : Type*} [Field K] {m p q : ℕ}

/-- Renaming coordinates preserves the space of homogeneous quadrics. -/
def renameQuadricsEquiv (e : T ≃ U) : Quadrics K T ≃ₗ[K] Quadrics K U where
  toFun f := ⟨rename e f.val, f.property.rename_isHomogeneous⟩
  invFun f := ⟨rename e.symm f.val, f.property.rename_isHomogeneous⟩
  left_inv f := by
    apply Subtype.ext
    change rename e.symm (rename e f.val) = f.val
    rw [rename_rename, e.symm_comp_self, rename_id_apply]
  right_inv f := by
    apply Subtype.ext
    change rename e (rename e.symm f.val) = f.val
    rw [rename_rename, e.self_comp_symm, rename_id_apply]
  map_add' f g := by
    apply Subtype.ext
    exact map_add (rename e) f.val g.val
  map_smul' a f := by
    apply Subtype.ext
    exact (rename e).toLinearMap.map_smul a f.val

@[simp] theorem renameQuadricsEquiv_val (e : T ≃ U) (f : Quadrics K T) :
    (renameQuadricsEquiv e f).val = rename e f.val := rfl

theorem eval_renameQuadricsEquiv (e : T ≃ U) (x : T → K) (f : Quadrics K T) :
    eval (x ∘ e.symm) (renameQuadricsEquiv e f).val = eval x f.val := by
  rw [renameQuadricsEquiv_val, eval_rename]
  simp [Function.comp_def]

/-- Pairs of actual flag-vanishing quadrics. -/
abbrev FlagQuadricPairs (K P J : Type*) [Field K] :
    Submodule K (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod quadraticFlagVanishing

/-- Evaluate the two flag quadrics on the extra trace representatives. -/
def extraPairEvaluation (extra : E → (P × Bool) ⊕ J → K) :
    FlagQuadricPairs K P J →ₗ[K] (E → K × K) where
  toFun f t := (quadraticEvaluation extra f.val.1 t, quadraticEvaluation extra f.val.2 t)
  map_add' f g := by
    funext t
    apply Prod.ext
    · exact congrFun ((quadraticEvaluation extra).map_add f.val.1 g.val.1) t
    · exact congrFun ((quadraticEvaluation extra).map_add f.val.2 g.val.2) t
  map_smul' a f := by
    funext t
    apply Prod.ext
    · exact congrFun ((quadraticEvaluation extra).map_smul a f.val.1) t
    · exact congrFun ((quadraticEvaluation extra).map_smul a f.val.2) t

@[simp] theorem extraPairEvaluation_apply (extra : E → (P × Bool) ⊕ J → K)
    (f : FlagQuadricPairs K P J) (t : E) :
    extraPairEvaluation extra f t =
      (eval (extra t) f.val.1.val, eval (extra t) f.val.2.val) := by
  change (quadraticEvaluation extra f.val.1 t, quadraticEvaluation extra f.val.2 t) = _
  simp

theorem extraPairEvaluation_surjective (extra : E → (P × Bool) ⊕ J → K)
    (h : Function.Surjective ((quadraticEvaluation extra).comp
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).subtype)) :
    Function.Surjective (extraPairEvaluation extra) := by
  intro v
  obtain ⟨f, hf⟩ := h (fun t => (v t).1)
  obtain ⟨g, hg⟩ := h (fun t => (v t).2)
  refine ⟨⟨(f.val, g.val), f.property, g.property⟩, ?_⟩
  funext t
  exact Prod.ext (congrFun hf t) (congrFun hg t)

theorem mem_traceLabelEvaluation_ker_iff (extra : E → (P × Bool) ⊕ J → K)
    (f : Quadrics K ((P × Bool) ⊕ J)) :
    f ∈ (traceLabelEvaluation extra).ker ↔
      f ∈ quadraticFlagVanishing ∧ quadraticEvaluation extra f = 0 := by
  rw [traceLabelEvaluation_ker]
  rfl

/-- The two scalar trace equations carried by a pair in the extra evaluation kernel. -/
def extraPairKernelEquiv (extra : E → (P × Bool) ⊕ J → K) :
    (extraPairEvaluation extra).ker ≃ₗ[K]
      (traceLabelEvaluation extra).ker × (traceLabelEvaluation extra).ker where
  toFun f := by
    have hz := LinearMap.mem_ker.mp f.property
    exact (⟨f.val.val.1, (mem_traceLabelEvaluation_ker_iff extra _).mpr
      ⟨f.val.property.1, funext fun t => congrArg Prod.fst (congrFun hz t)⟩⟩,
      ⟨f.val.val.2, (mem_traceLabelEvaluation_ker_iff extra _).mpr
      ⟨f.val.property.2, funext fun t => congrArg Prod.snd (congrFun hz t)⟩⟩)
  invFun f := by
    have h₁ := (mem_traceLabelEvaluation_ker_iff extra _).mp f.1.property
    have h₂ := (mem_traceLabelEvaluation_ker_iff extra _).mp f.2.property
    refine ⟨⟨(f.1.val, f.2.val), h₁.1, h₂.1⟩, LinearMap.mem_ker.mpr ?_⟩
    funext t
    exact Prod.ext (congrFun h₁.2 t) (congrFun h₂.2 t)
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl
  map_add' f g := rfl
  map_smul' a f := rfl

variable (e : ((P × Bool) ⊕ J) ≃ Fin m) (C : ConeConfiguration K 2 m p q)
  (k : TraceLabel P J E ≃ Fin q) (extra : E → (P × Bool) ⊕ J → K)
  (htrace : ∀ t, C.trace (k t) = traceLabelPoint extra t ∘ e.symm)

include htrace in
/-- Point compatibility identifies the scalar trace kernels under coordinate renaming. -/
theorem renameQuadrics_mem_tracePiece_iff (f : Quadrics K ((P × Bool) ⊕ J)) :
    renameQuadricsEquiv e f ∈ C.tracePiece 2 ↔ f ∈ (traceLabelEvaluation extra).ker := by
  rw [C.mem_tracePiece, LinearMap.mem_ker]
  constructor
  · intro h
    funext t
    have ht := h (k t)
    rw [htrace, eval_renameQuadricsEquiv] at ht
    simpa [traceLabelEvaluation] using ht
  · intro h i
    obtain ⟨t, rfl⟩ := k.surjective i
    rw [htrace, eval_renameQuadricsEquiv]
    simpa [traceLabelEvaluation] using congrFun h t

/-- Rename the actual scalar equations into the trace coordinates of the cone. -/
def scalarTraceEquiv : (traceLabelEvaluation extra).ker ≃ₗ[K] C.tracePiece 2 :=
  (renameQuadricsEquiv e).ofSubmodules _ _ (by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (renameQuadrics_mem_tracePiece_iff e C k extra htrace g).mpr hg
    · intro hf
      refine ⟨(renameQuadricsEquiv (K := K) e).symm f, ?_, LinearEquiv.apply_symm_apply _ _⟩
      apply (renameQuadrics_mem_tracePiece_iff e C k extra htrace _).mp
      simpa using hf)

@[simp] theorem scalarTraceEquiv_val (f : (traceLabelEvaluation extra).ker) :
    (scalarTraceEquiv e C k extra htrace f).val.val = rename e f.val.val := rfl

/-- Identify the pairs vanishing on the added probes with two actual trace equations. -/
def traceEquationEquiv : (extraPairEvaluation extra).ker ≃ₗ[K] (Fin 2 → C.tracePiece 2) :=
  ((extraPairKernelEquiv extra).trans ((scalarTraceEquiv e C k extra htrace).prodCongr
    (scalarTraceEquiv e C k extra htrace))).trans
    (LinearEquiv.finTwoArrow K (C.tracePiece 2)).symm

@[simp] theorem traceEquationEquiv_zero (f : (extraPairEvaluation extra).ker) :
    (traceEquationEquiv e C k extra htrace f 0).val.val = rename e f.val.val.1.val := rfl

@[simp] theorem traceEquationEquiv_one (f : (extraPairEvaluation extra).ker) :
    (traceEquationEquiv e C k extra htrace f 1).val.val = rename e f.val.val.2.val := rfl

theorem coneExtend_rename (f : MvPolynomial ((P × Bool) ⊕ J) K) :
    coneExtend K 2 m (rename e f) = rename (traceIndex e) f := by
  rw [coneExtend, rename_rename]
  rfl

/-- Flattening normal multiplication gives the normal multiples of the transported equations. -/
theorem flatten_normalPairMap_traceEquationEquiv (f : (extraPairEvaluation extra).ker) :
    flatten e (normalPairMap (f.val.val.1.val, f.val.val.2.val)) =
      ∑ i : Fin 2, X (i.castAdd m) * coneExtend K 2 m
        (traceEquationEquiv e C k extra htrace f i).val.val := by
  rw [flatten_normalPairMap, Fin.sum_univ_two, traceEquationEquiv_zero, traceEquationEquiv_one,
    coneExtend_rename, coneExtend_rename]
  change rename (traceIndex e) f.val.val.1.val * X ((0 : Fin 2).castAdd m) +
    rename (traceIndex e) f.val.val.2.val * X ((1 : Fin 2).castAdd m) = _
  simp only [mul_comm]

/-- The formula for normal trace multiplication in the ambient polynomial ring. -/
theorem normalTraceMultiplication_polynomial (f : Fin 2 → C.tracePiece 2) :
    (C.normalTraceMultiplication 2 f).val.val =
      ∑ i : Fin 2, X (i.castAdd m) * coneExtend K 2 m (f i).val.val := by
  change (formMultiplication K (2 + m) 2 (C.normalTraceCoefficients 2 f)).val = _
  rw [formMultiplication_val, Fin.sum_univ_add]
  simp [ConeConfiguration.normalTraceCoefficients, coneExtendForm]

theorem flatten_normalPairMap_normalTraceMultiplication (f : (extraPairEvaluation extra).ker) :
    flatten e (normalPairMap (f.val.val.1.val, f.val.val.2.val)) =
      (C.normalTraceMultiplication 2 (traceEquationEquiv e C k extra htrace f)).val.val := by
  rw [normalTraceMultiplication_polynomial, flatten_normalPairMap_traceEquationEquiv]

local instance residualCubicGroup : AddCommGroup (C.residualPiece 3) :=
  Module.addCommMonoidToAddCommGroup K

local instance flagPairGroup : AddCommGroup (FlagQuadricPairs K P J) :=
  Module.addCommMonoidToAddCommGroup K

/-- The augmented residual product map is the cone middle map in the trace coordinates. -/
theorem middleMultiplication_comp_traceEquationEquiv
    (g : FlagQuadricPairs K P J →ₗ[K] C.residualPiece 3)
    (hg : ∀ b, (g b).val.val = flatten e (normalPairMap (b.val.1.val, b.val.2.val))) :
    (C.middleMultiplication 2).comp
      ((LinearEquiv.refl K (Fin (2 + m) → C.residualPiece 2)).prodCongr
        (traceEquationEquiv e C k extra htrace)).toLinearMap =
      QuadraticAugmentedEvaluation.augmented (C.residualMultiplication 2) g
        (extraPairEvaluation extra) := by
  apply LinearMap.ext
  rintro ⟨d, v⟩
  have hv : C.normalTraceMultiplication 2 (traceEquationEquiv e C k extra htrace v) =
      g v.val := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hg]
    exact (flatten_normalPairMap_normalTraceMultiplication e C k extra htrace v).symm
  change C.residualMultiplication 2 d +
    C.normalTraceMultiplication 2 (traceEquationEquiv e C k extra htrace v) =
    C.residualMultiplication 2 d + g v.val
  rw [hv]

end IdealGeneration.QuadraticTraceRepresentation
