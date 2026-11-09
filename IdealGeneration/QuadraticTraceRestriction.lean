module

public import IdealGeneration.QuadraticFlagInterpolation
public import IdealGeneration.QuadraticLinearForms

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Polynomial and point restriction along an embedding of trace variables. -/

noncomputable section
namespace IdealGeneration.QuadraticTraceRestriction
open MvPolynomial QuadraticFlag

variable {α β : Type*}

/-- A sum supported on an embedded finite set can be taken over that set. -/
theorem sum_over_embedding {M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    (e : α ↪ β) (f : β → M) (hoff : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j, f j = ∑ i, f (e i) := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.map e, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hoff j
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    _ = _ := Finset.sum_map _ _ _

variable (K : Type*) [Field K] (e : α ↪ β)

/-- Retain the selected variables and set every other variable to zero. -/
def restrictPolynomial : MvPolynomial β K →ₐ[K] MvPolynomial α K :=
  MvPolynomial.killCompl e.injective

@[simp] theorem restrict_X_embedded (i : α) :
    restrictPolynomial K e (X (e i)) = X i := by
  simpa only [restrictPolynomial, rename_X] using
    (MvPolynomial.killCompl_rename_app e.injective (X i : MvPolynomial α K))

theorem restrict_X_off {j : β} (hj : j ∉ Set.range e) :
    restrictPolynomial K e (X j) = 0 := by
  classical
  unfold restrictPolynomial MvPolynomial.killCompl
  rw [aeval_X, dite_eq_right hj]

/-- The corresponding embedding of point coordinates extends by zero. -/
def extendPoint (x : α → K) (j : β) : K :=
  eval x (restrictPolynomial K e (X j))

@[simp] theorem extendPoint_embedded (x : α → K) (i : α) :
    extendPoint K e x (e i) = x i := by
  simp [extendPoint]

theorem extendPoint_off (x : α → K) {j : β} (hj : j ∉ Set.range e) :
    extendPoint K e x j = 0 := by
  simp [extendPoint, restrict_X_off K e hj]

/-- Restriction preserves homogeneous degree. -/
theorem restrict_homogeneous {f : MvPolynomial β K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (restrictPolynomial K e f).IsHomogeneous d := by
  classical
  have hvar (j : β) : (restrictPolynomial K e (X j)).IsHomogeneous 1 := by
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [restrict_X_embedded]
      exact isHomogeneous_X K i
    · rw [restrict_X_off K e hj]
      exact isHomogeneous_zero _ _ 1
  have heq : aeval (fun j => restrictPolynomial K e (X j)) = restrictPolynomial K e := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [aeval_X]
  simpa only [heq, one_mul] using hf.aeval _ hvar

/-- Evaluating a restriction is evaluating the original polynomial on the embedded point. -/
theorem eval_restrict (x : α → K) (f : MvPolynomial β K) :
    eval x (restrictPolynomial K e f) = eval (extendPoint K e x) f := by
  have h : (eval x).comp (restrictPolynomial K e).toRingHom = eval (extendPoint K e x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      change extendPoint K e x j = eval (extendPoint K e x) (X j)
      rw [eval_X]
  exact DFunLike.congr_fun h f

@[simp] theorem extendPoint_coordinate [DecidableEq α] [DecidableEq β] (i : α) :
    extendPoint K e (coordinatePoint i) = coordinatePoint (e i) := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hj
    simp [coordinatePoint, e.injective.eq_iff]
  · rw [extendPoint_off K e _ hj]
    have hne : j ≠ e i := fun h => hj ⟨i, h.symm⟩
    simp [coordinatePoint, hne]

@[simp] theorem extendPoint_add (x y : α → K) :
    extendPoint K e (x + y) = extendPoint K e x + extendPoint K e y := by
  classical
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · simp [extendPoint_off K e _ hj]

/-- Restricting a linear form retains just its selected coefficients. -/
theorem restrict_linearPolynomial [Fintype α] [Fintype β] (a : β → K) :
    restrictPolynomial K e (linearPolynomial a) = linearPolynomial (a ∘ e) := by
  simp only [linearPolynomial, map_sum, map_mul, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq]
  rw [sum_over_embedding e (fun j => C (a j) * restrictPolynomial K e (X j))]
  · simp
  · intro j hj
    simp [restrict_X_off K e hj]

/-- Restriction as a linear map on a homogeneous piece. -/
def restrictForm (d : ℕ) : homogeneousSubmodule β K d →ₗ[K] homogeneousSubmodule α K d where
  toFun f := ⟨restrictPolynomial K e f.val, restrict_homogeneous K e f.property⟩
  map_add' f g := Subtype.ext ((restrictPolynomial K e).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((restrictPolynomial K e).toLinearMap.map_smul a f.val)

@[simp] theorem restrictForm_val (d : ℕ) (f : homogeneousSubmodule β K d) :
    (restrictForm K e d f).val = restrictPolynomial K e f.val := rfl

/-- Restrict both components of a quadratic pair. -/
def restrictPair : (Quadrics K β × Quadrics K β) →ₗ[K] (Quadrics K α × Quadrics K α) :=
  (restrictForm K e 2).prodMap (restrictForm K e 2)

@[simp] theorem restrictPair_fst (f : Quadrics K β × Quadrics K β) :
    (restrictPair K e f).1.val = restrictPolynomial K e f.1.val := rfl

@[simp] theorem restrictPair_snd (f : Quadrics K β × Quadrics K β) :
    (restrictPair K e f).2.val = restrictPolynomial K e f.2.val := rfl

end IdealGeneration.QuadraticTraceRestriction
