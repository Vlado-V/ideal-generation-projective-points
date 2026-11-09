module

public import IdealGeneration.QuadraticFlag

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Explicit scalar interpolation on the paired quadratic flag. -/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial Module

variable {K P J V : Type*} [Field K]

/-- Quadratic forms with an arbitrary variable index type. -/
abbrev Quadrics (K V : Type*) [Field K] := homogeneousSubmodule V K 2

/-- Restrict to the base by setting every layer variable to zero. -/
def restrictBase : MvPolynomial ((P × Bool) ⊕ J) K →ₐ[K] MvPolynomial (P × Bool) K :=
  aeval (Sum.elim X (fun _ => 0))

@[simp] theorem restrictBase_rename (f : MvPolynomial (P × Bool) K) :
    restrictBase (J := J) (rename Sum.inl f) = f := by
  have h : (restrictBase (K := K) (P := P) (J := J)).comp (rename Sum.inl) =
      AlgHom.id K (MvPolynomial (P × Bool) K) := by
    ext i
    simp [restrictBase]
  exact congrArg (fun g => g f) h

@[simp] theorem restrictBase_X_base (i : P × Bool) :
    restrictBase (J := J) (X (Sum.inl i) : MvPolynomial ((P × Bool) ⊕ J) K) = X i := by
  simp [restrictBase]

@[simp] theorem restrictBase_X_layer (j : J) :
    restrictBase (P := P) (X (Sum.inr j) : MvPolynomial ((P × Bool) ⊕ J) K) = 0 := by
  simp [restrictBase]

theorem restrictBase_homogeneous (f : Quadrics K ((P × Bool) ⊕ J)) :
    (restrictBase f.val).IsHomogeneous 2 := by
  have h := f.property.aeval (Sum.elim X (fun _ : J => 0)) (n := 1) (by
    intro i
    cases i with
    | inl i => exact isHomogeneous_X K i
    | inr j => exact isHomogeneous_zero (P × Bool) K 1)
  simpa only [restrictBase, one_mul] using h

/-- Evaluation after restriction equals evaluation with all layer coordinates zero. -/
theorem eval_restrictBase (f : MvPolynomial ((P × Bool) ⊕ J) K)
    (x : P × Bool → K) :
    eval x (restrictBase f) = eval (Sum.elim x (fun _ : J => 0)) f := by
  have h : (eval x).comp (restrictBase (K := K) (P := P) (J := J)).toRingHom =
      eval (Sum.elim x (fun _ : J => 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [restrictBase]
    · intro i
      cases i <;> simp [restrictBase]
  exact congrArg (fun g => g f) h

/-- The paired base vector `π_p`. -/
def pairPoint (p : P) : P × Bool → K := by
  classical
  exact coordinatePoint (p, false) + coordinatePoint (p, true)

/-- A layer coordinate point. -/
def layerPoint (j : J) : (P × Bool) ⊕ J → K := by
  classical
  exact Sum.elim (fun _ => 0) (coordinatePoint j)

/-- The point `π_p+z_j`. -/
def pairedLayerPoint (p : P) (j : J) : (P × Bool) ⊕ J → K := by
  classical
  exact Sum.elim (pairPoint p) (coordinatePoint j)

/-- Scalar flag data, with the full base restriction recorded intrinsically. -/
abbrev ScalarFlagData := Quadrics K (P × Bool) × ((J → K) × (P × J → K))

/-- Restriction to the base and evaluations at all layer flag points. -/
def scalarFlagEvaluation : Quadrics K ((P × Bool) ⊕ J) →ₗ[K]
    ScalarFlagData (K := K) (P := P) (J := J) where
  toFun f := (⟨restrictBase f.val, restrictBase_homogeneous f⟩,
    (fun j => eval (layerPoint j) f.val, fun q => eval (pairedLayerPoint q.1 q.2) f.val))
  map_add' f g := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add _ _ _
    · apply Prod.ext <;> funext i <;> simp
  map_smul' r f := by
    apply Prod.ext
    · apply Subtype.ext
      exact (restrictBase (K := K) (P := P) (J := J)).toLinearMap.map_smul r f.val
    · apply Prod.ext <;> funext i <;> simp

variable [Fintype P] [Fintype J]

/-- Polynomial extension of arbitrary scalar flag data. -/
def scalarFlagExtensionPolynomial (d : ScalarFlagData (K := K) (P := P) (J := J)) :
    MvPolynomial ((P × Bool) ⊕ J) K :=
  rename Sum.inl d.1.val +
    (∑ j, C (d.2.1 j) * X (Sum.inr j) ^ 2) +
    ∑ p, ∑ j, C (d.2.2 (p, j) - d.2.1 j - eval (pairPoint p) d.1.val) *
      X (Sum.inl (p, false)) * X (Sum.inr j)

theorem scalarFlagExtensionPolynomial_homogeneous
    (d : ScalarFlagData (K := K) (P := P) (J := J)) :
    (scalarFlagExtensionPolynomial d).IsHomogeneous 2 := by
  apply IsHomogeneous.add
  · apply IsHomogeneous.add
    · simpa only [MvPolynomial.rename_eq_aeval, Function.comp_def, one_mul] using d.1.property.aeval
        (fun i => X (Sum.inl i)) (fun i => isHomogeneous_X K (Sum.inl i))
    · apply IsHomogeneous.sum
      intro j _
      exact isHomogeneous_C_mul_X_pow _ _ _
  · apply IsHomogeneous.sum
    intro p _
    apply IsHomogeneous.sum
    intro j _
    exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X K _)

/-- The explicit extension is again a homogeneous quadratic form. -/
def scalarFlagExtension (d : ScalarFlagData (K := K) (P := P) (J := J)) :
    Quadrics K ((P × Bool) ⊕ J) :=
  ⟨scalarFlagExtensionPolynomial d, scalarFlagExtensionPolynomial_homogeneous d⟩

theorem eval_zero_quadratic (f : Quadrics K V) : eval (0 : V → K) f.val = 0 := by
  simpa using IdealGeneration.homogeneous_eval_scale f.property (0 : V → K) (0 : K)

/-- The polynomial extension interpolates every prescribed scalar value. -/
theorem scalarFlagEvaluation_extension
    (d : ScalarFlagData (K := K) (P := P) (J := J)) :
    scalarFlagEvaluation (scalarFlagExtension d) = d := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    simp [scalarFlagEvaluation, scalarFlagExtension, scalarFlagExtensionPolynomial]
  · apply Prod.ext
    · funext j
      have hc : constantCoeff d.1.val = 0 := by
        simpa only [eval_zero] using eval_zero_quadratic d.1
      simp [scalarFlagEvaluation, scalarFlagExtension, scalarFlagExtensionPolynomial,
        layerPoint, coordinatePoint, eval_rename, Function.comp_def, hc]
    · funext q
      rcases q with ⟨p, j⟩
      simp [scalarFlagEvaluation, scalarFlagExtension, scalarFlagExtensionPolynomial,
        pairedLayerPoint, pairPoint, coordinatePoint, eval_rename, Function.comp_def]
      change eval (pairPoint p) d.1.val + d.2.1 j +
        (d.2.2 (p, j) - d.2.1 j - eval (pairPoint p) d.1.val) = d.2.2 (p, j)
      ring

/-- The scalar flag imposes independent conditions on homogeneous quadrics. -/
theorem scalarFlagEvaluation_surjective :
    Function.Surjective (scalarFlagEvaluation (K := K) (P := P) (J := J)) := by
  intro d
  exact ⟨scalarFlagExtension d, scalarFlagEvaluation_extension d⟩

end IdealGeneration.QuadraticFlag
