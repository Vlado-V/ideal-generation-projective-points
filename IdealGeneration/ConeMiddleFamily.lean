module

public import IdealGeneration.ConeParameterSpace
public import IdealGeneration.ConstrainedRankOpen

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# A fixed ambient presentation of the cone middle map

The normal-ideal form spaces and their multiplication map are fixed. Only
the evaluation constraints vary with the marked cone parameters. This gives
the actual middle map a polynomial constrained-map presentation.
-/

noncomputable section
namespace IdealGeneration.ConeMiddleFamily
open MvPolynomial Module ConeParameterSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {c m p q d : ℕ}

local instance (priority := 2000) submoduleCanonicalGroup
    {A : Type*} [AddCommMonoid A] [Module K A] (S : Submodule K A) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup K

def normalForms (K : Type*) [Field K] (c m d : ℕ) :
    Submodule K (Forms K (c + m) d) :=
  (coneRestrictForm K c m d).ker

abbrev Source (K : Type*) [Field K] (c m d : ℕ) :=
  (Fin (c + m) → normalForms K c m d) × (Fin c → Forms K m d)

abbrev NativeSource (C : ConeConfiguration K c m p q) (d : ℕ) :=
  (Fin (c + m) → C.residualPiece d) × (Fin c → C.tracePiece d)

/-- Evaluation on the fixed normal-ideal homogeneous subspace. -/
def normalEvaluation (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    normalForms K c m d →ₗ[K] (Fin p → K) :=
  (coneEvaluation support a d).comp (normalForms K c m d).subtype

/-- The source equations of the actual middle map on a fixed ambient source. -/
def sourceEvaluation (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    Source K c m d →ₗ[K] ((Fin (c + m) → Fin p → K) × (Fin c → Fin q → K)) :=
  ((LinearMap.pi (fun i => (normalEvaluation support a d).comp (LinearMap.proj i))).comp
    (LinearMap.fst K _ _)).prod
  ((LinearMap.pi (fun i => (traceEvaluation a d).comp (LinearMap.proj i))).comp
    (LinearMap.snd K _ _))

abbrev targetEvaluation (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :=
  normalEvaluation support a (d + 1)

def normalMultiplication (d : ℕ) :
    (Fin (c + m) → normalForms K c m d) →ₗ[K] normalForms K c m (d + 1) where
  toFun f := ⟨formMultiplication K (c + m) d (fun i => (f i).val), by
    change coneRestrictForm K c m (d + 1) _ = 0
    rw [coneRestrictForm_multiplication]
    have hz : (fun j : Fin m => coneRestrictForm K c m d (f (j.natAdd c)).val) = 0 := by
      funext j
      exact (f (j.natAdd c)).property
    rw [hz, map_zero]⟩
  map_add' f g := Subtype.ext ((formMultiplication K (c + m) d).map_add _ _)
  map_smul' a f := Subtype.ext ((formMultiplication K (c + m) d).map_smul a _)

def liftedTraceCoefficients (f : Fin c → Forms K m d) :
    Fin (c + m) → Forms K (c + m) d :=
  Fin.addCases (fun i => coneExtendForm K c m d (f i)) (fun _ => 0)

def normalTraceMultiplication (d : ℕ) :
    (Fin c → Forms K m d) →ₗ[K] normalForms K c m (d + 1) where
  toFun f := ⟨formMultiplication K (c + m) d (liftedTraceCoefficients f), by
    change coneRestrictForm K c m (d + 1) _ = 0
    rw [coneRestrictForm_multiplication]
    have hz : (fun j : Fin m => coneRestrictForm K c m d
        (liftedTraceCoefficients f (j.natAdd c))) = 0 := by
      funext j
      simp [liftedTraceCoefficients]
    rw [hz, map_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    change formMultiplication K (c + m) d _ =
      formMultiplication K (c + m) d _ + formMultiplication K (c + m) d _
    rw [← map_add]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [liftedTraceCoefficients]
  map_smul' a f := by
    apply Subtype.ext
    change formMultiplication K (c + m) d _ = a • formMultiplication K (c + m) d _
    rw [← map_smul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [liftedTraceCoefficients]

/-- The ambient multiplication map is independent of all cone parameters. -/
def ambientMiddle (d : ℕ) : Source K c m d →ₗ[K] normalForms K c m (d + 1) :=
  (normalMultiplication (K := K) (c := c) (m := m) d).coprod
    (normalTraceMultiplication (K := K) (c := c) (m := m) d)

/-- The source kernel is exactly the two summands in the actual middle-map domain. -/
def sourceKernelEquiv (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    NativeSource (configuration support a) d ≃ₗ[K] (sourceEvaluation support a d).ker where
  toFun f := ⟨((fun i => ⟨(f.1 i).val, (f.1 i).property.2⟩), fun i => (f.2 i).val), by
    apply Prod.ext
    · funext i j
      exact ((configuration support a).mem_conePiece _).mp (f.1 i).property.1 j
    · funext i j
      exact ((configuration support a).mem_tracePiece _).mp (f.2 i).property j⟩
  invFun f := ((fun i => ⟨(f.val.1 i).val, ⟨by
    apply ((configuration support a).mem_conePiece _).mpr
    intro j
    exact congrFun (congrFun (congrArg Prod.fst f.property) i) j,
      (f.val.1 i).property⟩⟩), fun i => ⟨f.val.2 i, by
    apply ((configuration support a).mem_tracePiece _).mpr
    intro j
    exact congrFun (congrFun (congrArg Prod.snd f.property) i) j⟩)
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' k f := rfl

/-- The normal-ideal cone equations are the kernel of normal evaluation. -/
def normalKernelEquiv (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    (configuration support a).residualPiece d ≃ₗ[K] (normalEvaluation support a d).ker where
  toFun f := ⟨⟨f.val, f.property.2⟩, by
    funext i
    exact ((configuration support a).mem_conePiece _).mp f.property.1 i⟩
  invFun f := ⟨f.val.val, ⟨by
    apply ((configuration support a).mem_conePiece _).mpr
    intro i
    exact congrFun f.property i, f.val.property⟩⟩
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' k f := rfl

abbrev targetKernelEquiv (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :=
  normalKernelEquiv support a (d + 1)

theorem traceEvaluation_ker (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :
    (traceEvaluation a d).ker = (configuration support a).tracePiece d := by
  ext f
  rw [LinearMap.mem_ker, (configuration support a).mem_tracePiece]
  constructor
  · intro hf i
    exact congrFun hf i
  · intro hf
    funext i
    exact hf i

/-- The fixed ambient multiplication gives exactly the native middle map. -/
theorem ambientMiddle_sourceKernelEquiv (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) (f : NativeSource (configuration support a) d) :
    ambientMiddle d (sourceKernelEquiv support a d f).val =
      (targetKernelEquiv support a d ((configuration support a).middleMultiplication d f)).val := by
  apply Subtype.ext
  rfl

theorem ambientMiddle_preserves (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) (v : Source K c m d)
    (hv : sourceEvaluation support a d v = 0) :
    targetEvaluation support a d (ambientMiddle d v) = 0 := by
  let x : (sourceEvaluation support a d).ker := ⟨v, hv⟩
  have h := ambientMiddle_sourceKernelEquiv support a d ((sourceKernelEquiv support a d).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [show v = x.val from rfl, h]
  exact (targetKernelEquiv support a d
    ((configuration support a).middleMultiplication d ((sourceKernelEquiv support a d).symm x))).property

def constrainedMiddle (support : Fin p → Fin q) (a : Parameters K c m p q) (d : ℕ) :=
  ConstrainedRankOpen.constrainedMap (sourceEvaluation support a d)
    (targetEvaluation support a d) (ambientMiddle d) (ambientMiddle_preserves support a d)

theorem middle_constrained_commutes (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ) (f : NativeSource (configuration support a) d) :
    constrainedMiddle support a d (sourceKernelEquiv support a d f) =
      targetKernelEquiv support a d ((configuration support a).middleMultiplication d f) := by
  apply Subtype.ext
  exact ambientMiddle_sourceKernelEquiv support a d f

/-- Coordinatewise polynomial dependence for a vector-valued finite tuple. -/
theorem isPolynomialFamily_pi_module {ι I W : Type*} [Fintype I]
    [AddCommGroup W] [Module K W] (f : (ι → K) → I → W)
    (hf : ∀ i, IsPolynomialFamily (fun a => f a i)) : IsPolynomialFamily f := by
  classical
  have h := IsPolynomialFamily.sum (fun i =>
    (hf i).linear_comp (LinearMap.single K (fun _ : I => W) i))
  have heq : (fun a => ∑ i, (LinearMap.single K (fun _ : I => W) i) (f a i)) = f := by
    funext a i
    simp [LinearMap.single_apply, Pi.single_apply]
  exact heq ▸ h

theorem normalEvaluation_isPolynomialFamily (support : Fin p → Fin q) (d : ℕ) :
    IsPolynomialFamily (fun a : Parameters K c m p q => normalEvaluation support a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  exact (coneEvaluation_isPolynomialFamily support d).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Fin p → K) f.val)

theorem sourceEvaluation_isPolynomialFamily (support : Fin p → Fin q) (d : ℕ) :
    IsPolynomialFamily (fun a : Parameters K c m p q => sourceEvaluation support a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  apply IsPolynomialFamily.prod_mk
  · apply isPolynomialFamily_pi_module
    intro i
    exact (normalEvaluation_isPolynomialFamily support d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin p → K) (f.1 i))
  · apply isPolynomialFamily_pi_module
    intro i
    exact (traceEvaluation_isPolynomialFamily (c := c) (m := m) (p := p) (q := q) d).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin q → K) (f.2 i))

theorem targetEvaluation_isPolynomialFamily (support : Fin p → Fin q) (d : ℕ) :
    IsPolynomialFamily (fun a : Parameters K c m p q => targetEvaluation support a d) :=
  normalEvaluation_isPolynomialFamily support (d + 1)

theorem sourceEvaluation_surjective (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ)
    (hnormal : Function.Surjective (normalEvaluation support a d))
    (htrace : Function.Surjective (traceEvaluation a d)) :
    Function.Surjective (sourceEvaluation support a d) := by
  intro y
  choose f hf using fun i => hnormal (y.1 i)
  choose g hg using fun i => htrace (y.2 i)
  exact ⟨(f, g), Prod.ext (funext hf) (funext hg)⟩

theorem normalEvaluation_normalMultiplication (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ)
    (f : Fin (c + m) → normalForms K c m d) (i : Fin p) :
    normalEvaluation support a (d + 1) (normalMultiplication d f) i =
      ∑ j, (configuration support a).point i j * normalEvaluation support a d (f j) i := by
  change eval ((configuration support a).point i)
    ((formMultiplication K (c + m) d (fun j => (f j).val)).val) = _
  simp only [formMultiplication_val, map_sum, map_mul, eval_X]
  rfl

/-- Full scalar evaluation in degree `d` implies full scalar evaluation in
degree `d+1` on the normal ideal. For each row, use one coordinate nonzero at
that representative to multiply its scalar interpolant. -/
theorem targetEvaluation_surjective_of_normalEvaluation (support : Fin p → Fin q)
    (a : Parameters K c m p q) (d : ℕ)
    (hpoint : ∀ i, (configuration support a).point i ≠ 0)
    (hnormal : Function.Surjective (normalEvaluation support a d)) :
    Function.Surjective (targetEvaluation support a d) := by
  classical
  intro y
  have hsingle (i : Fin p) : ∃ g : normalForms K c m (d + 1),
      targetEvaluation support a d g = Pi.single i (y i) := by
    have hj : ∃ j, (configuration support a).point i j ≠ 0 := by
      by_contra! hz
      exact hpoint i (funext hz)
    obtain ⟨j, hj⟩ := hj
    let δ : Fin p → K := Pi.single i (y i / (configuration support a).point i j)
    obtain ⟨f, hf⟩ := hnormal δ
    refine ⟨normalMultiplication d (Pi.single j f), ?_⟩
    funext k
    change normalEvaluation support a (d + 1) (normalMultiplication d (Pi.single j f)) k = _
    rw [normalEvaluation_normalMultiplication]
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, hf]
      by_cases hk : k = i
      · subst k
        simp [δ, mul_div_cancel₀ _ hj]
      · simp [δ, hk]
    · intro l _ hl
      simp [hl]
    · simp
  choose g hg using hsingle
  refine ⟨∑ i, g i, ?_⟩
  rw [map_sum]
  funext i
  simp [hg, Pi.single_apply]

end IdealGeneration.ConeMiddleFamily
