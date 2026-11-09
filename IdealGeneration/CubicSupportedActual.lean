module

public import IdealGeneration.CubicSupportedKernel
public import IdealGeneration.CubicSupportedConfiguration
public import IdealGeneration.CubicSupportedAmbientDimensions
public import IdealGeneration.CubicSupportedCoefficientUniqueness

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Identification of the supported coefficient kernel with actual cubic forms. -/

noncomputable section
namespace IdealGeneration.CubicSupported
open MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- Actual degree-three forms in the normal-coordinate ideal. -/
abbrev NormalForms (K : Type*) [Field K] (m : ℕ) := (coneRestrictForm K 2 m 3).ker

/-- The coefficient map lands in the genuine homogeneous normal ideal. -/
def coefficientNormalForm : Coefficients K m →ₗ[K] NormalForms K m where
  toFun u := ⟨⟨coefficientPolynomial u,
    polynomial_isHomogeneous u.1 u.2.1 u.2.2.1 u.2.2.2⟩, by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      exact polynomial_coneRestrict_zero u.1 u.2.1 u.2.2.1 u.2.2.2⟩
  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact coefficientPolynomial.map_add u v
  map_smul' r u := by
    apply Subtype.ext
    apply Subtype.ext
    exact coefficientPolynomial.map_smul r u

@[simp] theorem coefficientNormalForm_polynomial (u : Coefficients K m) :
    (coefficientNormalForm u).val.val = coefficientPolynomial u := rfl

/-- The actual polynomial map is injective in the characteristics used here. -/
theorem coefficientPolynomial_injective (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Function.Injective (coefficientPolynomial (K := K) (m := m)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  obtain ⟨hC, hB, hd, ho⟩ := polynomial_coefficients_eq_zero_of_ne h₂ h₆
    u.1 u.2.1 u.2.2.1 u.2.2.2 hu
  exact Prod.ext hC (Prod.ext hB (Prod.ext hd ho))

private theorem coefficientNormalForm_injective (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Function.Injective (coefficientNormalForm (K := K) (m := m)) := by
  intro u v h
  exact coefficientPolynomial_injective h₂ h₆
    (congrArg (fun f : NormalForms K m => f.val.val) h)

/-- The explicit coefficient model has exactly the dimension of the normal ideal. -/
theorem finrank_coefficients (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K (Coefficients K m) = (m + 2) ^ 2 := by
  have h := two_mul_card_edge_add m
  simp [Coefficients, Module.finrank_prod, Module.finrank_pi_fintype]
  nlinarith

private theorem coefficientNormalForm_surjective (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Function.Surjective (coefficientNormalForm (K := K) (m := m)) := by
  let _ : FiniteDimensional K (NormalForms K m) :=
    FiniteDimensional.finiteDimensional_submodule (NormalForms K m)
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq (K := K) (V := NormalForms K m)
  rw [LinearMap.finrank_range_of_inj (coefficientNormalForm_injective h₂ h₆),
    finrank_coefficients, finrank_cubic_restriction_ker]

/-- Every actual cubic of positive normal degree has unique coefficient coordinates. -/
def normalCoordinateEquiv (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Coefficients K m ≃ₗ[K] NormalForms K m :=
  LinearEquiv.ofBijective coefficientNormalForm
    ⟨coefficientNormalForm_injective h₂ h₆, coefficientNormalForm_surjective h₂ h₆⟩

@[simp] theorem normalCoordinateEquiv_polynomial (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)
    (u : Coefficients K m) :
    ((normalCoordinateEquiv h₂ h₆) u).val.val = coefficientPolynomial u := rfl

namespace Parameters

variable (P : Parameters K m)

/-- Evaluation of actual normal cubic forms at the supported cone points. -/
def actualConeEvaluation : NormalForms K m →ₗ[K] (P.ConeLabel → K) where
  toFun u a := eval (P.conePoint a) u.val.val
  map_add' u v := by
    funext a
    change eval (P.conePoint a) (u.val.val + v.val.val) = _
    simp only [map_add, Pi.add_apply]
  map_smul' r u := by
    funext a
    change eval (P.conePoint a) (r • u.val.val) = r * eval (P.conePoint a) u.val.val
    simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- The actual `K = P₃ ∩ I(Z₁)(3)` of the supported cone family. -/
def actualCubicKernel : Submodule K (NormalForms K m) := P.actualConeEvaluation.ker

@[simp] theorem mem_actualCubicKernel (u : NormalForms K m) :
    u ∈ P.actualCubicKernel ↔ ∀ a, eval (P.conePoint a) u.val.val = 0 := by
  rw [actualCubicKernel, LinearMap.mem_ker]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

private theorem mem_actual_normalCoordinateEquiv (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)
    (u : Coefficients K m) :
    normalCoordinateEquiv h₂ h₆ u ∈ P.actualCubicKernel ↔ u ∈ P.coefficientKernel := by
  rw [P.mem_actualCubicKernel, P.mem_coefficientKernel]
  rfl

/-- The coefficient equations identify with the kernel on actual normal cubic forms. -/
def coefficientActualEquiv (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    P.coefficientKernel ≃ₗ[K] P.actualCubicKernel where
  toFun u := ⟨normalCoordinateEquiv h₂ h₆ u.val,
    (P.mem_actual_normalCoordinateEquiv h₂ h₆ u.val).2 u.property⟩
  invFun u := ⟨(normalCoordinateEquiv h₂ h₆).symm u.val,
    (P.mem_actual_normalCoordinateEquiv h₂ h₆ ((normalCoordinateEquiv h₂ h₆).symm u.val)).1
      (by simpa only [LinearEquiv.apply_symm_apply] using u.property)⟩
  left_inv u := by
    apply Subtype.ext
    exact (normalCoordinateEquiv h₂ h₆).symm_apply_apply u.val
  right_inv u := by
    apply Subtype.ext
    exact (normalCoordinateEquiv h₂ h₆).apply_symm_apply u.val
  map_add' u v := by
    apply Subtype.ext
    exact (normalCoordinateEquiv h₂ h₆).map_add u.val v.val
  map_smul' r u := by
    apply Subtype.ext
    exact (normalCoordinateEquiv h₂ h₆).map_smul r u.val

/-- Lemma B.3's actual supported cubic chart. -/
def actualKernelCoordinates (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    P.actualCubicKernel ≃ₗ[K]
      ((Fin 4 → K) × (Fin m → Fin 3 → K) × (P.SingleEdge → K)) :=
  (P.coefficientActualEquiv h₂ h₆).symm.trans P.kernelCoordinatesEquiv

/-- The dimension of the genuine homogeneous supported cone kernel. -/
theorem finrank_actualCubicKernel (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Module.finrank K P.actualCubicKernel = 4 + 3 * m + Fintype.card P.SingleEdge := by
  rw [← (P.coefficientActualEquiv h₂ h₆).finrank_eq]
  exact P.finrank_coefficientKernel

/-- The projection onto `C,B` for actual supported cubic forms. -/
def actualTopProjection (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    P.actualCubicKernel →ₗ[K] ((Fin 4 → K) × (Fin m → Fin 3 → K)) :=
  P.topProjection.comp (P.coefficientActualEquiv h₂ h₆).symm.toLinearMap

theorem actualTopProjection_surjective (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Function.Surjective (P.actualTopProjection h₂ h₆) :=
  P.topProjection_surjective.comp (P.coefficientActualEquiv h₂ h₆).symm.surjective

/-- In the actual chart, the top projection forgets the single-edge coordinates. -/
theorem actualTopProjection_coordinates (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)
    (u : P.actualCubicKernel) :
    P.actualTopProjection h₂ h₆ u = ((P.actualKernelCoordinates h₂ h₆ u).1,
      (P.actualKernelCoordinates h₂ h₆ u).2.1) := rfl

/-- The lower normal-degree kernel has exactly the single-edge coordinates. -/
def actualK00Equiv (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    (P.actualTopProjection h₂ h₆).ker ≃ₗ[K] (P.SingleEdge → K) := by
  let e := P.actualKernelCoordinates h₂ h₆
  exact
    { toFun := fun u => (e u.val).2.2
      invFun := fun z => ⟨e.symm (0, 0, z), by
        apply LinearMap.mem_ker.mpr
        rw [P.actualTopProjection_coordinates]
        change ((e (e.symm (0, 0, z))).1, (e (e.symm (0, 0, z))).2.1) = 0
        simp⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply e.injective
        change e (e.symm (0, 0, (e u.val).2.2)) = e u.val
        rw [LinearEquiv.apply_symm_apply]
        have h := LinearMap.mem_ker.mp u.property
        rw [P.actualTopProjection_coordinates] at h
        change ((e u.val).1, (e u.val).2.1) = 0 at h
        have hC := congrArg Prod.fst h
        have hB := congrArg Prod.snd h
        exact Prod.ext hC.symm (Prod.ext hB.symm rfl)
      right_inv := fun z => by
        change (e (e.symm (0, 0, z))).2.2 = z
        simp
      map_add' := fun u v => congrArg (fun w => w.2.2) (e.map_add u.val v.val)
      map_smul' := fun r u => congrArg (fun w => w.2.2) (e.map_smul r u.val) }

/-- The actual lower normal-degree kernel `K00` has one dimension per single edge. -/
theorem finrank_actualK00 (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Module.finrank K (P.actualTopProjection h₂ h₆).ker = Fintype.card P.SingleEdge := by
  rw [(P.actualK00Equiv h₂ h₆).finrank_eq, Module.finrank_pi]


/-- The supported cubic kernel is the residual summand of the marked cone configuration. -/
def actualKernelResidualEquiv {f : ℕ} (free : Fin f → Fin m → K) :
    P.actualCubicKernel ≃ₗ[K] (P.toConeConfiguration free).residualPiece 3 where
  toFun u := ⟨u.val.val, ⟨by
    apply ((P.toConeConfiguration free).mem_conePiece _).mpr
    intro i
    let a := P.coneLabelEquiv.symm i
    have h := (P.mem_actualCubicKernel u.val).mp u.property a
    rw [← P.toConeConfiguration_point free a] at h
    simpa only [a, Equiv.apply_symm_apply] using h, u.val.property⟩⟩
  invFun u := ⟨⟨u.val, u.property.2⟩, (P.mem_actualCubicKernel _).mpr (fun a => by
    rw [← P.toConeConfiguration_point free a]
    exact ((P.toConeConfiguration free).mem_conePiece _).mp u.property.1 (P.coneLabelEquiv a))⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := Subtype.ext rfl
  map_add' u v := Subtype.ext rfl
  map_smul' r u := Subtype.ext rfl

/-- Coefficient coordinates for the actual middle-map residual source. -/
def residualKernelCoordinates {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    (P.toConeConfiguration free).residualPiece 3 ≃ₗ[K]
      ((Fin 4 → K) × (Fin m → Fin 3 → K) × (P.SingleEdge → K)) :=
  (P.actualKernelResidualEquiv free).symm.trans (P.actualKernelCoordinates h₂ h₆)

/-- The residual source of the actual marked cone has the supported kernel dimension. -/
theorem finrank_residualPiece_cubic {f : ℕ} (free : Fin f → Fin m → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) :
    Module.finrank K ((P.toConeConfiguration free).residualPiece 3) =
      4 + 3 * m + Fintype.card P.SingleEdge := by
  rw [← (P.actualKernelResidualEquiv free).finrank_eq]
  exact P.finrank_actualCubicKernel h₂ h₆

end Parameters
end IdealGeneration.CubicSupported
