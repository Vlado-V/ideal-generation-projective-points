module

public import IdealGeneration.QuadraticMultiplicationElimination
public import IdealGeneration.QuadraticLinearForms

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The normal-linear part of the actual residual multiplication image. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial QuadraticFlag

variable {K H T : Type*} [Field K] [AddCommGroup H] [Module K H] [Fintype T]

/-- The represented residual quadric in the polynomial ring with two normal variables. -/
def normalPolynomialMap
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    LiftSpace (K := K) (H := H) →ₗ[K] MvPolynomial Bool (MvPolynomial T K) where
  toFun x := liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ x
  map_add' x y := by
    simp [liftedQuadratic, quadraticExpression, map_add, mul_add, add_mul]
    ring
  map_smul' r x := by
    simp [liftedQuadratic, quadraticExpression, map_smul, Algebra.smul_def]
    ring

omit [Fintype T] in
@[simp] theorem normalPolynomialMap_apply
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)
    (x : LiftSpace (K := K) (H := H)) :
    normalPolynomialMap U V g₁ g₂ x =
      liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ x := rfl

/-- Embed a pair as a polynomial of normal degree one. -/
def normalPairMap : (MvPolynomial T K × MvPolynomial T K) →ₗ[K]
    MvPolynomial Bool (MvPolynomial T K) where
  toFun f := C f.1 * X false + C f.2 * X true
  map_add' f g := by simp [map_add, add_mul]; ring
  map_smul' r f := by simp [Algebra.smul_def]; ring

omit [Fintype T] in
@[simp] theorem normalPairMap_apply (f : MvPolynomial T K × MvPolynomial T K) :
    normalPairMap (K := K) f = C f.1 * X false + C f.2 * X true := rfl

/-- Coordinate multiplication by every trace and normal variable. -/
def middleMultiplication
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    ((LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) ×
      (T → LiftSpace (K := K) (H := H))) →ₗ[K] MvPolynomial Bool (MvPolynomial T K) where
  toFun d := (∑ j, C (X j) * normalPolynomialMap U V g₁ g₂ (d.2 j)) +
    X false * normalPolynomialMap U V g₁ g₂ d.1.1 +
    X true * normalPolynomialMap U V g₁ g₂ d.1.2
  map_add' x y := by
    simp [map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r x := by
    simp [map_smul, Finset.smul_sum, smul_add]

@[simp] theorem middleMultiplication_apply
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)
    (d : (LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) ×
      (T → LiftSpace (K := K) (H := H))) :
    middleMultiplication U V g₁ g₂ d =
      traceProduct normalEmbedding (X false) (X true) U V g₁ g₂ (fun j => X j) d.2 +
      X false * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.1 +
      X true * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.2 := rfl

/-- The space denoted by `W`, defined by the actual multiplication image. -/
def middleSpace
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    Submodule K (MvPolynomial T K × MvPolynomial T K) :=
  (middleMultiplication U V g₁ g₂).range.comap normalPairMap

/-- Products of mixed kernel generators with trace variables. -/
def mixedTraceMap (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    (T → H) →ₗ[K] (MvPolynomial T K × MvPolynomial T K) where
  toFun h := (∑ j, X j * g₁ (h j), ∑ j, X j * g₂ (h j))
  map_add' h k := by
    apply Prod.ext <;> simp [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' r h := by
    apply Prod.ext <;> simp [map_smul, Finset.smul_sum]

@[simp] theorem mixedTraceMap_apply (g₁ g₂ : H →ₗ[K] MvPolynomial T K) (h : T → H) :
    mixedTraceMap g₁ g₂ h = (∑ j, X j * g₁ (h j), ∑ j, X j * g₂ (h j)) := rfl

/-- Actual polynomial elimination puts every normal-linear product in `U+φ(Ω)`. -/
theorem middleSpace_le
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    middleSpace U V g₁ g₂ ≤ (mixedTraceMap g₁ g₂).range ⊔ (phi U V g₁ g₂).range := by
  classical
  rintro ⟨A, B⟩ ⟨d, hd⟩
  change traceProduct normalEmbedding (X false) (X true) U V g₁ g₂ (fun j => X j) d.2 +
      X false * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.1 +
      X true * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.2 =
      C A * X false + C B * X true at hd
  have hinj : Function.Injective (algebraMap K (MvPolynomial T K)) := by
    simpa only [MvPolynomial.algebraMap_eq] using MvPolynomial.C_injective (σ := T) (R := K)
  obtain ⟨w, _, hw⟩ := normalLinear_product_decomposition hinj U V g₁ g₂
    (fun j => X j) d.2 d.1.1 d.1.2 A B hd
  apply Submodule.mem_sup.mpr
  refine ⟨mixedTraceMap g₁ g₂ (fun j => (d.2 j).2), ⟨_, rfl⟩,
    phi U V g₁ g₂ w, ⟨w, rfl⟩, ?_⟩
  simpa only [mixedTraceMap, LinearMap.coe_mk, AddHom.coe_mk, traceKernelPair] using hw.symm

/-- Mixed trace products are themselves in the actual multiplication image. -/
theorem mixedTraceMap_range_le_middleSpace
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K) :
    (mixedTraceMap g₁ g₂).range ≤ middleSpace U V g₁ g₂ := by
  intro f hf
  obtain ⟨h, rfl⟩ := hf
  change normalPairMap (mixedTraceMap g₁ g₂ h) ∈ (middleMultiplication U V g₁ g₂).range
  let d : ((LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) ×
      (T → LiftSpace (K := K) (H := H))) := ((0, 0), fun j => (0, h j))
  apply LinearMap.mem_range.mpr
  refine ⟨d, ?_⟩
  rw [middleMultiplication_apply, normalPairMap_apply, mixedTraceMap_apply]
  dsimp only [d]
  have hz : liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂
      (0 : LiftSpace (K := K) (H := H)) = 0 :=
    (normalPolynomialMap U V g₁ g₂).map_zero
  have he := mixedTraceProduct_representation normalEmbedding (X false) (X true)
    U V g₁ g₂ (fun j => X j) h
  simpa only [hz, mul_zero, add_zero, traceProduct, normalEmbedding_apply, mul_comm] using he

/-- The eliminated pair has an actual coordinate-multiplication preimage. -/
theorem phi_range_le_middleSpace
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1) :
    (phi U V g₁ g₂).range ≤ middleSpace U V g₁ g₂ := by
  classical
  rintro f ⟨x, rfl⟩
  change normalPairMap (phi U V g₁ g₂ x) ∈ (middleMultiplication U V g₁ g₂).range
  let ell := eliminationCoefficients U V g₁ g₂ x
  have hell (i : Fin 3) : (ell i).IsHomogeneous 1 := by
    fin_cases i
    · exact (lowerPart_homogeneous U g₁ hU hg₁ x.val.1).neg
    · exact ((lowerPart_homogeneous V g₂ hV hg₂ x.val.1).add
        (lowerPart_homogeneous U g₁ hU hg₁ x.val.2)).neg
    · exact (lowerPart_homogeneous V g₂ hV hg₂ x.val.2).neg
  let z : T → LiftSpace (K := K) (H := H) := fun j =>
    (fun i => eval (coordinatePoint j) (ell i), 0)
  have hz (i : Fin 3) : traceNormalCoefficient (fun j : T => X j) z i = ell i := by
    have he := linearPolynomial_eval_coordinate_of_homogeneous (ell i) (hell i)
    simpa [traceNormalCoefficient, z, linearPolynomial, mul_comm] using he
  have hprod : traceProduct normalEmbedding (X false) (X true) U V g₁ g₂
      (fun j : T => X j) z =
      traceProduct normalEmbedding (X false) (X true) U V g₁ g₂ ell
        (unitLift (K := K) (H := H)) := by
    rw [traceProduct_eq_normalLifts, traceProduct_eq_normalLifts, hz 0, hz 1, hz 2]
    have hu (i : Fin 3) : traceNormalCoefficient ell (unitLift (K := K) (H := H)) i = ell i := by
      simp [traceNormalCoefficient, unitLift, Pi.single_apply]
    rw [hu 0, hu 1, hu 2]
    have hkz : traceKernelPair g₁ g₂ (fun j : T => X j) z = 0 := by
      simp [traceKernelPair, z]
    have hku : traceKernelPair g₁ g₂ ell (unitLift (K := K) (H := H)) = 0 := by
      simp [traceKernelPair, unitLift]
    rw [hkz, hku]
  apply LinearMap.mem_range.mpr
  refine ⟨(x.val, z), ?_⟩
  rw [middleMultiplication_apply, normalPairMap_apply]
  rw [hprod]
  have he := phi_product_representation normalEmbedding (X false) (X true) U V g₁ g₂ x
  simpa only [normalEmbedding_apply, mul_comm] using he

/-- The identity `W=U+φ(Ω)` follows from actual polynomial multiplication. -/
theorem middleSpace_eq
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1) :
    middleSpace U V g₁ g₂ = (mixedTraceMap g₁ g₂).range ⊔ (phi U V g₁ g₂).range := by
  exact le_antisymm (middleSpace_le U V g₁ g₂)
    (sup_le (mixedTraceMap_range_le_middleSpace U V g₁ g₂)
      (phi_range_le_middleSpace U V g₁ g₂ hU hV hg₁ hg₂))

end IdealGeneration.QuadraticElimination
