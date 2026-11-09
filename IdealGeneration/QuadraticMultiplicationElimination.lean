module

public import IdealGeneration.QuadraticElimination
public import IdealGeneration.QuadraticNormalCoefficients

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Polynomial elimination for trace and normal multiples of residual quadrics. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial

variable {K H R S J : Type*} [Field K] [AddCommGroup H] [Module K H]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [Fintype J]

/-- The chosen three normal lifts, as actual elements of the full algebra. -/
def normalLift (ψ : R →ₐ[K] S) (s t : S) (U V : Fin 3 → R) : Fin 3 → S :=
  ![s ^ 2 + s * ψ (U 0) + t * ψ (V 0),
    s * t + s * ψ (U 1) + t * ψ (V 1),
    t ^ 2 + s * ψ (U 2) + t * ψ (V 2)]

/-- The lift coordinates separate the pure-normal basis and mixed kernel part. -/
theorem liftedQuadratic_eq_normalLifts (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (x : LiftSpace (K := K) (H := H)) :
    liftedQuadratic ψ s t U V g₁ g₂ x =
      algebraMap K S (x.1 0) * normalLift ψ s t U V 0 +
      algebraMap K S (x.1 1) * normalLift ψ s t U V 1 +
      algebraMap K S (x.1 2) * normalLift ψ s t U V 2 +
      ψ (g₁ x.2) * s + ψ (g₂ x.2) * t := by
  simp [liftedQuadratic, quadraticExpression, lowerPart, normalLift,
    Fin.sum_univ_three, Algebra.smul_def]
  ring

/-- A finite family of trace multiples of residual quadrics. -/
def traceProduct (ψ : R →ₐ[K] S) (s t : S) (U V : Fin 3 → R)
    (g₁ g₂ : H →ₗ[K] R) (ell : J → R) (z : J → LiftSpace (K := K) (H := H)) : S :=
  ∑ j, ψ (ell j) * liftedQuadratic ψ s t U V g₁ g₂ (z j)

/-- Its coefficients on the three selected lifts. -/
def traceNormalCoefficient (ell : J → R) (z : J → LiftSpace (K := K) (H := H))
    (i : Fin 3) : R :=
  ∑ j, ell j * algebraMap K R ((z j).1 i)

/-- Its mixed kernel contribution. -/
def traceKernelPair (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H)) : R × R :=
  (∑ j, ell j * g₁ (z j).2, ∑ j, ell j * g₂ (z j).2)

/-- Separating the three lifts commutes with summing trace multiples. -/
theorem traceProduct_eq_normalLifts (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H)) :
    traceProduct ψ s t U V g₁ g₂ ell z =
      ψ (traceNormalCoefficient ell z 0) * normalLift ψ s t U V 0 +
      ψ (traceNormalCoefficient ell z 1) * normalLift ψ s t U V 1 +
      ψ (traceNormalCoefficient ell z 2) * normalLift ψ s t U V 2 +
      ψ (traceKernelPair g₁ g₂ ell z).1 * s +
      ψ (traceKernelPair g₁ g₂ ell z).2 * t := by
  simp only [traceProduct, liftedQuadratic_eq_normalLifts, mul_add,
    Finset.sum_add_distrib, traceNormalCoefficient, traceKernelPair, map_sum, map_mul,
    AlgHom.commutes, Finset.sum_mul, mul_assoc]

/-- When the normal quadratic coefficients cancel, all remaining products are
mixed trace products together with the explicit image of `φ`. -/
theorem traceProduct_elimination (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H))
    (x : Omega (LinearMap.fst K (Fin 3 → K) H))
    (h0 : traceNormalCoefficient ell z 0 + lowerPart U g₁ x.val.1 = 0)
    (h1 : traceNormalCoefficient ell z 1 +
      (lowerPart V g₂ x.val.1 + lowerPart U g₁ x.val.2) = 0)
    (h2 : traceNormalCoefficient ell z 2 + lowerPart V g₂ x.val.2 = 0) :
    traceProduct ψ s t U V g₁ g₂ ell z +
      s * liftedQuadratic ψ s t U V g₁ g₂ x.val.1 +
      t * liftedQuadratic ψ s t U V g₁ g₂ x.val.2 =
      s * ψ ((traceKernelPair g₁ g₂ ell z).1 + (phi U V g₁ g₂ x).1) +
      t * ψ ((traceKernelPair g₁ g₂ ell z).2 + (phi U V g₁ g₂ x).2) := by
  rw [traceProduct_eq_normalLifts]
  have he := phi_elimination_identity ψ s t U V g₁ g₂ x
  have h0' := congrArg ψ h0
  have h1' := congrArg ψ h1
  have h2' := congrArg ψ h2
  simp only [map_add, map_zero] at h0' h1' h2' he ⊢
  simp only [normalLift, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ⊢
  linear_combination he + (s ^ 2 + s * ψ (U 0) + t * ψ (V 0)) * h0' +
    (s * t + s * ψ (U 1) + t * ψ (V 1)) * h1' +
    (t ^ 2 + s * ψ (U 2) + t * ψ (V 2)) * h2'

/-- The trace-linear coefficient obtained after separating the normal degrees. -/
def traceLinearCoefficient (U : Fin 3 → R) (g : H →ₗ[K] R)
    (ell : J → R) (z : J → LiftSpace (K := K) (H := H)) : R :=
  traceNormalCoefficient ell z 0 * U 0 + traceNormalCoefficient ell z 1 * U 1 +
    traceNormalCoefficient ell z 2 * U 2 + ∑ j, ell j * g (z j).2

/-- Every product has an explicit expansion by normal degree. -/
theorem product_normal_expansion (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H))
    (x y : LiftSpace (K := K) (H := H)) :
    traceProduct ψ s t U V g₁ g₂ ell z +
      s * liftedQuadratic ψ s t U V g₁ g₂ x +
      t * liftedQuadratic ψ s t U V g₁ g₂ y =
    algebraMap K S (x.1 0) * s ^ 3 +
      algebraMap K S (x.1 1 + y.1 0) * s ^ 2 * t +
      algebraMap K S (x.1 2 + y.1 1) * s * t ^ 2 +
      algebraMap K S (y.1 2) * t ^ 3 +
      ψ (traceNormalCoefficient ell z 0 + lowerPart U g₁ x) * s ^ 2 +
      ψ (traceNormalCoefficient ell z 1 + lowerPart V g₂ x + lowerPart U g₁ y) * s * t +
      ψ (traceNormalCoefficient ell z 2 + lowerPart V g₂ y) * t ^ 2 +
      ψ (traceLinearCoefficient U g₁ ell z) * s +
      ψ (traceLinearCoefficient V g₂ ell z) * t := by
  rw [traceProduct_eq_normalLifts]
  simp only [liftedQuadratic, quadraticExpression, normalLift, traceLinearCoefficient,
    traceKernelPair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_mul, map_sum]
  ring

/-- A coordinate vector in the chosen pure-normal lift section. -/
def unitLift (i : Fin 3) : LiftSpace (K := K) (H := H) := (Pi.single i 1, 0)

theorem liftedQuadratic_unitLift (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (i : Fin 3) :
    liftedQuadratic ψ s t U V g₁ g₂ (unitLift i) = normalLift ψ s t U V i := by
  fin_cases i <;>
    simp [liftedQuadratic_eq_normalLifts, unitLift, normalLift]

/-- The three trace-linear coefficients subtracted in (A.3). -/
def eliminationCoefficients (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) : Fin 3 → R :=
  ![-lowerPart U g₁ x.val.1,
    -(lowerPart V g₂ x.val.1 + lowerPart U g₁ x.val.2),
    -lowerPart V g₂ x.val.2]

/-- Every `φ` value is represented by products of the chosen residual quadrics. -/
theorem phi_product_representation (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    traceProduct ψ s t U V g₁ g₂ (eliminationCoefficients U V g₁ g₂ x)
      (unitLift (K := K) (H := H)) +
      s * liftedQuadratic ψ s t U V g₁ g₂ x.val.1 +
      t * liftedQuadratic ψ s t U V g₁ g₂ x.val.2 =
      s * ψ (phi U V g₁ g₂ x).1 + t * ψ (phi U V g₁ g₂ x).2 := by
  have he := phi_elimination_identity ψ s t U V g₁ g₂ x
  simp only [map_add] at he
  simp [traceProduct, Fin.sum_univ_three, eliminationCoefficients,
    liftedQuadratic_unitLift, normalLift, map_add] at ⊢
  linear_combination he

/-- Pure mixed trace products also belong to the same multiplication image. -/
theorem mixedTraceProduct_representation (ψ : R →ₐ[K] S) (s t : S)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R) (h : J → H) :
    traceProduct ψ s t U V g₁ g₂ ell (fun j => (0, h j)) =
      s * ψ (∑ j, ell j * g₁ (h j)) + t * ψ (∑ j, ell j * g₂ (h j)) := by
  simp [traceProduct, liftedQuadratic, quadraticExpression, lowerPart,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum, map_sum, map_mul,
    mul_left_comm, mul_comm]

/-- The trace ring embeds as coefficients of the two-normal polynomial ring. -/
def normalEmbedding : R →ₐ[K] MvPolynomial Bool R :=
  IsScalarTower.toAlgHom K R (MvPolynomial Bool R)

@[simp] theorem normalEmbedding_apply (r : R) :
    normalEmbedding (K := K) r = (C r : MvPolynomial Bool R) := rfl

/-- Normal-linear coefficient pairs have unique polynomial representatives. -/
theorem normalLinearPair_injective :
    Function.Injective (fun p : R × R =>
      (C p.1 * X false + C p.2 * X true : MvPolynomial Bool R)) := by
  intro p q h
  apply Prod.ext
  · have he := congrArg (eval (fun b : Bool => if b = false then (1 : R) else 0)) h
    simpa using he
  · have he := congrArg (eval (fun b : Bool => if b = true then (1 : R) else 0)) h
    simpa using he

/-- An actual normal-linear product forces the cubic and quadratic normal
coefficients to vanish. -/
theorem normalLinear_product_constraints
    (hinj : Function.Injective (algebraMap K R))
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H))
    (x y : LiftSpace (K := K) (H := H)) (A B : R)
    (h : traceProduct (normalEmbedding (K := K)) (X false) (X true) U V g₁ g₂ ell z +
      X false * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ x +
      X true * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ y =
      C A * X false + C B * X true) :
    normalCubicMap (x.1, y.1) = 0 ∧
      traceNormalCoefficient ell z 0 + lowerPart U g₁ x = 0 ∧
      traceNormalCoefficient ell z 1 + (lowerPart V g₂ x + lowerPart U g₁ y) = 0 ∧
      traceNormalCoefficient ell z 2 + lowerPart V g₂ y = 0 := by
  have he := product_normal_expansion (normalEmbedding (K := K)) (X false) (X true)
    U V g₁ g₂ ell z x y
  have hv := he.symm.trans h
  simp only [normalEmbedding_apply, MvPolynomial.algebraMap_apply] at hv
  obtain ⟨ha, hb, hc, hd, hu, hv, hw, _, _⟩ :=
    IdealGeneration.QuadraticNormalCoefficients.normalDegree_separation
      _ _ _ _ _ _ _ _ _ _ _ hv
  refine ⟨(normalCubicMap_eq_zero_iff _).mpr ⟨?_, ?_, ?_, ?_⟩, hu, ?_, hw⟩
  · exact hinj (by simpa only [map_zero] using ha)
  · exact hinj (by simpa only [map_zero] using hb)
  · exact hinj (by simpa only [map_zero] using hc)
  · exact hinj (by simpa only [map_zero] using hd)
  · simpa only [add_assoc] using hv

/-- Every actual normal-linear product splits into its mixed trace products
and the explicitly eliminated `φ` contribution. -/
theorem normalLinear_product_decomposition
    (hinj : Function.Injective (algebraMap K R))
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (ell : J → R)
    (z : J → LiftSpace (K := K) (H := H))
    (x y : LiftSpace (K := K) (H := H)) (A B : R)
    (h : traceProduct (normalEmbedding (K := K)) (X false) (X true) U V g₁ g₂ ell z +
      X false * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ x +
      X true * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ y =
      C A * X false + C B * X true) :
    ∃ w : Omega (LinearMap.fst K (Fin 3 → K) H),
      w.val = (x, y) ∧ (A, B) = traceKernelPair g₁ g₂ ell z + phi U V g₁ g₂ w := by
  obtain ⟨hΩ, h0, h1, h2⟩ := normalLinear_product_constraints hinj U V g₁ g₂ ell z x y A B h
  let w : Omega (LinearMap.fst K (Fin 3 → K) H) := ⟨(x, y), hΩ⟩
  refine ⟨w, rfl, ?_⟩
  have he := traceProduct_elimination (normalEmbedding (K := K)) (X false) (X true)
    U V g₁ g₂ ell z w h0 h1 h2
  apply normalLinearPair_injective
  have hh := h.symm.trans he
  simpa only [normalEmbedding_apply, Prod.fst_add, Prod.snd_add, mul_comm] using hh

end IdealGeneration.QuadraticElimination
