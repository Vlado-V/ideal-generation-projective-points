module

public import IdealGeneration.QuadraticPairProjection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Injectivity of the actual residual multiplication from the projected elimination. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial QuadraticFlag

section Generic
variable {K T H : Type*} [Field K] [Fintype T] [AddCommGroup H] [Module K H]
variable (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)

/-- A relation first kills its normal coefficients through the projected
elimination, then its trace coefficients through the mixed products. -/
theorem middleMultiplication_injective
    (hMixed : Function.Injective (mixedTraceMap g₁ g₂))
    (hPhi : ∀ w, phi U V g₁ g₂ w ∈ (mixedTraceMap g₁ g₂).range → w = 0) :
    Function.Injective (middleMultiplication U V g₁ g₂) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro d hd
  have hzero : traceProduct normalEmbedding (X false) (X true) U V g₁ g₂
        (fun j => X j) d.2 +
      X false * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.1 +
      X true * liftedQuadratic normalEmbedding (X false) (X true) U V g₁ g₂ d.1.2 =
      C (0 : MvPolynomial T K) * X false + C (0 : MvPolynomial T K) * X true := by
    simpa only [middleMultiplication_apply, map_zero, zero_mul, add_zero] using hd
  have hinj : Function.Injective (algebraMap K (MvPolynomial T K)) := by
    simpa only [MvPolynomial.algebraMap_eq] using MvPolynomial.C_injective T K
  obtain ⟨w, hw, he⟩ := normalLinear_product_decomposition hinj U V g₁ g₂
    (fun j => X j) d.2 d.1.1 d.1.2 0 0 hzero
  let L : T → H := fun j => (d.2 j).2
  have he' : mixedTraceMap g₁ g₂ L + phi U V g₁ g₂ w = 0 := by
    change _ = (0, 0)
    simpa only [mixedTraceMap_apply, traceKernelPair, L] using he.symm
  have hp : phi U V g₁ g₂ w ∈ (mixedTraceMap g₁ g₂).range := by
    have hneg : phi U V g₁ g₂ w = -mixedTraceMap g₁ g₂ L :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he')
    rw [hneg]
    exact Submodule.neg_mem _ ⟨L, rfl⟩
  have hw₀ : w = 0 := hPhi w hp
  have hn : d.1 = 0 := by
    simpa only [hw₀, Submodule.coe_zero, Prod.eta] using hw.symm
  have hL : L = 0 := by
    apply hMixed
    simpa only [hw₀, map_zero, add_zero] using he'
  obtain ⟨_, h₀, h₁, h₂⟩ := normalLinear_product_constraints hinj U V g₁ g₂
    (fun j => X j) d.2 d.1.1 d.1.2 0 0 hzero
  have hq (k : Fin 3) :
      traceNormalCoefficient (fun j : T => (X j : MvPolynomial T K)) d.2 k = 0 := by
    fin_cases k
    · simpa [hn] using h₀
    · simpa [hn] using h₁
    · simpa [hn] using h₂
  have hcoeff (j : T) (k : Fin 3) : (d.2 j).1 k = 0 := by
    have hv := congrArg (eval (coordinatePoint j)) (hq k)
    simpa [traceNormalCoefficient, coordinatePoint, mul_comm] using hv
  apply Prod.ext
  · exact hn
  · funext j
    apply Prod.ext
    · exact funext (hcoeff j)
    · exact congrFun hL j

/-- An injective coordinate multiplication also makes the chosen residual
quadratic representation faithful. -/
theorem normalPolynomialMap_injective_of_middle
    (h : Function.Injective (middleMultiplication U V g₁ g₂)) :
    Function.Injective (normalPolynomialMap U V g₁ g₂) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  let d : (LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) ×
      (T → LiftSpace (K := K) (H := H)) := ((x, 0), 0)
  have hd : middleMultiplication U V g₁ g₂ d = 0 := by
    change (∑ j : T, C (X j) * normalPolynomialMap U V g₁ g₂ 0) +
      X false * normalPolynomialMap U V g₁ g₂ x +
      X true * normalPolynomialMap U V g₁ g₂ 0 = 0
    simp only [hx, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
  have he : d = 0 := h (by simpa only [map_zero] using hd)
  exact congrArg (fun d => d.1.1) he

end Generic

namespace QuadraticLiftParameters
variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable (D : QuadraticLiftParameters K P J)

/-- Transposition preserves injectivity of the actual mixed product map. -/
theorem actualMixedTraceMap_injective (hc : Function.Injective D.slope) :
    Function.Injective (mixedTraceMap (firstKernelMap D.firstCorrection)
      (secondKernelMap D.slope D.secondCorrection)) := by
  intro L M h
  have he := multiplication_injective D.slope D.firstCorrection D.secondCorrection hc
    (by simpa only [mixedTraceMap_eq_multiplication] using h)
  funext j i
  exact congrFun (congrFun he i) j

/-- A value already in the mixed image has zero projection along that image. -/
theorem actualProjectedPairMap_eq_zero_of_mixed (hc : Function.Injective D.slope)
    (x : Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K)))
    (hx : phi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
      (secondKernelMap D.slope D.secondCorrection) x ∈
        mixedImage D.slope D.firstCorrection D.secondCorrection) :
    D.actualProjectedPairMap hc x = 0 := by
  have hn₀ (j : J) : D.normal₀ j ≠ 0 := by
    intro h
    have hd := D.determinant_ne j
    simp [h] at hd
  have hn₁ (j : J) : D.normal₁ j ≠ 0 := by
    intro h
    have hd := D.determinant_ne j
    simp [h] at hd
  let e := quadraticFlagSplitting D.slope D.firstCorrection D.secondCorrection D.distinguishedPair
    D.normal₀ D.normal₁ hc hn₀ hn₁ D.first_normal_equation D.second_normal_equation
  let f := phiToAllowed D.slope D.distinguishedPair D.normal₀ D.normal₁ D.firstLift D.secondLift
    (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)
    D.firstLift_homogeneous D.secondLift_homogeneous
    (firstKernelMap_homogeneous _) (secondKernelMap_homogeneous _ _) D.actualNormalLiftVanishing
  rw [← map_quadraticMixedImage] at hx
  obtain ⟨m, hm, heq⟩ := hx
  let u : quadraticMixedImage D.slope D.firstCorrection D.secondCorrection := ⟨m, hm⟩
  have hu : e (u, 0) = f x := by
    apply Subtype.ext
    apply quadraticPairInclusion_injective
    have he : (e (u, 0)).val = u.val + (0 : (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
        (quadraticFlagVanishing (K := K) (P := P) (J := J))).val := by
      simp only [e, quadraticFlagSplitting, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
      exact disjointSumEquiv_val _ _ _ _
    rw [he, Submodule.coe_zero, add_zero]
    change quadraticPairInclusion m = phi D.firstLift D.secondLift
      (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection) x
    exact heq
  change ((e.symm (f x)).2).val = 0
  rw [← hu, LinearEquiv.symm_apply_apply]
  exact Submodule.coe_zero

/-- The actual represented `K⊗S₁` multiplication is injective when the
projected coefficient map is injective. -/
theorem actualMiddleMultiplication_injective (hc : Function.Injective D.slope)
    (h : Function.Injective (D.actualProjectedPairMap hc)) :
    Function.Injective (middleMultiplication D.firstLift D.secondLift
      (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)) := by
  apply middleMultiplication_injective
  · exact D.actualMixedTraceMap_injective hc
  · intro w hw
    rw [mixedTraceMap_range_eq_mixedImage] at hw
    apply h
    rw [map_zero]
    exact D.actualProjectedPairMap_eq_zero_of_mixed hc w hw

/-- The explicit residual quadrics are faithfully parameterized by `h+3` coefficients. -/
theorem actualNormalPolynomialMap_injective (hc : Function.Injective D.slope)
    (h : Function.Injective (D.actualProjectedPairMap hc)) :
    Function.Injective (normalPolynomialMap D.firstLift D.secondLift
      (firstKernelMap D.firstCorrection) (secondKernelMap D.slope D.secondCorrection)) :=
  normalPolynomialMap_injective_of_middle _ _ _ _ (D.actualMiddleMultiplication_injective hc h)

end QuadraticLiftParameters
end IdealGeneration.QuadraticElimination
