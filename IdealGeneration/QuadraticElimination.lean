module

public import IdealGeneration.QuadraticFlag
public import IdealGeneration.QuadraticA3
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Normal-degree elimination for two normal variables

The four coefficients of a normal cubic are the actual coefficients obtained
from `s Q_s + t Q_t`. Their kernel controls the source of the elimination map
in Appendix A.2.
-/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- The coefficient map of `(Q_s,Q_t) ↦ s Q_s+t Q_t`. -/
def normalCubicMap : ((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] (Fin 4 → K) where
  toFun Q := ![Q.1 0, Q.1 1 + Q.2 0, Q.1 2 + Q.2 1, Q.2 2]
  map_add' Q R := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' r Q := by
    funext i
    fin_cases i <;> simp <;> ring

/-- Every normal cubic has such a presentation. -/
theorem normalCubicMap_surjective : Function.Surjective (normalCubicMap (K := K)) := by
  intro v
  refine ⟨(![v 0, v 1, v 2], ![0, 0, v 3]), ?_⟩
  funext i
  fin_cases i <;> simp [normalCubicMap]

/-- The kernel is exactly the two familiar normal syzygies. -/
theorem normalCubicMap_eq_zero_iff (Q : (Fin 3 → K) × (Fin 3 → K)) :
    normalCubicMap Q = 0 ↔
      Q.1 0 = 0 ∧ Q.1 1 + Q.2 0 = 0 ∧ Q.1 2 + Q.2 1 = 0 ∧ Q.2 2 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i <;> simp_all [normalCubicMap]

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The normal-cubic part of two normal multiples of residual quadrics. -/
def omegaMap (q : E →ₗ[K] (Fin 3 → K)) : (E × E) →ₗ[K] (Fin 4 → K) :=
  normalCubicMap.comp (q.prodMap q)

/-- The source denoted by `Ω` in Appendix A.2. -/
def Omega (q : E →ₗ[K] (Fin 3 → K)) := (omegaMap q).ker

theorem omegaMap_surjective (q : E →ₗ[K] (Fin 3 → K)) (hq : Function.Surjective q) :
    Function.Surjective (omegaMap q) := by
  intro v
  obtain ⟨Q, hQ⟩ := normalCubicMap_surjective (K := K) v
  obtain ⟨x, hx⟩ := hq Q.1
  obtain ⟨y, hy⟩ := hq Q.2
  refine ⟨(x, y), ?_⟩
  change normalCubicMap (q x, q y) = v
  rw [hx, hy]
  exact hQ

/-- Surjectivity of the pure-normal quadratic part gives `dim Ω=2h+2`,
where `h` is the dimension of its kernel. -/
theorem finrank_Omega [FiniteDimensional K E]
    (q : E →ₗ[K] (Fin 3 → K)) (hq : Function.Surjective q) :
    finrank K (Omega q) = 2 * finrank K q.ker + 2 := by
  have hqrank := q.finrank_range_add_finrank_ker
  have horank := (omegaMap q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, Module.finrank_pi] at hqrank
  rw [LinearMap.range_eq_top.mpr (omegaMap_surjective q hq), finrank_top,
    Module.finrank_pi, Module.finrank_prod] at horank
  simp only [Fintype.card_fin] at hqrank horank
  change finrank K (omegaMap q).ker = _
  omega

/-- A quadratic expression in two specified elements of an algebra. -/
def quadraticExpression {R : Type*} [CommRing R] (s t : R) (Q : Fin 3 → R) : R :=
  Q 0 * s ^ 2 + Q 1 * s * t + Q 2 * t ^ 2

/-- The kernel condition is genuine cancellation of the normal cubic. -/
theorem normalCubic_cancellation {R : Type*} [CommRing R] [Algebra K R]
    (s t : R) (Q : (Fin 3 → K) × (Fin 3 → K))
    (hQ : normalCubicMap Q = 0) :
    s * quadraticExpression s t (fun i => algebraMap K R (Q.1 i)) +
      t * quadraticExpression s t (fun i => algebraMap K R (Q.2 i)) = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := (normalCubicMap_eq_zero_iff Q).mp hQ
  calc
    _ = s ^ 3 * algebraMap K R (Q.1 0) +
        s ^ 2 * t * algebraMap K R (Q.1 1 + Q.2 0) +
        s * t ^ 2 * algebraMap K R (Q.1 2 + Q.2 1) +
        t ^ 3 * algebraMap K R (Q.2 2) := by
          simp only [quadraticExpression, map_add]
          ring
    _ = 0 := by rw [h0, h1, h2, h3]; simp

section ExplicitElimination

variable {H R : Type*} [AddCommGroup H] [Module K H] [CommRing R] [Algebra K R]

/-- A quadric is recorded by its three pure-normal coefficients and its mixed kernel part. -/
abbrev LiftSpace := (Fin 3 → K) × H

/-- The mixed linear coefficient of a quadric with chosen normal lifts. -/
def lowerPart (U : Fin 3 → R) (g : H →ₗ[K] R) : LiftSpace (K := K) (H := H) →ₗ[K] R where
  toFun x := (∑ i, x.1 i • U i) + g x.2
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
    abel
  map_smul' r x := by
    simp [smul_add, Finset.smul_sum, smul_smul]

/-- The three normal lifts together with the mixed generators give the indicated full quadric. -/
def liftedQuadratic {S : Type*} [CommRing S] [Algebra K S]
    (ψ : R →ₐ[K] S) (s t : S) (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (x : LiftSpace (K := K) (H := H)) : S :=
  quadraticExpression s t (fun i => algebraMap K S (x.1 i)) +
    s * ψ (lowerPart U g₁ x) + t * ψ (lowerPart V g₂ x)

/-- The explicit coefficient pair left by normal-degree elimination. -/
def prePhi (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) :
    (LiftSpace (K := K) (H := H) × LiftSpace (K := K) (H := H)) →ₗ[K] (R × R) where
  toFun x :=
    (-U 0 * lowerPart U g₁ x.1 - U 1 * (lowerPart V g₂ x.1 + lowerPart U g₁ x.2) -
        U 2 * lowerPart V g₂ x.2,
     -V 0 * lowerPart U g₁ x.1 - V 1 * (lowerPart V g₂ x.1 + lowerPart U g₁ x.2) -
        V 2 * lowerPart V g₂ x.2)
  map_add' x y := by
    apply Prod.ext <;> simp [map_add] <;> ring
  map_smul' r x := by
    apply Prod.ext <;> simp [map_smul, Algebra.smul_def] <;> ring

/-- The map `φ` on the normal-cubic kernel, recording the surviving coefficient pair. -/
def phi (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) :
    Omega (LinearMap.fst K (Fin 3 → K) H) →ₗ[K] (R × R) :=
  (prePhi U V g₁ g₂).comp (Omega (LinearMap.fst K (Fin 3 → K) H)).subtype

/-- The three normal lifts add exactly three dimensions to the mixed kernel. -/
theorem finrank_normalPart_kernel [FiniteDimensional K H] :
    finrank K (LinearMap.fst K (Fin 3 → K) H).ker = finrank K H := by
  rw [LinearMap.ker_fst]
  apply LinearMap.finrank_range_of_inj
  intro x y h
  exact congrArg Prod.snd h

/-- The explicit normal-cubic kernel has the dimension used in Appendix A.2. -/
theorem finrank_explicitOmega [FiniteDimensional K H] :
    finrank K (Omega (LinearMap.fst K (Fin 3 → K) H)) = 2 * finrank K H + 2 := by
  rw [finrank_Omega _ (LinearMap.fst_surjective), finrank_normalPart_kernel]

/-- The eliminated pair has at most `2h+2` independent values. -/
theorem finrank_phi_range_le [FiniteDimensional K H]
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) :
    finrank K (phi U V g₁ g₂).range ≤ 2 * finrank K H + 2 := by
  exact (LinearMap.finrank_range_le (phi U V g₁ g₂)).trans_eq finrank_explicitOmega

/-- Any linear projection of these pairs has the same upper bound. -/
theorem finrank_projected_phi_range_le [FiniteDimensional K H]
    {T : Type*} [AddCommGroup T] [Module K T]
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R) (π : (R × R) →ₗ[K] T) :
    finrank K (π.comp (phi U V g₁ g₂)).range ≤ 2 * finrank K H + 2 := by
  exact (LinearMap.finrank_range_le (π.comp (phi U V g₁ g₂))).trans_eq finrank_explicitOmega

/-- The formula defining `φ` is exactly the polynomial identity (A.3). -/
theorem phi_elimination_identity {S : Type*} [CommRing S] [Algebra K S]
    (ψ : R →ₐ[K] S) (s t : S) (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    -(s ^ 2 + s * ψ (U 0) + t * ψ (V 0)) * ψ (lowerPart U g₁ x.val.1) -
      (s * t + s * ψ (U 1) + t * ψ (V 1)) *
        ψ (lowerPart V g₂ x.val.1 + lowerPart U g₁ x.val.2) -
      (t ^ 2 + s * ψ (U 2) + t * ψ (V 2)) * ψ (lowerPart V g₂ x.val.2) +
      s * liftedQuadratic ψ s t U V g₁ g₂ x.val.1 +
      t * liftedQuadratic ψ s t U V g₁ g₂ x.val.2 =
      s * ψ (phi U V g₁ g₂ x).1 + t * ψ (phi U V g₁ g₂ x).2 := by
  have hx := x.property
  change normalCubicMap (x.val.1.1, x.val.2.1) = 0 at hx
  have hc := normalCubic_cancellation s t (x.val.1.1, x.val.2.1) hx
  have h := IdealGeneration.QuadraticA3.normalElimination_expanded s t
    (ψ (U 0)) (ψ (V 0)) (ψ (U 1)) (ψ (V 1)) (ψ (U 2)) (ψ (V 2))
    (quadraticExpression s t (fun i => algebraMap K S (x.val.1.1 i)))
    (quadraticExpression s t (fun i => algebraMap K S (x.val.2.1 i)))
    (ψ (lowerPart U g₁ x.val.1)) (ψ (lowerPart V g₂ x.val.1))
    (ψ (lowerPart U g₁ x.val.2)) (ψ (lowerPart V g₂ x.val.2)) hc
  simpa [liftedQuadratic, phi, prePhi, map_add, map_sub, map_mul, map_neg] using h

/-- If the represented quadrics vanish at a cone point, the eliminated pair
satisfies its normal equation. -/
theorem phi_normal_evaluation
    (ψ : R →ₐ[K] K) (s t : K) (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (hpoint : ∀ z, liftedQuadratic ψ s t U V g₁ g₂ z = 0)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    s * ψ (phi U V g₁ g₂ x).1 + t * ψ (phi U V g₁ g₂ x).2 = 0 := by
  have h0 := hpoint (![1, 0, 0], 0)
  have h1 := hpoint (![0, 1, 0], 0)
  have h2 := hpoint (![0, 0, 1], 0)
  simp [liftedQuadratic, lowerPart, quadraticExpression, Fin.sum_univ_three] at h0 h1 h2
  have h := phi_elimination_identity ψ s t U V g₁ g₂ x
  rw [h0, h1, h2, hpoint x.val.1, hpoint x.val.2] at h
  simpa using h.symm

/-- A nonzero cone height cancels from the normal equation. -/
theorem phi_normal_evaluation_scaled
    (ψ : R →ₐ[K] K) (s t θ : K) (hθ : θ ≠ 0)
    (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (hpoint : ∀ z, liftedQuadratic ψ (θ * s) (θ * t) U V g₁ g₂ z = 0)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    s * ψ (phi U V g₁ g₂ x).1 + t * ψ (phi U V g₁ g₂ x).2 = 0 := by
  have h := phi_normal_evaluation ψ (θ * s) (θ * t) U V g₁ g₂ hpoint x
  have he : θ * (s * ψ (phi U V g₁ g₂ x).1 + t * ψ (phi U V g₁ g₂ x).2) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp he).resolve_left hθ

end ExplicitElimination

section HomogeneousElimination

variable {H T : Type*} [AddCommGroup H] [Module K H]

/-- Lower terms of the chosen lifts remain linear trace forms. -/
theorem lowerPart_homogeneous
    (U : Fin 3 → MvPolynomial T K) (g : H →ₗ[K] MvPolynomial T K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hg : ∀ h, (g h).IsHomogeneous 1)
    (x : LiftSpace (K := K) (H := H)) :
    (lowerPart U g x).IsHomogeneous 1 := by
  change (∑ i, x.1 i • U i) + g x.2 ∈ homogeneousSubmodule T K 1
  exact (homogeneousSubmodule T K 1).add_mem
    ((homogeneousSubmodule T K 1).sum_mem fun i _ =>
      (homogeneousSubmodule T K 1).smul_mem (x.1 i) (hU i)) (hg x.2)

/-- The surviving pair consists of genuine homogeneous trace quadrics. -/
theorem phi_homogeneous
    (U V : Fin 3 → MvPolynomial T K) (g₁ g₂ : H →ₗ[K] MvPolynomial T K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    (phi U V g₁ g₂ x).1.IsHomogeneous 2 ∧ (phi U V g₁ g₂ x).2.IsHomogeneous 2 := by
  have hus := lowerPart_homogeneous U g₁ hU hg₁ x.val.1
  have hvs := lowerPart_homogeneous V g₂ hV hg₂ x.val.1
  have hut := lowerPart_homogeneous U g₁ hU hg₁ x.val.2
  have hvt := lowerPart_homogeneous V g₂ hV hg₂ x.val.2
  constructor
  · exact (((hU 0).neg.mul hus).sub ((hU 1).mul (hvs.add hut))).sub ((hU 2).mul hvt)
  · exact (((hV 0).neg.mul hus).sub ((hV 1).mul (hvs.add hut))).sub ((hV 2).mul hvt)

end HomogeneousElimination


end IdealGeneration.QuadraticElimination
