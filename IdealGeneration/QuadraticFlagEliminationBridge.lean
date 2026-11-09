module

public import IdealGeneration.QuadraticFlagAssembly
public import IdealGeneration.QuadraticMiddleSpace
public import IdealGeneration.QuadraticProjection
public import IdealGeneration.QuadraticPhiLanding
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The concrete mixed-product and eliminated-image bridge

Coefficient transposition identifies trace products of the mixed kernel
with the quadratic image in the flag construction. The eliminated map is
then projected through the proved direct sum.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial Module QuadraticElimination

variable {K I J T H : Type*} [Field K] [Fintype I] [Fintype J]

/-- The first component of the actual mixed kernel. -/
def firstKernelMap (a : I → J → K) : (I → K) →ₗ[K] MvPolynomial (I ⊕ J) K :=
  Fintype.linearCombination K (firstGenerator a)

/-- The second component of the actual mixed kernel. -/
def secondKernelMap (c : I → K) (b : I → J → K) :
    (I → K) →ₗ[K] MvPolynomial (I ⊕ J) K :=
  Fintype.linearCombination K (secondGenerator c b)

theorem firstKernelMap_homogeneous (a : I → J → K) (v : I → K) :
    (firstKernelMap a v).IsHomogeneous 1 := by
  classical
  change (∑ i, v i • firstGenerator a i) ∈ homogeneousSubmodule (I ⊕ J) K 1
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply (isHomogeneous_X K (Sum.inl i)).add
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

theorem secondKernelMap_homogeneous (c : I → K) (b : I → J → K) (v : I → K) :
    (secondKernelMap c b v).IsHomogeneous 1 := by
  classical
  change (∑ i, v i • secondGenerator c b i) ∈ homogeneousSubmodule (I ⊕ J) K 1
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply (isHomogeneous_C_mul_X (c i) (Sum.inl i)).add
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

/-- The two coefficient arrangements differ only by matrix transposition. -/
theorem mixedTraceMap_eq_multiplication (c : I → K) (a b : I → J → K)
    (L : I ⊕ J → I → K) :
    mixedTraceMap (firstKernelMap a) (secondKernelMap c b) L =
      multiplication c a b (fun i j => L j i) := by
  classical
  apply Prod.ext <;>
    simp only [mixedTraceMap, firstKernelMap, secondKernelMap,
      Fintype.linearCombination_apply, multiplication, LinearMap.coe_mk, AddHom.coe_mk,
      linearPolynomial, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      Finset.mul_sum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The actual trace-product space is exactly the polynomial mixed image. -/
theorem mixedTraceMap_range_eq_mixedImage (c : I → K) (a b : I → J → K) :
    (mixedTraceMap (firstKernelMap a) (secondKernelMap c b)).range = mixedImage c a b := by
  ext f
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨fun i j => L j i, (mixedTraceMap_eq_multiplication c a b L).symm⟩
  · rintro ⟨L, rfl⟩
    exact ⟨fun j i => L i j, mixedTraceMap_eq_multiplication c a b (fun j i => L i j)⟩

/-- Forget the homogeneity proofs in a pair of trace quadrics. -/
def quadraticPairInclusion : (Quadrics K T × Quadrics K T) →ₗ[K]
    (MvPolynomial T K × MvPolynomial T K) :=
  (homogeneousSubmodule T K 2).subtype.prodMap (homogeneousSubmodule T K 2).subtype

@[simp] theorem quadraticPairInclusion_apply (f : Quadrics K T × Quadrics K T) :
    quadraticPairInclusion f = (f.1.val, f.2.val) := rfl

theorem quadraticPairInclusion_injective :
    Function.Injective (quadraticPairInclusion (K := K) (T := T)) := by
  intro f g h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

variable {P : Type*} [Fintype P]

theorem quadraticPairInclusion_multiplication (c : P × Bool → K) (a b : P × Bool → J → K) :
    (quadraticPairInclusion (K := K) (T := (P × Bool) ⊕ J)).comp (quadraticMultiplication c a b) =
      multiplication c a b := by
  ext L <;> rfl

/-- The homogeneous mixed image and its polynomial version are the same space. -/
theorem map_quadraticMixedImage (c : P × Bool → K) (a b : P × Bool → J → K) :
    (quadraticMixedImage c a b).map quadraticPairInclusion = mixedImage c a b := by
  rw [quadraticMixedImage, ← LinearMap.range_comp, quadraticPairInclusion_multiplication]
  rfl

section Phi
variable [AddCommGroup H] [Module K H]

omit [Fintype J] [Fintype P] in
@[simp] theorem quadraticPairInclusion_quadraticPhi
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1) :
    quadraticPairInclusion.comp (quadraticPhi U V g₁ g₂ hU hV hg₁ hg₂) =
      phi U V g₁ g₂ := by
  ext x <;> rfl

omit [Fintype J] [Fintype P] in
theorem map_quadraticPhi_range
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1) :
    (quadraticPhi U V g₁ g₂ hU hV hg₁ hg₂).range.map quadraticPairInclusion =
      (phi U V g₁ g₂).range := by
  rw [← LinearMap.range_comp, quadraticPairInclusion_quadraticPhi]

end Phi

/-- The actual normal-linear multiplication space in homogeneous trace coordinates. -/
def quadraticMiddleSpace (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (c : P × Bool → K) (a b : P × Bool → J → K) :
    Submodule K (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  (middleSpace U V (firstKernelMap a) (secondKernelMap c b)).comap quadraticPairInclusion

/-- Normal elimination gives the concrete sum of the mixed image and the eliminated image. -/
theorem quadraticMiddleSpace_eq
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (c : P × Bool → K) (a b : P × Bool → J → K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1) :
    quadraticMiddleSpace U V c a b = quadraticMixedImage c a b ⊔
      (quadraticPhi U V (firstKernelMap a) (secondKernelMap c b) hU hV
        (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b)).range := by
  rw [quadraticMiddleSpace,
    middleSpace_eq U V (firstKernelMap a) (secondKernelMap c b) hU hV
      (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b),
    mixedTraceMap_range_eq_mixedImage, ← map_quadraticMixedImage,
    ← map_quadraticPhi_range U V (firstKernelMap a) (secondKernelMap c b) hU hV
      (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b)]
  exact Submodule.comap_sup_map_of_injective quadraticPairInclusion_injective _ _

/-- Addition is the underlying map of the disjoint-sum equivalence. -/
theorem disjointSumEquiv_val {M : Type*} [AddCommGroup M] [Module K M]
    (U W : Submodule K M) (hd : Disjoint U W) (x : U × W) :
    ((disjointSumEquiv U W hd x : ↥(U ⊔ W)) : M) = (x.1 : M) + (x.2 : M) := by
  simp [disjointSumEquiv, LinearMap.coprod_apply]

/-- Projection of an allowed-valued map identifies its image in the target summand. -/
theorem projected_intersection_of_splitting
    {M E : Type*} [AddCommGroup M] [Module K M] [AddCommGroup E] [Module K E]
    (U W A : Submodule K M) (e : (U × W) ≃ₗ[K] A)
    (he : ∀ x : U × W, (e x : M) = (x.1 : M) + (x.2 : M))
    (f : E →ₗ[K] A) :
    (U ⊔ (A.subtype.comp f).range) ⊓ W =
      (W.subtype.comp ((LinearMap.snd K U W).comp (e.symm.toLinearMap.comp f))).range := by
  let iU : U →ₗ[K] A := e.toLinearMap.comp (LinearMap.inl K U W)
  let iW : W →ₗ[K] A := e.toLinearMap.comp (LinearMap.inr K U W)
  let p : A →ₗ[K] A := iW.comp ((LinearMap.snd K U W).comp e.symm.toLinearMap)
  have hpU : ∀ u ∈ iU.range, p u = 0 := by
    rintro u ⟨v, rfl⟩
    simp [p, iU, iW]
  have hpW : ∀ w ∈ iW.range, p w = w := by
    rintro w ⟨v, rfl⟩
    simp [p, iW]
  have hp : ∀ m, p m ∈ iW.range := fun m => ⟨(e.symm m).2, rfl⟩
  have hsub : ∀ m, m - p m ∈ iU.range := by
    intro m
    refine ⟨(e.symm m).1, ?_⟩
    change e ((e.symm m).1, 0) = m - e (0, (e.symm m).2)
    apply eq_sub_iff_add_eq.mpr
    rw [← map_add]
    simp
  have h := QuadraticProjection.projection_range_intersection iU.range iW.range p f
    hpU hpW hp hsub
  have hiU : A.subtype.comp iU = U.subtype := by
    ext u
    simpa [iU] using he (u, 0)
  have hiW : A.subtype.comp iW = W.subtype := by
    ext w
    simpa [iW] using he (0, w)
  have hmU : iU.range.map A.subtype = U := by
    rw [← LinearMap.range_comp, hiU, Submodule.range_subtype]
  have hmW : iW.range.map A.subtype = W := by
    rw [← LinearMap.range_comp, hiW, Submodule.range_subtype]
  have hm := congrArg (Submodule.map A.subtype) h
  rw [Submodule.map_inf _ Subtype.val_injective, Submodule.map_sup, hmU, hmW,
    ← LinearMap.range_comp, ← LinearMap.range_comp] at hm
  have hmaps : A.subtype.comp (p.comp f) =
      W.subtype.comp ((LinearMap.snd K U W).comp (e.symm.toLinearMap.comp f)) := by
    rw [← LinearMap.comp_assoc, show A.subtype.comp p =
      W.subtype.comp ((LinearMap.snd K U W).comp e.symm.toLinearMap) by
        dsimp only [p]
        rw [← LinearMap.comp_assoc, hiW]]
    rfl
  rw [hmaps] at hm
  exact hm

section ActualProjection

variable (c : P × Bool → K) (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
  (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
  (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
  (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
    (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0)
  (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
  (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
  (C : NormalLiftVanishing c p₀ n₀ n₁ U V (firstKernelMap a) (secondKernelMap c b))

/-- The actual map `πφ` whose range is the residual quadratic space `W'`. -/
def projectedEliminatedMap :
    Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K)) →ₗ[K]
      (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) :=
  ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
    (quadraticFlagVanishing (K := K) (P := P) (J := J))).subtype.comp
      ((quadraticFlagProjection c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁).comp
        (phiToAllowed c p₀ n₀ n₁ U V (firstKernelMap a) (secondKernelMap c b) hU hV
          (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b) C))

/-- The image of `πφ` is exactly the intersection of actual normal-linear
multiplication with the pair of scalar flag ideals. -/
theorem quadraticMiddleSpace_inf_flag :
    quadraticMiddleSpace U V c a b ⊓
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
        (quadraticFlagVanishing (K := K) (P := P) (J := J)) =
    (projectedEliminatedMap c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁ U V hU hV C).range := by
  rw [quadraticMiddleSpace_eq U V c a b hU hV]
  let e := quadraticFlagSplitting c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁
  have he : ∀ x, (e x).val = x.1.val + x.2.val := by
    intro x
    simp only [e, quadraticFlagSplitting, LinearEquiv.trans_apply,
      LinearEquiv.coe_ofEq_apply]
    exact disjointSumEquiv_val _ _ _ x
  have h := projected_intersection_of_splitting _ _ _ e he
    (phiToAllowed c p₀ n₀ n₁ U V (firstKernelMap a) (secondKernelMap c b) hU hV
      (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b) C)
  exact h

/-- The actual residual quadratic space has dimension at most `2h+2`. -/
theorem finrank_projectedEliminatedMap_range_le :
    finrank K (projectedEliminatedMap c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁ U V hU hV C).range ≤
      2 * Fintype.card (P × Bool) + 2 := by
  apply (LinearMap.finrank_range_le _).trans_eq
  simpa only [Module.finrank_pi] using
    (finrank_explicitOmega (K := K) (H := P × Bool → K))

include hc hn₀ hn₁ h₀ h₁ hU hV C in
/-- The same bound holds for the intersection formulation of `W'`. -/
theorem finrank_quadraticMiddleSpace_inf_flag_le :
    finrank K ↥(quadraticMiddleSpace U V c a b ⊓
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
        (quadraticFlagVanishing (K := K) (P := P) (J := J))) ≤
      2 * Fintype.card (P × Bool) + 2 := by
  rw [quadraticMiddleSpace_inf_flag c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁ U V hU hV C]
  exact finrank_projectedEliminatedMap_range_le c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁ U V hU hV C

end ActualProjection
end IdealGeneration.QuadraticFlag
