module

public import IdealGeneration.QuadraticFlagEliminationBridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The projected component is determined by its two direct-sum conditions. -/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial QuadraticElimination

section ActualProjection

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
  (c : P × Bool → K) (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
  (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
  (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
  (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
    (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0)
  (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
  (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
  (C : NormalLiftVanishing c p₀ n₀ n₁ U V (firstKernelMap a) (secondKernelMap c b))

/-- The projected value is a flag pair and differs from the eliminated pair by a mixed product. -/
theorem projectedEliminatedMap_spec
    (x : Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K))) :
    let p := projectedEliminatedMap c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁ U V hU hV C x
    p ∈ (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
      (quadraticFlagVanishing (K := K) (P := P) (J := J)) ∧
    quadraticPhi U V (firstKernelMap a) (secondKernelMap c b) hU hV
      (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b) x - p ∈
        quadraticMixedImage c a b := by
  let e := quadraticFlagSplitting c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁
  let z := phiToAllowed c p₀ n₀ n₁ U V (firstKernelMap a) (secondKernelMap c b) hU hV
    (firstKernelMap_homogeneous a) (secondKernelMap_homogeneous c b) C x
  have he : ∀ y, (e y).val = y.1.val + y.2.val := by
    intro y
    simp only [e, quadraticFlagSplitting, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    exact disjointSumEquiv_val _ _ _ y
  have hz : z.val = (e.symm z).1.val + (e.symm z).2.val := by
    simpa only [LinearEquiv.apply_symm_apply] using he (e.symm z)
  refine ⟨(e.symm z).2.property, ?_⟩
  change z.val - (e.symm z).2.val ∈ quadraticMixedImage c a b
  rw [hz, add_sub_cancel_right]
  exact (e.symm z).1.property

end ActualProjection

/-- A linear map preserving both summands carries a projected value to the
corresponding projected value in the target. -/
theorem projected_value_natural {K M M' : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']
    (r : M →ₗ[K] M') (U W : Submodule K M) (U' W' : Submodule K M')
    (hU : U.map r ≤ U') (hW : W.map r ≤ W') (hd : Disjoint U' W')
    {f p : M} {p' : M'} (hf : f - p ∈ U) (hp : p ∈ W)
    (hf' : r f - p' ∈ U') (hp' : p' ∈ W') : r p = p' := by
  have hrU : r f - r p ∈ U' := by
    rw [← map_sub]
    exact hU ⟨f - p, hf, rfl⟩
  have hrW : r p ∈ W' := hW ⟨p, hp, rfl⟩
  have hdiff : r p - p' ∈ U' := by
    have heq : r p - p' = (r f - p') - (r f - r p) := by abel
    rw [heq]
    exact U'.sub_mem hf' hrU
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hd) _ hdiff (W'.sub_mem hrW hp'))

end IdealGeneration.QuadraticFlag
