module

public import IdealGeneration.QuadraticFlagAssembly
public import IdealGeneration.QuadraticMultiplicationElimination

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The explicit elimination map takes values in the actual normal-condition space. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial Module QuadraticFlag

variable {K P J H : Type*} [Field K] [Fintype P] [Fintype J]
  [AddCommGroup H] [Module K H]

/-- A base coordinate representative inside the full trace vector space. -/
def traceBasePoint (i : P × Bool) : (P × Bool) ⊕ J → K := by
  classical
  exact Sum.elim (coordinatePoint i) (fun _ => 0)

/-- Actual cone-point vanishing for the chosen normal lifts and mixed kernel. -/
structure NormalLiftVanishing (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K) where
  baseHeight : P × Bool → K
  layerHeight₀ : J → K
  layerHeight₁ : J → K
  baseHeight_ne : ∀ i, baseHeight i ≠ 0
  layerHeight₀_ne : ∀ j, layerHeight₀ j ≠ 0
  layerHeight₁_ne : ∀ j, layerHeight₁ j ≠ 0
  base : ∀ i z, liftedQuadratic (aeval (traceBasePoint i))
    (baseHeight i * c i) (baseHeight i * (-1)) U V g₁ g₂ z = 0
  layer₀ : ∀ j z, liftedQuadratic (aeval (layerPoint j))
    (layerHeight₀ j * (n₀ j).1) (layerHeight₀ j * (n₀ j).2) U V g₁ g₂ z = 0
  layer₁ : ∀ j z, liftedQuadratic (aeval (pairedLayerPoint p₀ j))
    (layerHeight₁ j * (n₁ j).1) (layerHeight₁ j * (n₁ j).2) U V g₁ g₂ z = 0

/-- Record the proven quadratic homogeneity of both eliminated components. -/
def quadraticPhi
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1) :
    Omega (LinearMap.fst K (Fin 3 → K) H) →ₗ[K]
      (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) where
  toFun x := (⟨(phi U V g₁ g₂ x).1, (phi_homogeneous U V g₁ g₂ hU hV hg₁ hg₂ x).1⟩,
    ⟨(phi U V g₁ g₂ x).2, (phi_homogeneous U V g₁ g₂ hU hV hg₁ hg₂ x).2⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((phi U V g₁ g₂).map_add x y)
    · exact congrArg Prod.snd ((phi U V g₁ g₂).map_add x y)
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((phi U V g₁ g₂).map_smul r x)
    · exact congrArg Prod.snd ((phi U V g₁ g₂).map_smul r x)

omit [Fintype P] [Fintype J] in
/-- Equation (A.3) and actual cone-point vanishing put `φ` in `A`. -/
theorem quadraticPhi_mem_allowed
    (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (C : NormalLiftVanishing c p₀ n₀ n₁ U V g₁ g₂)
    (x : Omega (LinearMap.fst K (Fin 3 → K) H)) :
    quadraticPhi U V g₁ g₂ hU hV hg₁ hg₂ x ∈ allowedQuadraticPairs c p₀ n₀ n₁ := by
  classical
  change quadraticConditionMap c p₀ n₀ n₁ (quadraticPhi U V g₁ g₂ hU hV hg₁ hg₂ x) = 0
  apply Prod.ext
  · funext i
    have h := phi_normal_evaluation_scaled (aeval (traceBasePoint i))
      (c i) (-1) (C.baseHeight i) (C.baseHeight_ne i) U V g₁ g₂ (C.base i) x
    change c i * eval (traceBasePoint i) (phi U V g₁ g₂ x).1 +
      (-1) * eval (traceBasePoint i) (phi U V g₁ g₂ x).2 = 0 at h
    change eval (coordinatePoint i) (restrictBase (phi U V g₁ g₂ x).2) -
      c i * eval (coordinatePoint i) (restrictBase (phi U V g₁ g₂ x).1) = 0
    rw [eval_restrictBase, eval_restrictBase]
    change eval (traceBasePoint i) (phi U V g₁ g₂ x).2 -
      c i * eval (traceBasePoint i) (phi U V g₁ g₂ x).1 = 0
    linear_combination -h
  · apply Prod.ext <;> funext j
    · exact phi_normal_evaluation_scaled (aeval (layerPoint j))
        (n₀ j).1 (n₀ j).2 (C.layerHeight₀ j) (C.layerHeight₀_ne j)
        U V g₁ g₂ (C.layer₀ j) x
    · exact phi_normal_evaluation_scaled (aeval (pairedLayerPoint p₀ j))
        (n₁ j).1 (n₁ j).2 (C.layerHeight₁ j) (C.layerHeight₁_ne j)
        U V g₁ g₂ (C.layer₁ j) x

/-- The elimination map with codomain restricted to the actual allowed space. -/
def phiToAllowed
    (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (C : NormalLiftVanishing c p₀ n₀ n₁ U V g₁ g₂) :
    Omega (LinearMap.fst K (Fin 3 → K) H) →ₗ[K] allowedQuadraticPairs c p₀ n₀ n₁ :=
  (quadraticPhi U V g₁ g₂ hU hV hg₁ hg₂).codRestrict _
    (quadraticPhi_mem_allowed c p₀ n₀ n₁ U V g₁ g₂ hU hV hg₁ hg₂ C)

/-- Vanishing of the three selected lifts and of the mixed kernel is enough
for the full represented family to vanish at a cone point. -/
theorem liftedVanishing_of_basis
    {R S : Type*} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (ψ : R →ₐ[K] S) (s t : S) (U V : Fin 3 → R) (g₁ g₂ : H →ₗ[K] R)
    (hL : ∀ i, normalLift ψ s t U V i = 0)
    (hg : ∀ h, s * ψ (g₁ h) + t * ψ (g₂ h) = 0) :
    ∀ x, liftedQuadratic ψ s t U V g₁ g₂ x = 0 := by
  intro x
  rw [liftedQuadratic_eq_normalLifts, hL 0, hL 1, hL 2]
  simpa [mul_comm] using hg x.2

/-- Projecting the actual allowed-valued `φ` has dimension at most `2h+2`. -/
theorem finrank_projection_phiToAllowed_le [FiniteDimensional K H]
    (c : P × Bool → K) (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
    (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
    (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
      (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0)
    (U V : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hU : ∀ i, (U i).IsHomogeneous 1) (hV : ∀ i, (V i).IsHomogeneous 1)
    (hg₁ : ∀ h, (g₁ h).IsHomogeneous 1) (hg₂ : ∀ h, (g₂ h).IsHomogeneous 1)
    (C : NormalLiftVanishing c p₀ n₀ n₁ U V g₁ g₂) :
    finrank K ((quadraticFlagProjection c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁).comp
      (phiToAllowed c p₀ n₀ n₁ U V g₁ g₂ hU hV hg₁ hg₂ C)).range ≤
        2 * finrank K H + 2 := by
  exact (LinearMap.finrank_range_le _).trans_eq finrank_explicitOmega

end IdealGeneration.QuadraticElimination
