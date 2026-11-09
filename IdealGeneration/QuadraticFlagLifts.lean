module

public import IdealGeneration.QuadraticPhiLanding

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Explicit normal lifts for the paired two-normal cone construction. -/

noncomputable section
namespace IdealGeneration.QuadraticElimination
open MvPolynomial QuadraticFlag

variable {K P J : Type*} [Field K]

/-- Independent layer directions and nonzero cone heights. -/
structure QuadraticLiftParameters (K P J : Type*) [Field K] where
  slope : P × Bool → K
  distinguishedPair : P
  normal₀ : J → K × K
  normal₁ : J → K × K
  baseHeight : P × Bool → K
  height₀ : J → K
  height₁ : J → K
  baseHeight_ne : ∀ i, baseHeight i ≠ 0
  height₀_ne : ∀ j, height₀ j ≠ 0
  height₁_ne : ∀ j, height₁ j ≠ 0
  determinant_ne : ∀ j, (normal₀ j).1 * (normal₁ j).2 -
    (normal₁ j).1 * (normal₀ j).2 ≠ 0

/-- The values of the three pure-normal quadratic monomials. -/
def normalBasisValue (i : Fin 3) (s t : K) : K := (![s ^ 2, s * t, t ^ 2] : Fin 3 → K) i

theorem normalBasisValue_scale (i : Fin 3) (θ s t : K) :
    normalBasisValue i (θ * s) (θ * t) = θ ^ 2 * normalBasisValue i s t := by
  fin_cases i <;> simp [normalBasisValue] <;> ring

/-- Solving the two independent normal equations with prescribed targets. -/
def solveLayerNormal (n₀ n₁ : K × K) (r₀ r₁ : K) : K × K :=
  let d := n₀.1 * n₁.2 - n₁.1 * n₀.2
  ((n₁.2 * r₀ - n₀.2 * r₁) / d, (n₀.1 * r₁ - n₁.1 * r₀) / d)

theorem solveLayerNormal_spec (n₀ n₁ : K × K) (r₀ r₁ : K)
    (hd : n₀.1 * n₁.2 - n₁.1 * n₀.2 ≠ 0) :
    n₀.1 * (solveLayerNormal n₀ n₁ r₀ r₁).1 +
      n₀.2 * (solveLayerNormal n₀ n₁ r₀ r₁).2 = r₀ ∧
    n₁.1 * (solveLayerNormal n₀ n₁ r₀ r₁).1 +
      n₁.2 * (solveLayerNormal n₀ n₁ r₀ r₁).2 = r₁ := by
  let d := n₀.1 * n₁.2 - n₁.1 * n₀.2
  have hd' : d ≠ 0 := hd
  change n₀.1 * ((n₁.2 * r₀ - n₀.2 * r₁) / d) +
      n₀.2 * ((n₀.1 * r₁ - n₁.1 * r₀) / d) = r₀ ∧
    n₁.1 * ((n₁.2 * r₀ - n₀.2 * r₁) / d) +
      n₁.2 * ((n₀.1 * r₁ - n₁.1 * r₀) / d) = r₁
  constructor
  · calc
      _ = (n₀.1 * (n₁.2 * r₀ - n₀.2 * r₁) +
          n₀.2 * (n₀.1 * r₁ - n₁.1 * r₀)) / d := by ring
      _ = (d * r₀) / d := by congr 1; dsimp [d]; ring
      _ = r₀ := mul_div_cancel_left₀ _ hd'
  · calc
      _ = (n₁.1 * (n₁.2 * r₀ - n₀.2 * r₁) +
          n₁.2 * (n₀.1 * r₁ - n₁.1 * r₀)) / d := by ring
      _ = (d * r₁) / d := by congr 1; dsimp [d]; ring
      _ = r₁ := mul_div_cancel_left₀ _ hd'

namespace QuadraticLiftParameters
variable (D : QuadraticLiftParameters K P J)

/-- The base coefficient of the second mixed term after normalizing the first to zero. -/
def baseCoefficient (k : Fin 3) (i : P × Bool) : K :=
  D.baseHeight i * normalBasisValue k (D.slope i) (-1)

variable [Fintype P]

/-- The base contribution at the distinguished paired support. -/
def pairedBaseValue (k : Fin 3) : K :=
  ∑ i, D.baseCoefficient k i * pairPoint D.distinguishedPair i

/-- The two mixed coefficients in each layer, solved independently. -/
def layerCoefficients (k : Fin 3) (j : J) : K × K :=
  solveLayerNormal (D.normal₀ j) (D.normal₁ j)
    (-D.height₀ j * normalBasisValue k (D.normal₀ j).1 (D.normal₀ j).2)
    (-D.height₁ j * normalBasisValue k (D.normal₁ j).1 (D.normal₁ j).2 -
      (D.normal₁ j).2 * D.pairedBaseValue k)

theorem layerCoefficients_spec (k : Fin 3) (j : J) :
    (D.normal₀ j).1 * (D.layerCoefficients k j).1 +
      (D.normal₀ j).2 * (D.layerCoefficients k j).2 =
        -D.height₀ j * normalBasisValue k (D.normal₀ j).1 (D.normal₀ j).2 ∧
    (D.normal₁ j).1 * (D.layerCoefficients k j).1 +
      (D.normal₁ j).2 * (D.layerCoefficients k j).2 =
        -D.height₁ j * normalBasisValue k (D.normal₁ j).1 (D.normal₁ j).2 -
          (D.normal₁ j).2 * D.pairedBaseValue k :=
  solveLayerNormal_spec _ _ _ _ (D.determinant_ne j)

variable [Fintype J]

/-- The first mixed linear form of the normalized lift. -/
def firstLift (k : Fin 3) : MvPolynomial ((P × Bool) ⊕ J) K :=
  linearPolynomial (Sum.elim (fun _ => 0) (fun j => (D.layerCoefficients k j).1))

/-- The second mixed linear form of the normalized lift. -/
def secondLift (k : Fin 3) : MvPolynomial ((P × Bool) ⊕ J) K :=
  linearPolynomial (Sum.elim (D.baseCoefficient k) (fun j => (D.layerCoefficients k j).2))

theorem firstLift_homogeneous (k : Fin 3) : (D.firstLift k).IsHomogeneous 1 :=
  linearPolynomial_isHomogeneous _

theorem secondLift_homogeneous (k : Fin 3) : (D.secondLift k).IsHomogeneous 1 :=
  linearPolynomial_isHomogeneous _

@[simp] theorem eval_firstLift_base (k : Fin 3) (i : P × Bool) :
    eval (traceBasePoint i) (D.firstLift k) = 0 := by
  classical
  simp [firstLift, traceBasePoint, coordinatePoint]

@[simp] theorem eval_secondLift_base (k : Fin 3) (i : P × Bool) :
    eval (traceBasePoint i) (D.secondLift k) = D.baseCoefficient k i := by
  classical
  simp [secondLift, traceBasePoint, coordinatePoint]

@[simp] theorem eval_firstLift_layer (k : Fin 3) (j : J) :
    eval (layerPoint j) (D.firstLift k) = (D.layerCoefficients k j).1 := by
  classical
  simp [firstLift, layerPoint, coordinatePoint]

@[simp] theorem eval_secondLift_layer (k : Fin 3) (j : J) :
    eval (layerPoint j) (D.secondLift k) = (D.layerCoefficients k j).2 := by
  classical
  simp [secondLift, layerPoint, coordinatePoint]

@[simp] theorem eval_firstLift_pairedLayer (k : Fin 3) (j : J) :
    eval (pairedLayerPoint D.distinguishedPair j) (D.firstLift k) = (D.layerCoefficients k j).1 := by
  classical
  simp [firstLift, pairedLayerPoint, coordinatePoint]

@[simp] theorem eval_secondLift_pairedLayer (k : Fin 3) (j : J) :
    eval (pairedLayerPoint D.distinguishedPair j) (D.secondLift k) =
      D.pairedBaseValue k + (D.layerCoefficients k j).2 := by
  classical
  simp [secondLift, pairedLayerPoint, coordinatePoint, pairedBaseValue]

/-- Normal-lift evaluation is the pure quadratic monomial plus its mixed corrections. -/
theorem normalLift_eq_basisValue (ψ : MvPolynomial ((P × Bool) ⊕ J) K →ₐ[K] K)
    (s t : K) (k : Fin 3) :
    normalLift ψ s t D.firstLift D.secondLift k =
      normalBasisValue k s t + s * ψ (D.firstLift k) + t * ψ (D.secondLift k) := by
  fin_cases k <;> simp [normalLift, normalBasisValue]

/-- The three normalized lifts vanish over every base coordinate support. -/
theorem normalLift_base (k : Fin 3) (i : P × Bool) :
    normalLift (aeval (traceBasePoint i)) (D.baseHeight i * D.slope i)
      (D.baseHeight i * (-1)) D.firstLift D.secondLift k = 0 := by
  rw [D.normalLift_eq_basisValue, normalBasisValue_scale]
  simp [MvPolynomial.aeval_eq_eval, baseCoefficient]
  ring

/-- The first layer equation holds by the explicit two-by-two solve. -/
theorem normalLift_layer₀ (k : Fin 3) (j : J) :
    normalLift (aeval (layerPoint j)) (D.height₀ j * (D.normal₀ j).1)
      (D.height₀ j * (D.normal₀ j).2) D.firstLift D.secondLift k = 0 := by
  rw [D.normalLift_eq_basisValue, normalBasisValue_scale]
  simp only [MvPolynomial.aeval_eq_eval, eval_firstLift_layer, eval_secondLift_layer]
  linear_combination D.height₀ j * (D.layerCoefficients_spec k j).1

/-- The second layer equation also includes the known paired base contribution. -/
theorem normalLift_layer₁ (k : Fin 3) (j : J) :
    normalLift (aeval (pairedLayerPoint D.distinguishedPair j))
      (D.height₁ j * (D.normal₁ j).1) (D.height₁ j * (D.normal₁ j).2)
      D.firstLift D.secondLift k = 0 := by
  rw [D.normalLift_eq_basisValue, normalBasisValue_scale]
  simp only [MvPolynomial.aeval_eq_eval, eval_firstLift_pairedLayer, eval_secondLift_pairedLayer]
  linear_combination D.height₁ j * (D.layerCoefficients_spec k j).2

variable {H : Type*} [AddCommGroup H] [Module K H]

/-- The constructed lifts give actual point vanishing as soon as the mixed
kernel satisfies its defining linear normal equations. -/
def normalLiftVanishing
    (g₁ g₂ : H →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (hbase : ∀ i h, D.slope i * eval (traceBasePoint i) (g₁ h) -
      eval (traceBasePoint i) (g₂ h) = 0)
    (h₀ : ∀ j h, (D.normal₀ j).1 * eval (layerPoint j) (g₁ h) +
      (D.normal₀ j).2 * eval (layerPoint j) (g₂ h) = 0)
    (h₁ : ∀ j h, (D.normal₁ j).1 * eval (pairedLayerPoint D.distinguishedPair j) (g₁ h) +
      (D.normal₁ j).2 * eval (pairedLayerPoint D.distinguishedPair j) (g₂ h) = 0) :
    NormalLiftVanishing D.slope D.distinguishedPair D.normal₀ D.normal₁ D.firstLift D.secondLift g₁ g₂ where
  baseHeight := D.baseHeight
  layerHeight₀ := D.height₀
  layerHeight₁ := D.height₁
  baseHeight_ne := D.baseHeight_ne
  layerHeight₀_ne := D.height₀_ne
  layerHeight₁_ne := D.height₁_ne
  base i := liftedVanishing_of_basis _ _ _ _ _ _ _ (fun k => D.normalLift_base k i) (by
    intro h
    simp only [MvPolynomial.aeval_eq_eval]
    linear_combination D.baseHeight i * hbase i h)
  layer₀ j := liftedVanishing_of_basis _ _ _ _ _ _ _ (fun k => D.normalLift_layer₀ k j) (by
    intro h
    simp only [MvPolynomial.aeval_eq_eval]
    linear_combination D.height₀ j * h₀ j h)
  layer₁ j := liftedVanishing_of_basis _ _ _ _ _ _ _ (fun k => D.normalLift_layer₁ k j) (by
    intro h
    simp only [MvPolynomial.aeval_eq_eval]
    linear_combination D.height₁ j * h₁ j h)

end QuadraticLiftParameters
end IdealGeneration.QuadraticElimination
