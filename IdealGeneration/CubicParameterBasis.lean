module

public import IdealGeneration.CubicExplicitSource
public import IdealGeneration.CubicLiftDecomposition
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Scalar basis labels for the independent cubic source coordinates. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open CubicUpperSolve

variable {K : Type*} [Field K] {m : ℕ} (P : Parameters K m)

/-- The independent scalar parameters of the eliminated source. -/
inductive ParameterIndex
  | pure (q : Fin 3)
  | mixed (u : Fin 2) (i : Fin m) (q : Fin 3)
  | normalEdge (u : Fin 2) (e : P.SingleEdge)
  | antisymmetric (e : Edge m) (q : Fin 3)
  | edgeTensor (i : Fin m) (e : P.SingleEdge)
  deriving Fintype

/-- Read either entry of the independent normal pair. -/
def normalPairAt (x : Omega P.cubicTop) (u : Fin 2) : P.coefficientKernel :=
  ![x.val.1, x.val.2] u

/-- The three free coefficients of the binary cubic pair in the normal quartic equation. -/
def purePair (a : Fin 3 → K) : Fin 2 → Fin 4 → K :=
  ![![0, a 0, a 1, a 2], ![-a 0, -a 1, -a 2, 0]]

private theorem normalQuarticMap_purePair (a : Fin 3 → K) :
    normalQuarticMap (purePair a 0, purePair a 1) = 0 := by
  funext q
  fin_cases q <;> simp [normalQuarticMap, purePair]

private theorem normalQuarticMap_purePair_complete (c d : Fin 4 → K)
    (h : normalQuarticMap (c, d) = 0) :
    (c, d) = (purePair (fun q => c q.succ) 0, purePair (fun q => c q.succ) 1) := by
  have hq (q : Fin 5) := congrFun h q
  apply Prod.ext
  · funext q
    fin_cases q
    · simpa [normalQuarticMap, purePair] using hq 0
    · rfl
    · rfl
    · rfl
  · have h1 : c 1 + d 0 = 0 := hq 1
    have h2 : c 2 + d 1 = 0 := hq 2
    have h3 : c 3 + d 2 = 0 := hq 3
    have h4 : d 3 = 0 := hq 4
    funext q
    fin_cases q
    · exact eq_neg_of_add_eq_zero_right h1
    · exact eq_neg_of_add_eq_zero_right h2
    · exact eq_neg_of_add_eq_zero_right h3
    · exact h4

/-- Read a scalar coordinate of the independent source. -/
def parameterScalar (x : P.EliminatedParameters) : P.ParameterIndex → K
  | .pure q => x.1.val.1.val.1 q.succ
  | .mixed u i q => (P.normalPairAt x.1 u).val.2.1 i q
  | .normalEdge u e => P.freeCoefficients (P.normalPairAt x.1 u) e
  | .antisymmetric e q => x.2.1 e q
  | .edgeTensor i e => x.2.2 i e

private def assembleNormalPair (a : P.ParameterIndex → K) : Omega P.cubicTop := by
  let L (u : Fin 2) := P.coefficientLift (purePair (fun q => a (.pure q)) u)
    (fun i q => a (.mixed u i q)) (fun e => a (.normalEdge u e))
  refine ⟨(L 0, L 1), ?_⟩
  change normalQuarticMap (purePair (fun q => a (.pure q)) 0, purePair (fun q => a (.pure q)) 1) = 0
  exact normalQuarticMap_purePair _

/-- Assemble independent parameters from their scalar coordinates. -/
def assembleParameters (a : P.ParameterIndex → K) : P.EliminatedParameters :=
  (P.assembleNormalPair a, fun e q => a (.antisymmetric e q), fun i e => a (.edgeTensor i e))

@[simp] theorem parameterScalar_assembleParameters (a : P.ParameterIndex → K) :
    P.parameterScalar (P.assembleParameters a) = a := by
  funext i
  cases i with
  | pure q =>
      fin_cases q <;> rfl
  | mixed u i q =>
      fin_cases u <;> rfl
  | normalEdge u e =>
      fin_cases u <;>
        simp [parameterScalar, assembleParameters, normalPairAt, assembleNormalPair,
          freeCoefficients, coefficientLift, offDiagonalLift, e.property]
  | antisymmetric e q => rfl
  | edgeTensor i e => rfl

@[simp] theorem assembleParameters_parameterScalar (x : P.EliminatedParameters) :
    P.assembleParameters (P.parameterScalar x) = x := by
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) rfl
  · apply P.kernelCoordinatesEquiv.injective
    have hC := congrArg Prod.fst (normalQuarticMap_purePair_complete _ _ x.1.property)
    change P.kernelCoordinatesEquiv (P.coefficientLift _ _ _) = _
    rw [P.kernelCoordinatesEquiv_coefficientLift]
    exact Prod.ext hC.symm rfl
  · apply P.kernelCoordinatesEquiv.injective
    have hC := congrArg Prod.snd (normalQuarticMap_purePair_complete _ _ x.1.property)
    change P.kernelCoordinatesEquiv (P.coefficientLift _ _ _) = _
    rw [P.kernelCoordinatesEquiv_coefficientLift]
    exact Prod.ext hC.symm rfl

/-- The scalar coordinates give a basis of the independent source without a rank assumption. -/
def parameterScalarEquiv : P.EliminatedParameters ≃ₗ[K] (P.ParameterIndex → K) where
  toFun := P.parameterScalar
  invFun := P.assembleParameters
  left_inv := P.assembleParameters_parameterScalar
  right_inv := P.parameterScalar_assembleParameters
  map_add' x y := by
    funext i
    cases i with
    | pure q => rfl
    | mixed u i q => fin_cases u <;> rfl
    | normalEdge u e =>
        fin_cases u <;> simp [parameterScalar, normalPairAt, freeCoefficients, add_comm]
    | antisymmetric e q => rfl
    | edgeTensor i e => rfl
  map_smul' r x := by
    funext i
    cases i with
    | pure q => rfl
    | mixed u i q => fin_cases u <;> rfl
    | normalEdge u e =>
        fin_cases u <;> simp [parameterScalar, normalPairAt, freeCoefficients, smul_eq_mul]
    | antisymmetric e q => rfl
    | edgeTensor i e => rfl

local instance : DecidableEq P.ParameterIndex := Classical.decEq _

/-- The basis vector for one scalar parameter. -/
def parameterColumn (i : P.ParameterIndex) : P.EliminatedParameters :=
  P.assembleParameters (fun j => if j = i then 1 else 0)

@[simp] theorem parameterScalar_parameterColumn (i j : P.ParameterIndex) :
    P.parameterScalar (P.parameterColumn i) j = if j = i then 1 else 0 := by
  rw [parameterColumn, P.parameterScalar_assembleParameters]

end IdealGeneration.CubicSupported.Parameters
