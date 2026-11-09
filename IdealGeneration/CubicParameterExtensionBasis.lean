module

public import IdealGeneration.CubicParameterRestriction
public import IdealGeneration.CubicParameterBasis
public import IdealGeneration.CubicPairExtensionLabels

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Old and new scalar coordinates of the actual supported cubic pair extension. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Compatible

open Parameters

variable {K : Type*} [Field K] {m : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)

/-- The old scalar labels inside the independent enlarged source. -/
def oldParameterIndex : P.ParameterIndex ↪ Q.ParameterIndex where
  toFun
    | .pure q => .pure q
    | .mixed u i q => .mixed u (Fin.castAdd 2 i) q
    | .normalEdge u e => .normalEdge u (h.singleEdge e)
    | .antisymmetric e q => .antisymmetric (oldEdge m e) q
    | .edgeTensor i e => .edgeTensor (Fin.castAdd 2 i) (h.singleEdge e)
  inj' := by
    intro i j he
    cases i <;> cases j <;> simp_all

/-- In scalar coordinates, actual restriction simply reads the old labels. -/
theorem parameterScalar_restrictParameters (x : Q.EliminatedParameters) (i : P.ParameterIndex) :
    P.parameterScalar (h.restrictParameters x) i = Q.parameterScalar x (h.oldParameterIndex i) := by
  cases i with
  | pure q => rfl
  | mixed u i q => fin_cases u <;> rfl
  | normalEdge u e => fin_cases u <;> rfl
  | antisymmetric e q => rfl
  | edgeTensor i e => rfl

/-- The independent labels that disappear on the old configuration. -/
abbrev NewParameterIndex := {i : Q.ParameterIndex // i ∉ Set.range h.oldParameterIndex}

open Classical in
private def extendNewArray (a : h.NewParameterIndex → K) (i : Q.ParameterIndex) : K :=
  if hi : i ∉ Set.range h.oldParameterIndex then a ⟨i, hi⟩ else 0

private theorem assembleNew_mem (a : h.NewParameterIndex → K) :
    Q.assembleParameters (h.extendNewArray a) ∈ h.restrictParameters.ker := by
  apply LinearMap.mem_ker.mpr
  apply P.parameterScalarEquiv.injective
  funext i
  change P.parameterScalar (h.restrictParameters (Q.assembleParameters (h.extendNewArray a))) i =
    (P.parameterScalarEquiv 0) i
  rw [parameterScalar_restrictParameters, Q.parameterScalar_assembleParameters, P.parameterScalarEquiv.map_zero]
  simp [extendNewArray]

/-- The new source is freely parametrized by the complementary scalar labels. -/
def newParameterCoordinates : h.restrictParameters.ker ≃ₗ[K] (h.NewParameterIndex → K) where
  toFun x i := Q.parameterScalar x.val i.val
  invFun a := ⟨Q.assembleParameters (h.extendNewArray a), h.assembleNew_mem a⟩
  left_inv x := by
    apply Subtype.ext
    apply Q.parameterScalarEquiv.injective
    funext i
    change Q.parameterScalar (Q.assembleParameters (h.extendNewArray _)) i =
      Q.parameterScalar x.val i
    rw [Q.parameterScalar_assembleParameters]
    by_cases hi : i ∉ Set.range h.oldParameterIndex
    · simp [extendNewArray, hi]
    · obtain ⟨j, rfl⟩ := not_not.mp hi
      rw [← h.parameterScalar_restrictParameters, LinearMap.mem_ker.mp x.property]
      change h.extendNewArray _ (h.oldParameterIndex j) = (P.parameterScalarEquiv 0) j
      rw [P.parameterScalarEquiv.map_zero]
      simp [extendNewArray]
  right_inv a := by
    funext i
    change Q.parameterScalar (Q.assembleParameters (h.extendNewArray a)) i.val = a i
    rw [Q.parameterScalar_assembleParameters]
    simp [extendNewArray, i.property]
  map_add' x y := by
    funext i
    exact congrFun (Q.parameterScalarEquiv.map_add x.val y.val) i.val
  map_smul' r x := by
    funext i
    exact congrFun (Q.parameterScalarEquiv.map_smul r x.val) i.val

/-- The new source basis column is the same scalar basis column of the enlarged source. -/
theorem parameterColumn_mem_new (i : h.NewParameterIndex) :
    Q.parameterColumn i.val ∈ h.restrictParameters.ker := by
  classical
  apply LinearMap.mem_ker.mpr
  apply P.parameterScalarEquiv.injective
  funext j
  change P.parameterScalar (h.restrictParameters (Q.parameterColumn i.val)) j =
    (P.parameterScalarEquiv 0) j
  rw [parameterScalar_restrictParameters, Q.parameterScalar_parameterColumn, P.parameterScalarEquiv.map_zero]
  have hn : h.oldParameterIndex j ≠ i.val := fun e => i.property ⟨j, e⟩
  simp [hn]

end IdealGeneration.CubicSupported.Compatible
