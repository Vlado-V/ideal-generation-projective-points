module

public import IdealGeneration.CubicEliminatedCoordinates
public import IdealGeneration.CubicUpperBlockEquations
public import IdealGeneration.TripleNormalKernelStages

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The independent coordinates of the actual eliminated cubic source. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Parameters

open CubicMiddle CubicNormalExpansion CubicUpperSolve CubicUpperBlockEquations

variable {K : Type*} [Field K] {m f : ℕ} (P : Parameters K m)
variable (free : Fin f → Fin m → K) (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

local notation "Cₚ" => P.toConeConfiguration free
local notation "Eₚ" => P.residualCoefficientEquiv free h₂ h₆

/-- The pure normal cubic component of a supported kernel cubic. -/
def cubicTop : P.coefficientKernel →ₗ[K] (Fin 4 → K) where
  toFun u := u.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cubicTop_surjective : Function.Surjective P.cubicTop := by
  intro C
  exact ⟨P.coefficientLift C 0 0, rfl⟩

/-- Independent normal-pair, antisymmetric and single-edge coordinates in Lemma B.2. -/
abbrev EliminatedParameters :=
  Omega P.cubicTop × (Edge m → Fin 3 → K) × (Fin m → P.SingleEdge → K)

private abbrev sourceU (u : ResidualSource Cₚ) : P.coefficientKernel := Eₚ (u (Fin.castAdd m 0))
private abbrev sourceV (u : ResidualSource Cₚ) : P.coefficientKernel := Eₚ (u (Fin.castAdd m 1))
private abbrev sourceW (u : ResidualSource Cₚ) (i : Fin m) : P.coefficientKernel :=
  Eₚ (u (Fin.natAdd 2 i))

private theorem normalPair_mem_omega (u : eliminatedSource Cₚ) :
    (P.sourceU free h₂ h₆ u.val, P.sourceV free h₂ h₆ u.val) ∈ Omega P.cubicTop := by
  exact ((P.mem_eliminatedSource_iff_upper free h₂ h₆ u.val).mp u.property).1

/-- Recover the independent coordinates of an actual eliminated source. -/
def eliminatedParameterRead (u : eliminatedSource Cₚ) : P.EliminatedParameters :=
  let U := P.sourceU free h₂ h₆ u.val
  let V := P.sourceV free h₂ h₆ u.val
  let W := P.sourceW free h₂ h₆ u.val
  let A := quadraticTarget U.val V.val
  (⟨(U, V), P.normalPair_mem_omega free h₂ h₆ u⟩,
    fun e a => (W e.val.1).val.2.1 e.val.2 a + (A e.val.1 e.val.2 a + A e.val.2 e.val.1 a) / 2,
    fun i => P.freeCoefficients (W i))

/-- The trace-multiplier cubic determined by the normal pair and the free arrays. -/
def parameterTraceCubic (x : P.EliminatedParameters) (i : Fin m) : P.coefficientKernel :=
  let U := x.1.val.1.val
  let V := x.1.val.2.val
  P.coefficientLift (cubicCorrection (U.2.1 i) (V.2.1 i))
    (symmetricCompletion (quadraticTarget U V) x.2.1 i) (x.2.2 i)

/-- Construct the actual residual source from the independent arrays. -/
def parameterResidualSource (x : P.EliminatedParameters) : ResidualSource Cₚ :=
  fun j => (Eₚ).symm (Fin.addCases ![x.1.val.1, x.1.val.2] (P.parameterTraceCubic x) j)

@[simp] private theorem sourceU_parameterResidualSource (x : P.EliminatedParameters) :
    P.sourceU free h₂ h₆ (P.parameterResidualSource free h₂ h₆ x) = x.1.val.1 := by
  simp [sourceU, parameterResidualSource]

@[simp] private theorem sourceV_parameterResidualSource (x : P.EliminatedParameters) :
    P.sourceV free h₂ h₆ (P.parameterResidualSource free h₂ h₆ x) = x.1.val.2 := by
  simp [sourceV, parameterResidualSource]

@[simp] private theorem sourceW_parameterResidualSource (x : P.EliminatedParameters) (i : Fin m) :
    P.sourceW free h₂ h₆ (P.parameterResidualSource free h₂ h₆ x) i = P.parameterTraceCubic x i := by
  simp [sourceW, parameterResidualSource]

private theorem coefficientSource_ext (u v : ResidualSource Cₚ)
    (hU : P.sourceU free h₂ h₆ u = P.sourceU free h₂ h₆ v)
    (hV : P.sourceV free h₂ h₆ u = P.sourceV free h₂ h₆ v)
    (hW : P.sourceW free h₂ h₆ u = P.sourceW free h₂ h₆ v) : u = v := by
  funext i
  apply (Eₚ).injective
  refine Fin.addCases (fun j => ?_) (fun j => congrFun hW j) i
  fin_cases j
  · exact hU
  · exact hV

private theorem coefficientLift_free (C : Fin 4 → K) (B : Fin m → Fin 3 → K)
    (z : P.SingleEdge → K) : P.freeCoefficients (P.coefficientLift C B z) = z := by
  funext e
  change -P.offDiagonalLift C B z e.val 1 = z e
  simp [offDiagonalLift, e.property]

private theorem coefficientLift_eq (u : P.coefficientKernel) :
    P.coefficientLift u.val.1 u.val.2.1 (P.freeCoefficients u) = u := by
  apply Subtype.ext
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext
    (P.kernel_diagonal_eq u).symm (P.kernel_offDiagonal_eq u).symm))

private theorem symmetricCompletion_read (A : Fin m → Fin m → Fin 3 → K)
    (z : Edge m → Fin 3 → K) (e : Edge m) (a : Fin 3) :
    symmetricCompletion A z e.val.1 e.val.2 a + (A e.val.1 e.val.2 a + A e.val.2 e.val.1 a) / 2 =
      z e a := by
  simp [symmetricCompletion, antisymmetric, e.property]


private theorem parameterResidualSource_mem (x : P.EliminatedParameters) :
    P.parameterResidualSource free h₂ h₆ x ∈ eliminatedSource Cₚ := by
  apply (P.mem_eliminatedSource_iff_upper free h₂ h₆ _).mpr
  change productNormal4 (P.sourceU free h₂ h₆ _).val (P.sourceV free h₂ h₆ _).val = 0 ∧
    productNormal3 (P.sourceU free h₂ h₆ _).val (P.sourceV free h₂ h₆ _).val
      (fun i => (P.sourceW free h₂ h₆ _ i).val) = 0 ∧
    productNormal2 (P.sourceU free h₂ h₆ _).val (P.sourceV free h₂ h₆ _).val
      (fun i => (P.sourceW free h₂ h₆ _ i).val) = 0
  simp only [sourceU_parameterResidualSource, sourceV_parameterResidualSource,
    sourceW_parameterResidualSource]
  exact ⟨x.1.property, (productNormal3_eq_zero_iff _ _ _).mpr (fun _ => rfl),
    (productNormal2_eq_zero_iff h₂ _ _ _).mpr ⟨x.2.1, rfl⟩⟩

/-- Assemble the unique eliminated residual source with the prescribed independent parameters. -/
def parameterEliminatedSource (x : P.EliminatedParameters) : eliminatedSource Cₚ :=
  ⟨P.parameterResidualSource free h₂ h₆ x, P.parameterResidualSource_mem free h₂ h₆ x⟩

private theorem eliminatedParameterRead_parameterEliminatedSource (x : P.EliminatedParameters) :
    P.eliminatedParameterRead free h₂ h₆ (P.parameterEliminatedSource free h₂ h₆ x) = x := by
  unfold eliminatedParameterRead parameterEliminatedSource
  dsimp only
  simp only [sourceU_parameterResidualSource, sourceV_parameterResidualSource,
    sourceW_parameterResidualSource]
  refine Prod.ext (Subtype.ext rfl) (Prod.ext ?_ ?_)
  · funext e a
    exact symmetricCompletion_read _ _ e a
  · funext i
    exact P.coefficientLift_free _ _ _

private theorem parameterEliminatedSource_eliminatedParameterRead (u : eliminatedSource Cₚ) :
    P.parameterEliminatedSource free h₂ h₆ (P.eliminatedParameterRead free h₂ h₆ u) = u := by
  apply Subtype.ext
  apply P.coefficientSource_ext free h₂ h₆
  · exact P.sourceU_parameterResidualSource free h₂ h₆ _
  · exact P.sourceV_parameterResidualSource free h₂ h₆ _
  · funext i
    change P.sourceW free h₂ h₆
      (P.parameterResidualSource free h₂ h₆ (P.eliminatedParameterRead free h₂ h₆ u)) i = _
    rw [sourceW_parameterResidualSource]
    let U := P.sourceU free h₂ h₆ u.val
    let V := P.sourceV free h₂ h₆ u.val
    let W := P.sourceW free h₂ h₆ u.val
    have hupper := (P.mem_eliminatedSource_iff_upper free h₂ h₆ u.val).mp u.property
    obtain ⟨_, h3, h2⟩ := hupper
    change productNormal3 U.val V.val (fun i => (W i).val) = 0 at h3
    change productNormal2 U.val V.val (fun i => (W i).val) = 0 at h2
    have hC := (productNormal3_eq_zero_iff _ _ _).mp h3
    obtain ⟨z, hz⟩ := (productNormal2_eq_zero_iff h₂ _ _ _).mp h2
    let A := quadraticTarget U.val V.val
    have hz_read :
        (fun (e : Edge m) a => (W e.val.1).val.2.1 e.val.2 a +
          (A e.val.1 e.val.2 a + A e.val.2 e.val.1 a) / 2) = z := by
      funext e a
      rw [congrFun (congrFun (congrFun hz e.val.1) e.val.2) a]
      exact symmetricCompletion_read A z e a
    change P.coefficientLift (cubicCorrection (U.val.2.1 i) (V.val.2.1 i))
      (symmetricCompletion A (fun e a => (W e.val.1).val.2.1 e.val.2 a +
        (A e.val.1 e.val.2 a + A e.val.2 e.val.1 a) / 2) i) (P.freeCoefficients (W i)) = W i
    rw [hz_read, ← congrFun hz i, ← hC i]
    exact P.coefficientLift_eq (W i)

/-- Lemma B.2's parameter space is linearly equivalent to the actual eliminated source. -/
def eliminatedParametersEquiv : eliminatedSource Cₚ ≃ₗ[K] P.EliminatedParameters where
  toFun := P.eliminatedParameterRead free h₂ h₆
  invFun := P.parameterEliminatedSource free h₂ h₆
  left_inv := P.parameterEliminatedSource_eliminatedParameterRead free h₂ h₆
  right_inv := P.eliminatedParameterRead_parameterEliminatedSource free h₂ h₆
  map_add' u v := by
    unfold eliminatedParameterRead
    dsimp only [sourceU, sourceV, sourceW]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · apply Prod.ext <;> exact map_add (Eₚ) _ _
    · funext e a
      simp only [Submodule.coe_add, Pi.add_apply, map_add, Prod.snd_add, Prod.fst_add]
      rw [quadraticTarget_add]
      simp only [Pi.add_apply]
      ring
    · funext i e
      simp only [Submodule.coe_add, Pi.add_apply, map_add, Prod.snd_add, freeCoefficients]
      ring
  map_smul' r u := by
    unfold eliminatedParameterRead
    dsimp only [sourceU, sourceV, sourceW]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · apply Prod.ext <;> exact map_smul (Eₚ) _ _
    · funext e a
      simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Prod.smul_snd,
        Prod.smul_fst, smul_eq_mul]
      rw [quadraticTarget_smul]
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · funext i e
      simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Prod.smul_snd,
        freeCoefficients, smul_eq_mul, RingHom.id_apply]
      ring

/-- The `Φ` column associated to an independent parameter array. -/
def parameterPhi : P.EliminatedParameters →ₗ[K] (Fin 2 → Forms K m 3) :=
  (phi Cₚ).comp (P.eliminatedParametersEquiv free h₂ h₆).symm.toLinearMap

/-- The explicit trace cubic formula in Lemma B.2 represents actual multiplication. -/
theorem parameterPhi_polynomial (x : P.EliminatedParameters) (k : Fin 2) :
    (P.parameterPhi free h₂ h₆ x k).val =
      productNormal1 (fun i => (P.parameterTraceCubic x i).val) k := by
  change (phi Cₚ (P.parameterEliminatedSource free h₂ h₆ x) k).val = _
  rw [P.phi_eq_productNormal1 free h₂ h₆]
  congr 1
  funext i
  exact congrArg Subtype.val (P.sourceW_parameterResidualSource free h₂ h₆ x i)

/-- The allowed evaluation written in the explicit parameter coordinates. -/
def parameterEvaluation (hheight : ∀ i, (Cₚ).height i ≠ 0) :
    P.EliminatedParameters →ₗ[K] allowedValues Cₚ :=
  (allowedEvaluation Cₚ hheight).comp (P.eliminatedParametersEquiv free h₂ h₆).symm.toLinearMap

/-- The explicit source coordinates have the dimension stated in B.4. -/
theorem finrank_eliminatedParameters :
    Module.finrank K P.EliminatedParameters =
      (2 * (4 + 3 * m + Fintype.card P.SingleEdge) - 5) +
        3 * Fintype.card (Edge m) + m * Fintype.card P.SingleEdge := by
  let _ : FiniteDimensional K P.coefficientKernel :=
    FiniteDimensional.finiteDimensional_submodule _
  have : Module.Free K (Omega P.cubicTop) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (Omega P.cubicTop)
  change Module.finrank K (Omega P.cubicTop × (Edge m → Fin 3 → K) ×
    (Fin m → P.SingleEdge → K)) = _
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_omega P.cubicTop P.cubicTop_surjective, P.finrank_coefficientKernel]
  simp [Module.finrank_pi_fintype, Nat.mul_comm, Nat.add_assoc]


/-- The kernel in the actual middle map is the kernel of the explicit parameter evaluation. -/
def middleKernelParameterEquiv (hheight : ∀ i, (Cₚ).height i ≠ 0) :
    ((Cₚ).middleMultiplication 3).ker ≃ₗ[K] (P.parameterEvaluation free h₂ h₆ hheight).ker :=
  (middleKernelAllowedEquiv Cₚ hheight).trans
    (let e := P.eliminatedParametersEquiv free h₂ h₆
    { toFun := fun u => ⟨e u.val, LinearMap.mem_ker.mpr (by
        change allowedEvaluation Cₚ hheight (e.symm (e u.val)) = 0
        rw [e.symm_apply_apply]
        exact LinearMap.mem_ker.mp u.property)⟩
      invFun := fun x => ⟨e.symm x.val, LinearMap.mem_ker.mp x.property⟩
      left_inv := fun u => Subtype.ext (e.symm_apply_apply u.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun u v => Subtype.ext (e.map_add u.val v.val)
      map_smul' := fun r u => Subtype.ext (e.map_smul r u.val) })

/-- Full column rank of the explicit evaluated matrix is enough for the actual middle map. -/
theorem middleMultiplication_injective_iff_parameterEvaluation
    (hheight : ∀ i, (Cₚ).height i ≠ 0) :
    Function.Injective ((Cₚ).middleMultiplication 3) ↔
      Function.Injective (P.parameterEvaluation free h₂ h₆ hheight) := by
  exact (linearMap_injective_iff_kernel_subsingleton ((Cₚ).middleMultiplication 3)).trans
    ((P.middleKernelParameterEquiv free h₂ h₆ hheight).toEquiv.subsingleton_congr.trans
      (linearMap_injective_iff_kernel_subsingleton
        (P.parameterEvaluation free h₂ h₆ hheight)).symm)

end IdealGeneration.CubicSupported.Parameters
