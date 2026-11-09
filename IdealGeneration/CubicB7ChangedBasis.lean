module

public import IdealGeneration.CubicB7Basis
public import IdealGeneration.CubicMarkedBlock
public import IdealGeneration.CubicB22Higher
public import IdealGeneration.CubicColumnCorrection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The star column changes preserve the actual new source basis. -/

noncomputable section
namespace IdealGeneration.CubicSupported.Compatible

open Parameters MvPolynomial B5 B22 Module

variable {K : Type*} [Field K] {m f : ℕ}
variable {P : Parameters K m} {Q : Parameters K (m + 2)} (h : Compatible P Q)
variable (hP : ∀ e, P.single e = B5.single e) (hQ : ∀ e, Q.single e = B5.single e)
variable (free : Fin f → Fin m → K)
variable (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- Old injectivity detects membership in the new source from the literal old-space vanishing. -/
theorem mem_restrictParameters_ker_of_phi_eval_zero
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (x : Q.EliminatedParameters)
    (hx : ∀ (y : Fin m → K) (k : Fin 2), eval (extendTrace y)
      (Q.parameterPhi (fun i : Fin 0 => i.elim0) h₂ h₆ x k).val = 0) :
    x ∈ h.restrictParameters.ker := by
  apply LinearMap.mem_ker.mpr
  apply hold
  rw [(P.markedEvaluation free h₂ h₆).map_zero]
  apply Prod.ext
  · funext b
    rw [P.markedEvaluation_singleEdge, ← h.parameterPhi_eval_extendTrace free (fun i : Fin 0 => i.elim0) h₂ h₆, hx]
    simp
  · funext i k
    rw [P.markedEvaluation_free, ← h.parameterPhi_eval_extendTrace free (fun i : Fin 0 => i.elim0) h₂ h₆, hx]
    rfl

/-- Every actual lower column belongs to the kernel of the old restriction. -/
theorem b7Parameter_mem_new (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (c : B7Column m) : b7Parameter Q hQ c ∈ h.restrictParameters.ker := by
  apply h.mem_restrictParameters_ker_of_phi_eval_zero free h₂ h₆ hold
  intro y k
  rw [parameterPhi_b7Parameter, map_mul, eval_X, extendTrace_new, zero_mul]

/-- Every actual higher column belongs to the kernel of the old restriction. -/
theorem highParameter_mem_new (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (c : HigherColumn Q) : highParameter Q c ∈ h.restrictParameters.ker := by
  apply h.mem_restrictParameters_ker_of_phi_eval_zero free h₂ h₆ hold
  intro y k
  rw [← movingEvaluation_coeff_zero y (0 : Fin 2 → K), higherPolynomial_parameterPhi,
    movingEvaluation_higherPolynomial_coeff_zero]

private def changedIndex : B7Column m ⊕ HigherColumn Q → Bool
  | .inl (.extra ..) => true
  | .inl (.remaining ..) => true
  | _ => false

/-- The adjusted source column, with its actual membership in the new source. -/
def actualNewColumn (hold : Function.Injective (P.markedEvaluation free h₂ h₆)) :
    B7Column m ⊕ HigherColumn Q → h.restrictParameters.ker
  | .inl c => ⟨b7Parameter Q hQ c, h.b7Parameter_mem_new hQ free h₂ h₆ hold c⟩
  | .inr c => ⟨highParameter Q c, h.highParameter_mem_new free h₂ h₆ hold c⟩

open Classical in
private theorem scalar_singleEdgeParameter (i : Fin (m + 2)) (e : Q.SingleEdge)
    (j : Q.ParameterIndex) :
    Q.parameterScalar (Q.singleEdgeParameter i e) j =
      if j = .edgeTensor i e then 1 else 0 := by
  cases j with
  | pure q => simp [parameterScalar, singleEdgeParameter]
  | mixed u j q => fin_cases u <;> simp [parameterScalar, normalPairAt, singleEdgeParameter]
  | normalEdge u a => fin_cases u <;> simp [parameterScalar, normalPairAt, singleEdgeParameter, freeCoefficients]
  | antisymmetric a q => simp [parameterScalar, singleEdgeParameter]
  | edgeTensor j a =>
      by_cases hji : j = i <;> by_cases hae : a = e <;>
        simp [parameterScalar, singleEdgeParameter, hji, hae]

open Classical in
private theorem scalar_mixedEdgeParameter (e : Edge (m + 2)) (q : Fin 3)
    (j : Q.ParameterIndex) :
    Q.parameterScalar (Q.mixedEdgeParameter e (normalBasis q)) j =
      if j = .antisymmetric e q then 1 else 0 := by
  cases j with
  | pure j => simp [parameterScalar, mixedEdgeParameter]
  | mixed u j r => fin_cases u <;> simp [parameterScalar, normalPairAt, mixedEdgeParameter]
  | normalEdge u a => fin_cases u <;> simp [parameterScalar, normalPairAt, mixedEdgeParameter, freeCoefficients]
  | antisymmetric a r =>
      by_cases hae : a = e <;> by_cases hrq : r = q <;>
        simp [parameterScalar, mixedEdgeParameter, normalBasis, hae, hrq]
  | edgeTensor i a => simp [parameterScalar, mixedEdgeParameter]


private theorem normalPairAt_starParameter (u v : Fin 2) (F : Q.coefficientKernel)
    (hC : F.val.1 = 0) (w : Fin (m + 2)) (a : Fin (m + 2) → Fin 2 → K) :
    Q.normalPairAt (Q.starParameter u F hC w a).1 v = if v = u then -F else 0 := by
  fin_cases u <;> fin_cases v <;> simp [normalPairAt, starParameter, starNormalPair]

private theorem normalPairAt_edgeStarParameter (u v : Fin 2) (e : Q.SingleEdge)
    (i w : Fin (m + 2)) :
    Q.normalPairAt (Q.edgeStarParameter u e i w).1 v = if v = u then -Q.edgeCubic e else 0 :=
  normalPairAt_starParameter u v (Q.edgeCubic e) rfl w _

private theorem normalPairAt_mixedStarParameter (u v : Fin 2) (w : Fin (m + 2)) (q : Fin 3) :
    Q.normalPairAt (Q.mixedStarParameter u w (normalBasis q)).1 v =
      if v = u then -Q.mixedCubic w (normalBasis q) else 0 :=
  normalPairAt_starParameter u v (Q.mixedCubic w (normalBasis q)) rfl w _

private theorem freeCoefficients_lift_apply (C₀ : Fin 4 → K)
    (A : Fin (m + 2) → Fin 3 → K) (z : Q.SingleEdge → K) (e : Q.SingleEdge) :
    Q.freeCoefficients (Q.coefficientLift C₀ A z) e = z e := by
  exact congrArg (fun w : (Fin 4 → K) × (Fin (m + 2) → Fin 3 → K) × (Q.SingleEdge → K) =>
    w.2.2 e) (Q.kernelCoordinatesEquiv_coefficientLift C₀ A z)

private theorem freeCoefficients_neg_apply (F : Q.coefficientKernel) (e : Q.SingleEdge) :
    Q.freeCoefficients (-F) e = -Q.freeCoefficients F e := rfl

private theorem freeCoefficients_zero_apply (e : Q.SingleEdge) :
    Q.freeCoefficients (0 : Q.coefficientKernel) e = 0 := neg_zero

open Classical in
private theorem scalar_normalEdge_edgeStar (u v : Fin 2) (e a : Q.SingleEdge)
    (i w : Fin (m + 2)) :
    Q.parameterScalar (Q.edgeStarParameter u e i w) (.normalEdge v a) =
      if ParameterIndex.normalEdge v a = ParameterIndex.normalEdge u e then -1 else 0 := by
  simp only [parameterScalar, normalPairAt_edgeStarParameter]
  by_cases hv : v = u <;> by_cases hae : a = e <;>
    simp [hv, hae, freeCoefficients_neg_apply, freeCoefficients_zero_apply, edgeCubic,
      freeCoefficients_lift_apply]

private theorem scalar_mixed_edgeStar (u v : Fin 2) (e : Q.SingleEdge)
    (i w j : Fin (m + 2)) (q : Fin 3) :
    Q.parameterScalar (Q.edgeStarParameter u e i w) (.mixed v j q) = 0 := by
  simp only [parameterScalar, normalPairAt_edgeStarParameter]
  by_cases hv : v = u <;> simp [hv, edgeCubic, coefficientLift]

private theorem scalar_normalEdge_mixedStar (u v : Fin 2) (a : Q.SingleEdge)
    (w : Fin (m + 2)) (q : Fin 3) :
    Q.parameterScalar (Q.mixedStarParameter u w (normalBasis q)) (.normalEdge v a) = 0 := by
  simp only [parameterScalar, normalPairAt_mixedStarParameter]
  by_cases hv : v = u <;>
    simp [hv, freeCoefficients_neg_apply, freeCoefficients_zero_apply, mixedCubic, freeCoefficients_lift_apply]

open Classical in
private theorem scalar_mixed_mixedStar (u v : Fin 2) (w j : Fin (m + 2)) (q r : Fin 3) :
    Q.parameterScalar (Q.mixedStarParameter u w (normalBasis q)) (.mixed v j r) =
      if ParameterIndex.mixed (P := Q) v j r = .mixed u w q then -1 else 0 := by
  simp only [parameterScalar, normalPairAt_mixedStarParameter]
  by_cases hv : v = u <;> by_cases hj : j = w <;> by_cases hr : r = q <;>
    simp [hv, hj, hr, mixedCubic, mixedArray, coefficientLift, normalBasis]


open Classical in
private theorem newIndexMap_val_eq_iff (hpair : Q.single (newPairEdge m) = false)
    (a b : B7Column m ⊕ HigherColumn Q) :
    (h.newIndexMap hP hQ a).val = (h.newIndexMap hP hQ b).val ↔ a = b := by
  constructor
  · intro he
    exact (h.newIndexEquiv hP hQ hpair).injective (Subtype.ext he)
  · rintro rfl
    rfl

open Classical in
private theorem actualNewColumn_unchanged (hpair : Q.single (newPairEdge m) = false)
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (j : B7Column m ⊕ HigherColumn Q) (hj : changedIndex j = false) :
    (fun i => Q.parameterScalar (h.actualNewColumn hQ free h₂ h₆ hold j).val
      (h.newIndexMap hP hQ i).val) = Pi.single j 1 := by
  funext i
  rw [Pi.single_apply]
  trans (if (h.newIndexMap hP hQ i).val = (h.newIndexMap hP hQ j).val then 1 else 0)
  · rcases j with (⟨b, e | ⟨c, d⟩⟩ | ⟨b, c, q⟩ | ⟨b, c, u⟩ | ⟨b, u, q⟩) | (⟨p, b⟩ | q)
    · exact scalar_singleEdgeParameter _ _ _
    · exact scalar_singleEdgeParameter _ _ _
    · exact scalar_mixedEdgeParameter _ _ _
    · simp [changedIndex] at hj
    · simp [changedIndex] at hj
    · exact scalar_singleEdgeParameter _ _ _
    · exact scalar_mixedEdgeParameter _ _ _
  · simp [h.newIndexMap_val_eq_iff hP hQ hpair]

open Classical in
private theorem actualNewColumn_changed (hpair : Q.single (newPairEdge m) = false)
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (i : B7Column m ⊕ HigherColumn Q) (hi : changedIndex i = true)
    (j : B7Column m ⊕ HigherColumn Q) :
    Q.parameterScalar (h.actualNewColumn hQ free h₂ h₆ hold j).val
      (h.newIndexMap hP hQ i).val = if j = i then -1 else 0 := by
  trans (if (h.newIndexMap hP hQ i).val = (h.newIndexMap hP hQ j).val then -1 else 0)
  · rcases i with (⟨b, c⟩ | ⟨b, c, q⟩ | ⟨b, c, u⟩ | ⟨b, u, q⟩) | i
    · simp [changedIndex] at hi
    · simp [changedIndex] at hi
    · rcases j with (⟨b', e | ⟨c', d'⟩⟩ | ⟨b', c', q'⟩ | ⟨b', c', u'⟩ | ⟨b', u', q'⟩) |
          (⟨p', b'⟩ | q')
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_mixedEdgeParameter]
      · exact scalar_normalEdge_edgeStar _ _ _ _ _ _
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_normalEdge_mixedStar]
      · simp [actualNewColumn, highParameter, newIndexMap, lowerNewIndex, lowerIndex, higherNewIndex,
          higherIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, highParameter, newIndexMap, lowerNewIndex, lowerIndex, higherNewIndex,
          higherIndex, show (basisQuadratic q' : Fin 3 → K) = normalBasis q' from rfl,
          scalar_mixedEdgeParameter]
    · rcases j with (⟨b', e | ⟨c', d'⟩⟩ | ⟨b', c', q'⟩ | ⟨b', c', u'⟩ | ⟨b', u', q'⟩) |
          (⟨p', b'⟩ | q')
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_mixedEdgeParameter]
      · simp [actualNewColumn, b7Parameter, newIndexMap, lowerNewIndex, lowerIndex, scalar_mixed_edgeStar]
      · exact scalar_mixed_mixedStar _ _ _ _ _ _
      · simp [actualNewColumn, highParameter, newIndexMap, lowerNewIndex, lowerIndex, higherNewIndex,
          higherIndex, scalar_singleEdgeParameter]
      · simp [actualNewColumn, highParameter, newIndexMap, lowerNewIndex, lowerIndex, higherNewIndex,
          higherIndex, show (basisQuadratic q' : Fin 3 → K) = normalBasis q' from rfl,
          scalar_mixedEdgeParameter]
    · simp [changedIndex] at hi
  · by_cases he : j = i
    · subst j
      simp
    · have hn : (h.newIndexMap hP hQ i).val ≠ (h.newIndexMap hP hQ j).val :=
        fun he' => he ((h.newIndexMap_val_eq_iff hP hQ hpair i j).mp he').symm
      simp [he, hn]

private theorem parameterIndex_finite : Finite Q.ParameterIndex := by
  let encode : Q.ParameterIndex →
      (Fin 3 ⊕ ((Fin 2 × Fin (m + 2) × Fin 3) ⊕ ((Fin 2 × Q.SingleEdge) ⊕
        ((Edge (m + 2) × Fin 3) ⊕ (Fin (m + 2) × Q.SingleEdge))))) :=
    fun i => match i with
    | .pure q => .inl q
    | .mixed u j q => .inr (.inl (u, j, q))
    | .normalEdge u e => .inr (.inr (.inl (u, e)))
    | .antisymmetric e q => .inr (.inr (.inr (.inl (e, q))))
    | .edgeTensor i e => .inr (.inr (.inr (.inr (i, e))))
  apply Finite.of_injective encode
  intro i j he
  cases i <;> cases j <;> simp_all [encode]

/-- The actual lower and higher source vectors, after the star-column changes, form a basis. -/
def actualNewBasis (hpair : Q.single (newPairEdge m) = false)
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆)) :
    Basis (B7Column m ⊕ HigherColumn Q) K h.restrictParameters.ker := by
  classical
  let e := h.newIndexEquiv hP hQ hpair
  let _ : Finite Q.ParameterIndex := parameterIndex_finite
  let _ : Fintype h.NewParameterIndex := Fintype.ofFinite _
  let _ : Fintype (B7Column m ⊕ HigherColumn Q) := Fintype.ofEquiv _ e.symm
  let E := h.newParameterCoordinates.trans (LinearEquiv.funCongrLeft K K e)
  let v := fun i => E (h.actualNewColumn hQ free h₂ h₆ hold i)
  exact (correctedColumnBasis v changedIndex
    (h.actualNewColumn_unchanged hP hQ free h₂ h₆ hpair hold)
    (h.actualNewColumn_changed hP hQ free h₂ h₆ hpair hold)).map E.symm

@[simp] theorem actualNewBasis_apply (hpair : Q.single (newPairEdge m) = false)
    (hold : Function.Injective (P.markedEvaluation free h₂ h₆))
    (i : B7Column m ⊕ HigherColumn Q) :
    h.actualNewBasis hP hQ free h₂ h₆ hpair hold i =
      h.actualNewColumn hQ free h₂ h₆ hold i := by
  classical
  let e := h.newIndexEquiv hP hQ hpair
  let _ : Finite Q.ParameterIndex := parameterIndex_finite
  let _ : Fintype h.NewParameterIndex := Fintype.ofFinite _
  let _ : Fintype (B7Column m ⊕ HigherColumn Q) := Fintype.ofEquiv _ e.symm
  simp only [actualNewBasis, Basis.map_apply]
  apply (h.newParameterCoordinates.trans (LinearEquiv.funCongrLeft K K
    (h.newIndexEquiv hP hQ hpair))).injective
  rw [LinearEquiv.apply_symm_apply]
  exact correctedColumnBasis_apply _ _ _ _ _

end IdealGeneration.CubicSupported.Compatible
