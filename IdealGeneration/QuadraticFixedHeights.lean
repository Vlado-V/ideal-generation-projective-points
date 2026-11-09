module

public import IdealGeneration.QuadraticFlagFamily

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The fixed core heights already give full rank in every untouched pair. -/

noncomputable section
namespace IdealGeneration.QuadraticFlagFamily
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticLayerJacobian
open QuadraticElimination.QuadraticLiftParameters

variable {K P J : Type*} [Field K] [Fintype P]

private theorem sum_only_pair (p₀ : P) (f : P × Bool → K)
    (h : ∀ i, i.1 ≠ p₀ → f i = 0) :
    (∑ i, f i) = f (p₀, false) + f (p₀, true) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p₀]
  · simp only [Fintype.sum_bool, add_comm]
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro b _
    exact h (p,b) hp
  · simp

omit [Fintype P] in
private theorem pairPoint_apply [DecidableEq P] (p q : P) (b : Bool) :
    pairPoint (K := K) p (q,b) = if q = p then 1 else 0 := by
  classical
  cases b <;> simp [pairPoint, coordinatePoint]

private theorem pairedBaseValue_eq (D : QuadraticLiftParameters K P J) (k : Fin 3) :
    D.pairedBaseValue k = D.baseCoefficient k (D.distinguishedPair,false) +
      D.baseCoefficient k (D.distinguishedPair,true) := by
  classical
  rw [pairedBaseValue, sum_only_pair D.distinguishedPair]
  · simp [pairPoint_apply]
  · intro i hi
    rcases i with ⟨p,b⟩
    simp [pairPoint_apply, hi]

private theorem offsetFirst_eq (D : QuadraticLiftParameters K P J) (r : Fin 2) (j : J) :
    D.offsetFirst r j = D.baseWeight r (D.distinguishedPair,false) *
        D.firstCorrection (D.distinguishedPair,false) j +
      D.baseWeight r (D.distinguishedPair,true) * D.firstCorrection (D.distinguishedPair,true) j := by
  simp only [offsetFirst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply sum_only_pair
  intro i hi
  have hz : D.firstCorrection i j = 0 := congrArg Prod.fst
    (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair D.normal₀ D.normal₁ i j hi)
  simp [hz]

private theorem offsetSecond_eq (D : QuadraticLiftParameters K P J) (r : Fin 2) (j : J) :
    D.offsetSecond r j = D.baseWeight r (D.distinguishedPair,false) *
        D.secondCorrection (D.distinguishedPair,false) j +
      D.baseWeight r (D.distinguishedPair,true) * D.secondCorrection (D.distinguishedPair,true) j := by
  simp only [offsetSecond, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply sum_only_pair
  intro i hi
  have hz : D.secondCorrection i j = 0 := congrArg Prod.snd
    (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair D.normal₀ D.normal₁ i j hi)
  simp [hz]

variable (K) [CharZero K] [DecidableEq J]
variable (p₀ : P) (layers : Bool → J) (hle : layers false ≠ layers true)

local notation "D" => parameters K p₀ layers

private theorem pairedBaseValue_fixed (k : Fin 3) :
    (D).pairedBaseValue k = (![5, -3, 2] : Fin 3 → K) k := by
  rw [pairedBaseValue_eq]
  fin_cases k <;> norm_num [baseCoefficient, parameters, naturalSlope,
    baseOrder_distinguished, normalBasisValue]

include hle in
private theorem coreCorrection_fixed (b j : Bool) :
    ((D).firstCorrection (p₀,b) (layers j), (D).secondCorrection (p₀,b) (layers j)) =
      if j then (if b then (27,-9) else (15,-5)) else
        (if b then (5,-5) else (3,-3)) := by
  classical
  cases j <;> cases b <;>
    norm_num [firstCorrection, secondCorrection, layerCorrection, normalCorrection,
      pairPoint_apply, parameters, naturalSlope, baseOrder_distinguished, hle]

include hle in
private theorem layerCoefficients_fixed (k : Fin 3) (j : Bool) :
    (D).layerCoefficients k (layers j) =
      if j then (![ (65,-22), (-12,3), (132,-47)] : Fin 3 → K × K) k
      else (![ (10,-11), (-4,3), (10,-11)] : Fin 3 → K × K) k := by
  rw [layerCoefficients, pairedBaseValue_fixed K p₀ layers]
  cases j <;> fin_cases k <;> norm_num [parameters, solveLayerNormal, normalBasisValue, hle]

include hle in
private theorem clearingOffset_fixed (r : Fin 2) (j : Bool) :
    (D).clearingOffset r (layers j) =
      if j then (![ (69,-23), (-42,14)] : Fin 2 → K × K) r
      else (![ (13,-13), (-8,8)] : Fin 2 → K × K) r := by
  have hc₀ := coreCorrection_fixed K p₀ layers hle false j
  have hc₁ := coreCorrection_fixed K p₀ layers hle true j
  have h₀₀ := congrArg Prod.fst hc₀
  have h₀₁ := congrArg Prod.fst hc₁
  have h₁₀ := congrArg Prod.snd hc₀
  have h₁₁ := congrArg Prod.snd hc₁
  dsimp only at h₀₀ h₀₁ h₁₀ h₁₁
  rw [clearingOffset, offsetFirst_eq, offsetSecond_eq,
    show (D).distinguishedPair = p₀ from rfl, h₀₀, h₀₁, h₁₀, h₁₁]
  cases j <;> fin_cases r <;>
    norm_num [baseWeight, parameters, naturalSlope, baseOrder_distinguished]

/-- The common scalar factor of each selected layer row. -/
def slopeFactor {F : Type*} [Field F] (c : F) (j : Bool) : F :=
  if j then (3*c+1)*(4*c+1) else (2*c+1)*(c+1)

/-- The two fixed-height rows after projecting along the original direction. -/
def fixedGammaRow {F : Type*} [Field F] (c c' : F) (j : Bool) : F × F :=
  (slopeFactor c j / (c'-c)) • (if j then (-1,11) else (-2,5))

include hle in
theorem gammaPair_fixed (i : P × Bool) (j : Bool) :
    (D).gammaPair i (layers j) = fixedGammaRow ((D).slope i) ((D).slope (partner i)) j := by
  have hF (r : Fin 2) := congrArg Prod.fst (clearingOffset_fixed K p₀ layers hle r j)
  have hS (r : Fin 2) := congrArg Prod.snd (clearingOffset_fixed K p₀ layers hle r j)
  dsimp only [clearingOffset] at hF hS
  cases j <;> apply Prod.ext <;>
    norm_num [gammaPair, pairGamma, clearedFirst, clearedSecond, combinedFirst, combinedSecond,
      layerCoefficients_fixed K p₀ layers hle, hF, hS, fixedGammaRow, slopeFactor,
      div_eq_mul_inv, smul_eq_mul] <;> ring

private theorem slopeFactor_ne (i : P × Bool) (j : Bool) : slopeFactor ((D).slope i) j ≠ 0 := by
  have hm (m : ℕ) : (m : K) * (D).slope i + 1 ≠ 0 := by
    change (m : K) * (naturalSlope p₀ i : K) + 1 ≠ 0
    exact_mod_cast (show m * naturalSlope p₀ i + 1 ≠ 0 by omega)
  cases j
  · exact mul_ne_zero (by simpa using hm 2) (by simpa using hm 1)
  · exact mul_ne_zero (by simpa using hm 3) (by simpa using hm 4)

private theorem slopeDifference_ne (i : P × Bool) : (D).slope (partner i) - (D).slope i ≠ 0 :=
  sub_ne_zero.mpr fun h => partner_ne i (parameters_slope_injective K p₀ layers h)

include hle in
/-- The untouched two-layer evaluation matrices are nonsingular at the
same fixed heights that give the six-point core certificate. -/
theorem gammaPair_fixed_det_ne (i : P × Bool) :
    normalDet ((D).gammaPair i (layers false)) ((D).gammaPair i (layers true)) ≠ 0 := by
  rw [gammaPair_fixed K p₀ layers hle i false, gammaPair_fixed K p₀ layers hle i true]
  let c := (D).slope i
  let c' := (D).slope (partner i)
  have hdet : normalDet (fixedGammaRow c c' false) (fixedGammaRow c c' true) =
      (-17 : K) * (slopeFactor c false / (c'-c)) * (slopeFactor c true / (c'-c)) := by
    simp [normalDet, fixedGammaRow, smul_eq_mul]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (div_ne_zero (slopeFactor_ne K p₀ layers i false) (slopeDifference_ne K p₀ layers i)))
    (div_ne_zero (slopeFactor_ne K p₀ layers i true) (slopeDifference_ne K p₀ layers i))

include hle in
/-- The first layer already detects the `t` multiplier at the injective endpoint. -/
theorem gamma_t_firstLayer_ne (i : P × Bool) : (D).pairGamma i 1 (layers false) ≠ 0 := by
  have h := congrArg Prod.snd (gammaPair_fixed K p₀ layers hle i false)
  change (D).pairGamma i 1 (layers false) =
    (slopeFactor ((D).slope i) false / ((D).slope (partner i)-(D).slope i)) * 5 at h
  rw [h]
  exact mul_ne_zero (div_ne_zero (slopeFactor_ne K p₀ layers i false)
    (slopeDifference_ne K p₀ layers i)) (by norm_num)

include hle in
/-- The coefficient of the first layer in `U₃` detects the last pure-normal parameter. -/
theorem thirdLift_firstLayer_ne : ((D).layerCoefficients (2 : Fin 3) (layers false)).1 ≠ 0 := by
  rw [layerCoefficients_fixed K p₀ layers hle 2 false]
  norm_num

end IdealGeneration.QuadraticFlagFamily
