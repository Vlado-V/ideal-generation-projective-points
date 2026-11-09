module

public import IdealGeneration.TripleNormalInitialData
public import IdealGeneration.TripleNormalSupportedQuadrics

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The exact supported geometry of the A.4 initial configuration. -/

noncomputable section
namespace IdealGeneration.TripleNormalInitial
open TripleNormal TripleNormal.SupportedQuadrics MvPolynomial Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

def baseParameters (K : Type*) [Field K] : Fin 8 → K := fun i => (i.val + 1 : ℕ)

def layerNormals (K : Type*) [Field K] : Layer.Normals K :=
  fun j ν a => table2Normal j ν a

/-- Only the first two part-sum trace points in each layer are lifted. -/
def layerHeights (K : Type*) [Field K] : Layer.Heights K :=
  fun j => ![1, (table2Zeta j 0 : K), (table2Zeta j 1 : K)]

def baseConeIndex (i : Fin 8) (μ : Fin 2) : Fin 28 :=
  ((finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin 16) (i, μ)).castAdd 12

def layerConeIndex (j : Fin 4) (ν : Fin 3) : Fin 28 :=
  ((finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12) (j, ν)).natAdd 16

def baseTraceIndex (i : Fin 8) : Fin 52 := i.castAdd 44

def layerTraceIndex (j ν : Fin 4) : Fin 52 :=
  ((((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16) (j, ν)).castAdd 4).natAdd 24).natAdd 8

@[simp] theorem support_baseConeIndex (i : Fin 8) (μ : Fin 2) :
    support (baseConeIndex i μ) = baseTraceIndex i := by
  apply Fin.ext
  rw [baseConeIndex, support, Fin.addCases_left]
  change (μ.val + 2 * i.val) / 2 = i.val
  have hμ := μ.isLt
  omega

@[simp] theorem support_layerConeIndex (j : Fin 4) (ν : Fin 3) :
    support (layerConeIndex j ν) = layerTraceIndex j ν.castSucc := by
  apply Fin.ext
  rw [layerConeIndex, support, Fin.addCases_right]
  change 32 + 4 * ((ν.val + 3 * j.val) / 3) + (ν.val + 3 * j.val) % 3 =
    8 + (24 + (ν.val + 4 * j.val))
  have hν := ν.isLt
  omega

@[simp] theorem configuration_normal_baseConeIndex (ω : K) (i : Fin 8) (μ : Fin 2) :
    (configuration ω).normal (baseConeIndex i μ) = baseNormal ω (baseParameters K i) μ := by
  funext a
  change (normalPolynomial (baseConeIndex i μ) a).eval₂ (Int.castRingHom K) ω = _
  rw [baseConeIndex, normalPolynomial, Fin.addCases_left, Equiv.symm_apply_apply]
  fin_cases μ <;> fin_cases a <;>
    simp [baseNormalPolynomial, baseNormal, baseParameters, thetaPlus, thetaMinus,
      sigmaPlus, sigmaMinus, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

@[simp] theorem configuration_normal_layerConeIndex (ω : K) (j : Fin 4) (ν : Fin 3) :
    (configuration ω).normal (layerConeIndex j ν) = layerNormals K j ν := by
  funext a
  change (normalPolynomial (layerConeIndex j ν) a).eval₂ (Int.castRingHom K) ω = _
  rw [layerConeIndex, normalPolynomial, Fin.addCases_right, Equiv.symm_apply_apply]
  change (Polynomial.C (table2Normal j ν a : ℤ)).eval₂ (Int.castRingHom K) ω = _
  rw [Polynomial.eval₂_C]
  change (((table2Normal j ν a : ℕ) : ℤ) : K) = _
  simp [layerNormals]

@[simp] theorem traceIntegers_baseTraceIndex (i : Fin 8) (a : Fin 12) :
    traceIntegers (baseTraceIndex i) a = baseTrace i a := by
  simp [traceIntegers, baseTraceIndex]

@[simp] theorem traceIntegers_layerTraceIndex (j ν : Fin 4) (a : Fin 12) :
    traceIntegers (layerTraceIndex j ν) a = layerTrace j ν a := by
  simp [traceIntegers, layerTraceIndex]

private theorem configuration_trace_baseTraceIndex (ω : K) (i : Fin 8) :
    (configuration ω).trace (baseTraceIndex i) =
      Fin.addCases (motive := fun _ => K) (Pi.single i 1) (0 : Fin 4 → K) := by
  funext a
  change (traceIntegers (baseTraceIndex i) a : K) = _
  rw [traceIntegers_baseTraceIndex]
  change Fin (8 + 4) at a
  induction a using Fin.addCases with
  | left a =>
      simp [baseTrace, Pi.single_apply, Fin.ext_iff, eq_comm]
  | right a =>
      have hne : 8 + a.val ≠ i.val := by have := i.isLt; omega
      simp [baseTrace, hne]

private theorem layerTrace_zero (j : Fin 4) (a : Fin 12) :
    layerTrace j 0 a = if a.val = 8 + j.val then 1 else 0 := by
  simp [layerTrace]

private theorem layerTrace_succ (j : Fin 4) (ν : Fin 3) (a : Fin 12) :
    layerTrace j ν.succ a = Fin.addCases
      (fun i : Fin 8 => if i.val / 3 = ν.val then 1 else 0)
      (fun i : Fin 4 => if i = j then (table2Zeta j ν : ℤ) else 0) a := by
  simp [layerTrace]

private theorem configuration_trace_layerTraceIndex (ω : K) (j : Fin 4) (ν : Fin 3) :
    (configuration ω).trace (layerTraceIndex j ν.castSucc) =
      Fin.addCases (motive := fun _ => K) (Layer.baseSupport K 8 j ν) (Pi.single j (layerHeights K j ν)) := by
  funext a
  change (traceIntegers (layerTraceIndex j ν.castSucc) a : K) = _
  rw [traceIntegers_layerTraceIndex]
  change Fin (8 + 4) at a
  fin_cases ν
  · change (layerTrace j 0 a : K) =
      Fin.addCases (motive := fun _ => K) (Layer.baseSupport K 8 j 0) (Pi.single j (1 : K)) a
    rw [layerTrace_zero]
    induction a using Fin.addCases with
    | left i =>
        have hne : i.val ≠ 8 + j.val := by have := i.isLt; omega
        simp [Layer.baseSupport, hne]
    | right i =>
        simp [Pi.single_apply, Fin.ext_iff, eq_comm]
  · change (layerTrace j (0 : Fin 3).succ a : K) =
      Fin.addCases (motive := fun _ => K) (Layer.baseSupport K 8 j 1) (Pi.single j (table2Zeta j 0 : K)) a
    rw [layerTrace_succ]
    induction a using Fin.addCases with
    | left i => simp [Layer.baseSupport]
    | right i => simp [Pi.single_apply, eq_comm]
  · change (layerTrace j (1 : Fin 3).succ a : K) =
      Fin.addCases (motive := fun _ => K) (Layer.baseSupport K 8 j 2) (Pi.single j (table2Zeta j 1 : K)) a
    rw [layerTrace_succ]
    induction a using Fin.addCases with
    | left i =>
        have he : i.val / 3 = 1 ↔ 3 ≤ i.val ∧ i.val < 6 := by omega
        simp [Layer.baseSupport, he]
    | right i => simp [Pi.single_apply, eq_comm]

theorem configuration_point_baseConeIndex (ω : K) (i : Fin 8) (μ : Fin 2) :
    (configuration ω).point (baseConeIndex i μ) =
      Layer.point (baseNormal ω (baseParameters K i) μ) (Pi.single i 1) 0 := by
  funext a
  induction a using Fin.addCases with
  | left a => simp [ConeConfiguration.point, Layer.point]
  | right a =>
      simp only [ConeConfiguration.point, Layer.point, Fin.addCases_right]
      change (1 : K) * (configuration ω).trace (support (baseConeIndex i μ)) a =
        Fin.addCases (motive := fun _ => K) (Pi.single i 1) (0 : Fin 4 → K) a
      rw [one_mul, support_baseConeIndex, configuration_trace_baseTraceIndex]

theorem configuration_point_layerConeIndex (ω : K) (j : Fin 4) (ν : Fin 3) :
    (configuration ω).point (layerConeIndex j ν) =
      Layer.point (layerNormals K j ν) (Layer.baseSupport K 8 j ν)
        (Pi.single j (layerHeights K j ν)) := by
  funext a
  induction a using Fin.addCases with
  | left a => simp [ConeConfiguration.point, Layer.point]
  | right a =>
      simp only [ConeConfiguration.point, Layer.point, Fin.addCases_right]
      change (1 : K) * (configuration ω).trace (support (layerConeIndex j ν)) a =
        Fin.addCases (motive := fun _ => K) (Layer.baseSupport K 8 j ν) (Pi.single j (layerHeights K j ν)) a
      rw [one_mul, support_layerConeIndex, configuration_trace_layerTraceIndex]

/-- The initial marked configuration contains exactly the prescribed base
pairs and the twelve supported layer points. -/
theorem initialPointPattern (ω : K) :
    PointPattern (configuration ω) ω (baseParameters K) (layerNormals K)
      (layerHeights K) (Layer.baseSupport K 8) := by
  constructor
  · intro k
    change Fin (16 + 12) at k
    induction k using Fin.addCases with
    | left k =>
        obtain ⟨⟨i, μ⟩, rfl⟩ := (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin 16).surjective k
        exact Or.inl ⟨i, μ, configuration_point_baseConeIndex ω i μ⟩
    | right k =>
        obtain ⟨⟨j, ν⟩, rfl⟩ := (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin 12).surjective k
        exact Or.inr ⟨j, ν, configuration_point_layerConeIndex ω j ν⟩
  · intro i μ
    exact ⟨baseConeIndex i μ, configuration_point_baseConeIndex ω i μ⟩
  · intro j ν
    exact ⟨layerConeIndex j ν, configuration_point_layerConeIndex ω j ν⟩

theorem baseParameters_ne_zero [CharZero K] (i : Fin 8) : baseParameters K i ≠ 0 := by
  unfold baseParameters
  exact_mod_cast (show i.val + 1 ≠ 0 by omega)

theorem baseParameters_injective [CharZero K] : Function.Injective (baseParameters K) := by
  intro i j he
  apply Fin.ext
  change ((i.val + 1 : ℕ) : K) = ((j.val + 1 : ℕ) : K) at he
  have hn : i.val + 1 = j.val + 1 := by exact_mod_cast he
  omega

theorem initial_chordFactor_ne_zero [CharZero K] (i j : Fin 8) (hij : i ≠ j) :
    chordFactor (baseParameters K i) (baseParameters K j) ≠ 0 := by
  unfold chordFactor
  apply mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (fun h => hij (baseParameters_injective h))))
  have hn : (i.val + 1) ^ 2 + (i.val + 1) * (j.val + 1) + (j.val + 1) ^ 2 ≠ 0 := by
    positivity
  unfold baseParameters
  exact_mod_cast hn

theorem layerHeights_ne_zero [CharZero K] (j : Fin 4) (ν : Fin 3) : layerHeights K j ν ≠ 0 := by
  fin_cases j <;> fin_cases ν <;> norm_num [layerHeights, table2Zeta]

def layerNormalIntegers (j : Fin 4) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun ν a => table2Normal j ν a

theorem layerNormalMatrix_eq_map (j : Fin 4) :
    Layer.normalMatrix (layerNormals K) j = (layerNormalIntegers j).map (Int.castRingHom K) := by
  ext ν a
  change (table2Normal j ν a : K) = (((table2Normal j ν a : ℕ) : ℤ) : K)
  simp

theorem layerNormalMatrix_mod_det (j : Fin 4) :
    ((layerNormalIntegers j).map (Int.castRingHom (ZMod 1009))).det =
      (![832, 164, 963, 296] : Fin 4 → ZMod 1009) j := by
  fin_cases j <;> norm_num [Matrix.det_fin_three, layerNormalIntegers, table2Normal] <;> decide +kernel

theorem layerNormalMatrix_det_ne_zero [CharZero K] (j : Fin 4) :
    (Layer.normalMatrix (layerNormals K) j).det ≠ 0 := by
  rw [layerNormalMatrix_eq_map]
  apply integer_matrix_det_ne_zero_over (layerNormalIntegers j) 1009
  rw [layerNormalMatrix_mod_det]
  fin_cases j <;> decide +kernel

end IdealGeneration.TripleNormalInitial
