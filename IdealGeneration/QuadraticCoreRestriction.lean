module

public import IdealGeneration.QuadraticCoreRestrictionData
public import IdealGeneration.QuadraticTraceRestriction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Restricting the actual generators and eliminated pairs to the selected core. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreRestriction
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticCoreMiddle QuadraticTraceRestriction

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]
variable (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)

local notation "B" => baseEmbedding D.distinguishedPair
local notation "E" => traceEmbedding D.distinguishedPair e
local notation "D₀" => restrictParameters D e
local notation "ρ" => restrictPolynomial K E

omit [Fintype P] [Fintype J] in
@[simp] theorem restrict_baseVariable (i : Unit × Bool) :
    ρ (X (.inl (B i))) = X (.inl i) := by
  simpa only [traceEmbedding_inl] using restrict_X_embedded K E (.inl i)

omit [Fintype P] [Fintype J] in
@[simp] theorem restrict_layerVariable (j : Fin 2) :
    ρ (X (.inr (e j))) = X (.inr j) := by
  simpa only [traceEmbedding_inr] using restrict_X_embedded K E (.inr j)

omit [Fintype P] in
/-- Restriction of a trace-linear layer term retains exactly the selected layers. -/
theorem restrict_layerSum (v : J → K) :
    ρ (∑ j, C (v j) * X (.inr j)) = ∑ j, C (v (e j)) * X (.inr j) := by
  simp only [map_sum, map_mul, algHom_C, MvPolynomial.algebraMap_eq]
  rw [sum_over_embedding e (fun j => C (v j) * ρ (X (.inr j)))]
  · simp
  · intro j hj
    rw [restrict_X_off K E (j := .inr j) (by simpa only [inr_mem_range_traceEmbedding] using hj), mul_zero]

@[simp] theorem restrict_firstLift (k : Fin 3) : ρ (D.firstLift k) = (D₀).firstLift k := by
  simp only [QuadraticLiftParameters.firstLift, restrict_linearPolynomial]
  congr 1
  funext j
  cases j <;> simp

@[simp] theorem restrict_secondLift (k : Fin 3) : ρ (D.secondLift k) = (D₀).secondLift k := by
  simp only [QuadraticLiftParameters.secondLift, restrict_linearPolynomial]
  congr 1
  funext j
  cases j <;> simp

omit [Fintype P] in
@[simp] theorem restrict_firstGenerator (i : Unit × Bool) :
    ρ (firstGenerator D.firstCorrection (B i)) = firstGenerator (D₀).firstCorrection i := by
  simp only [firstGenerator, map_add, restrict_baseVariable, restrict_layerSum,
    restrictParameters_firstCorrection]

omit [Fintype P] in
@[simp] theorem restrict_secondGenerator (i : Unit × Bool) :
    ρ (secondGenerator D.slope D.secondCorrection (B i)) =
      secondGenerator (D₀).slope (D₀).secondCorrection i := by
  simp only [secondGenerator, map_add, map_mul, algHom_C, MvPolynomial.algebraMap_eq,
    restrict_baseVariable, restrict_layerSum, restrictParameters_secondCorrection]
  all_goals rfl

omit [Fintype P] in
theorem restrict_firstGenerator_off (i : P × Bool) (hi : i.1 ≠ D.distinguishedPair) :
    ρ (firstGenerator D.firstCorrection i) = 0 := by
  have hX := restrict_X_off K E (j := .inl i)
    (by simpa only [inl_mem_range_traceEmbedding] using hi)
  have h (j : J) := firstCorrection_off D i j hi
  simp [firstGenerator, h, hX]

omit [Fintype P] in
theorem restrict_secondGenerator_off (i : P × Bool) (hi : i.1 ≠ D.distinguishedPair) :
    ρ (secondGenerator D.slope D.secondCorrection i) = 0 := by
  have hX := restrict_X_off K E (j := .inl i)
    (by simpa only [inl_mem_range_traceEmbedding] using hi)
  have h (j : J) := secondCorrection_off D i j hi
  simp [secondGenerator, h, hX]

@[simp] theorem restrict_firstKernelMap (h : P × Bool → K) :
    ρ (firstKernelMap D.firstCorrection h) = firstKernelMap (D₀).firstCorrection (h ∘ B) := by
  simp only [firstKernelMap, Fintype.linearCombination_apply, map_sum, map_smul]
  rw [sum_over_embedding B (fun i => h i • ρ (firstGenerator D.firstCorrection i))]
  · simp only [restrict_firstGenerator, Function.comp_apply]
  · intro i hi
    rw [restrict_firstGenerator_off D e i (by simpa only [mem_range_baseEmbedding] using hi), smul_zero]

@[simp] theorem restrict_secondKernelMap (h : P × Bool → K) :
    ρ (secondKernelMap D.slope D.secondCorrection h) =
      secondKernelMap (D₀).slope (D₀).secondCorrection (h ∘ B) := by
  simp only [secondKernelMap, Fintype.linearCombination_apply, map_sum, map_smul]
  rw [sum_over_embedding B (fun i => h i • ρ (secondGenerator D.slope D.secondCorrection i))]
  · simp only [restrict_secondGenerator, Function.comp_apply]
  · intro i hi
    rw [restrict_secondGenerator_off D e i (by simpa only [mem_range_baseEmbedding] using hi), smul_zero]

/-- The mixed-product subspace restricts to the mixed-product subspace of the core. -/
theorem restrictPair_mixedImage :
    (quadraticMixedImage D.slope D.firstCorrection D.secondCorrection).map (restrictPair K E) ≤
      quadraticMixedImage (D₀).slope (D₀).firstCorrection (D₀).secondCorrection := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨L, rfl⟩ := hf
  let L₀ : Unit × Bool → TraceIndex → K := fun i j => L (B i) (E j)
  refine ⟨L₀, ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · change (∑ i, firstGenerator (D₀).firstCorrection i * linearPolynomial (L₀ i)) =
      ρ (∑ i, firstGenerator D.firstCorrection i * linearPolynomial (L i))
    simp only [map_sum, map_mul, restrict_linearPolynomial]
    rw [sum_over_embedding B (fun i => ρ (firstGenerator D.firstCorrection i) * linearPolynomial (L i ∘ E))]
    · simp only [restrict_firstGenerator, L₀, Function.comp_def]
    · intro i hi
      rw [restrict_firstGenerator_off D e i (by simpa only [mem_range_baseEmbedding] using hi), zero_mul]
  · change (∑ i, secondGenerator (D₀).slope (D₀).secondCorrection i * linearPolynomial (L₀ i)) =
      ρ (∑ i, secondGenerator D.slope D.secondCorrection i * linearPolynomial (L i))
    simp only [map_sum, map_mul, restrict_linearPolynomial]
    rw [sum_over_embedding B (fun i => ρ (secondGenerator D.slope D.secondCorrection i) * linearPolynomial (L i ∘ E))]
    · simp only [restrict_secondGenerator, L₀, Function.comp_def]
    · intro i hi
      rw [restrict_secondGenerator_off D e i (by simpa only [mem_range_baseEmbedding] using hi), zero_mul]

@[simp] theorem restrict_firstLowerPart (x : LiftSpace (K := K) (H := P × Bool → K)) :
    ρ (lowerPart D.firstLift (firstKernelMap D.firstCorrection) x) =
      lowerPart (D₀).firstLift (firstKernelMap (D₀).firstCorrection) (x.1, x.2 ∘ B) := by
  change ρ ((∑ i, x.1 i • D.firstLift i) + firstKernelMap D.firstCorrection x.2) =
    (∑ i, x.1 i • (D₀).firstLift i) + firstKernelMap (D₀).firstCorrection (x.2 ∘ B)
  simp only [map_add, map_sum, map_smul, restrict_firstLift, restrict_firstKernelMap]

@[simp] theorem restrict_secondLowerPart (x : LiftSpace (K := K) (H := P × Bool → K)) :
    ρ (lowerPart D.secondLift (secondKernelMap D.slope D.secondCorrection) x) =
      lowerPart (D₀).secondLift (secondKernelMap (D₀).slope (D₀).secondCorrection) (x.1, x.2 ∘ B) := by
  change ρ ((∑ i, x.1 i • D.secondLift i) + secondKernelMap D.slope D.secondCorrection x.2) =
    (∑ i, x.1 i • (D₀).secondLift i) + secondKernelMap (D₀).slope (D₀).secondCorrection (x.2 ∘ B)
  simp only [map_add, map_sum, map_smul, restrict_secondLift, restrict_secondKernelMap]

/-- Restrict the mixed kernel coefficients and retain the pure normal coefficients. -/
def restrictOmega (x : Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K))) :
    Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K)) :=
  ⟨((x.val.1.1, x.val.1.2 ∘ B), (x.val.2.1, x.val.2.2 ∘ B)), x.property⟩

/-- Extend a mixed kernel coefficient vector by zero on the other base pairs. -/
def extendKernel (h : KernelCoefficients K) : P × Bool → K := by
  classical
  exact fun i => if i.1 = D.distinguishedPair then h ((), i.2) else 0

omit [Fintype P] [Fintype J] in
@[simp] theorem extendKernel_restrict (h : KernelCoefficients K) : extendKernel D h ∘ B = h := by
  funext i
  rcases i with ⟨u, b⟩
  cases u
  simp [extendKernel]

/-- Zero-extend the mixed part of a core element of `Ω`. -/
def extendOmega (x : Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K))) :
    Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K)) :=
  ⟨((x.val.1.1, extendKernel D x.val.1.2), (x.val.2.1, extendKernel D x.val.2.2)), x.property⟩

omit [Fintype P] [Fintype J] in
@[simp] theorem restrictOmega_extendOmega
    (x : Omega (LinearMap.fst K (Fin 3 → K) (KernelCoefficients K))) :
    restrictOmega D (extendOmega D x) = x := by
  apply Subtype.ext
  rcases x with ⟨⟨⟨q, h⟩, ⟨r, k⟩⟩, _⟩
  simp [restrictOmega, extendOmega]

/-- The actual quadratic eliminated pair commutes with restriction. -/
theorem restrict_quadraticPhi
    (x : Omega (LinearMap.fst K (Fin 3 → K) (P × Bool → K))) :
    restrictPair K E (quadraticPhi D.firstLift D.secondLift (firstKernelMap D.firstCorrection)
      (secondKernelMap D.slope D.secondCorrection) D.firstLift_homogeneous D.secondLift_homogeneous
      (firstKernelMap_homogeneous D.firstCorrection) (secondKernelMap_homogeneous D.slope D.secondCorrection) x) =
    quadraticPhi (D₀).firstLift (D₀).secondLift (firstKernelMap (D₀).firstCorrection)
      (secondKernelMap (D₀).slope (D₀).secondCorrection) (D₀).firstLift_homogeneous (D₀).secondLift_homogeneous
      (firstKernelMap_homogeneous (D₀).firstCorrection) (secondKernelMap_homogeneous (D₀).slope (D₀).secondCorrection)
      (restrictOmega D x) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quadraticPhi, phi, prePhi, restrictOmega]

end IdealGeneration.QuadraticCoreRestriction
