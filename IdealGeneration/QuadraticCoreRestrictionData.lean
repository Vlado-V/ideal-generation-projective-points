module

public import IdealGeneration.QuadraticCoreProbeEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The distinguished pair and two selected layers inherit the actual lift data. -/

noncomputable section
namespace IdealGeneration.QuadraticCoreRestriction
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticCoreMiddle

variable {K P J : Type*} [Field K]

/-- Include the distinguished pair of base coordinates. -/
def baseEmbedding (p : P) : Unit × Bool ↪ P × Bool where
  toFun i := (p, i.2)
  inj' _i _j h := Prod.ext (Subsingleton.elim _ _) (congrArg (fun v : P × Bool => v.2) h)

@[simp] theorem baseEmbedding_apply (p : P) (i : Unit × Bool) :
    baseEmbedding p i = (p, i.2) := rfl

@[simp] theorem mem_range_baseEmbedding (p : P) (i : P × Bool) :
    i ∈ Set.range (baseEmbedding p) ↔ i.1 = p := by
  constructor
  · rintro ⟨j, rfl⟩
    rfl
  · intro h
    exact ⟨((), i.2), Prod.ext h.symm rfl⟩

/-- Include the four trace variables retained in the core. -/
def traceEmbedding (p : P) (e : Fin 2 ↪ J) : TraceIndex ↪ ((P × Bool) ⊕ J) :=
  (baseEmbedding p).sumMap e

@[simp] theorem traceEmbedding_inl (p : P) (e : Fin 2 ↪ J) (i : Unit × Bool) :
    traceEmbedding p e (.inl i) = Sum.inl (baseEmbedding p i) := rfl

@[simp] theorem traceEmbedding_inr (p : P) (e : Fin 2 ↪ J) (j : Fin 2) :
    traceEmbedding p e (.inr j) = Sum.inr (e j) := rfl

@[simp] theorem inl_mem_range_traceEmbedding (p : P) (e : Fin 2 ↪ J) (i : P × Bool) :
    Sum.inl i ∈ Set.range (traceEmbedding p e) ↔ i.1 = p := by
  constructor
  · rintro ⟨j, h⟩
    cases j with
    | inl j => exact (mem_range_baseEmbedding p i).mp ⟨j, Sum.inl.inj h⟩
    | inr j => cases h
  · intro h
    obtain ⟨j, rfl⟩ := (mem_range_baseEmbedding p i).mpr h
    exact ⟨.inl j, rfl⟩

@[simp] theorem inr_mem_range_traceEmbedding (p : P) (e : Fin 2 ↪ J) (j : J) :
    Sum.inr j ∈ Set.range (traceEmbedding p e) ↔ j ∈ Set.range e := by
  constructor
  · rintro ⟨i, h⟩
    cases i with
    | inl i => cases h
    | inr i => exact ⟨i, Sum.inr.inj h⟩
  · rintro ⟨i, rfl⟩
    exact ⟨.inr i, rfl⟩

/-- The actual core parameter data are restrictions of the full parameter data. -/
def restrictParameters (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J) :
    QuadraticLiftParameters K Unit (Fin 2) where
  slope i := D.slope (baseEmbedding D.distinguishedPair i)
  distinguishedPair := ()
  normal₀ j := D.normal₀ (e j)
  normal₁ j := D.normal₁ (e j)
  baseHeight i := D.baseHeight (baseEmbedding D.distinguishedPair i)
  height₀ j := D.height₀ (e j)
  height₁ j := D.height₁ (e j)
  baseHeight_ne i := D.baseHeight_ne (baseEmbedding D.distinguishedPair i)
  height₀_ne j := D.height₀_ne (e j)
  height₁_ne j := D.height₁_ne (e j)
  determinant_ne j := D.determinant_ne (e j)

theorem restrictParameters_slope_injective (D : QuadraticLiftParameters K P J) (e : Fin 2 ↪ J)
    (hc : Function.Injective D.slope) : Function.Injective (restrictParameters D e).slope :=
  hc.comp (baseEmbedding D.distinguishedPair).injective

@[simp] theorem pairPoint_on (p : P) (b : Bool) :
    pairPoint (K := K) p (p, b) = 1 := by
  classical
  cases b <;> simp [pairPoint, coordinatePoint]

@[simp] theorem restrictParameters_baseCoefficient (D : QuadraticLiftParameters K P J)
    (e : Fin 2 ↪ J) (k : Fin 3) (i : Unit × Bool) :
    (restrictParameters D e).baseCoefficient k i =
      D.baseCoefficient k (baseEmbedding D.distinguishedPair i) := rfl

section PairedBaseValue
variable [Fintype P]

/-- Only the two distinguished base coefficients contribute to the lift data. -/
theorem pairedBaseValue_eq (D : QuadraticLiftParameters K P J) (k : Fin 3) :
    D.pairedBaseValue k = D.baseCoefficient k (D.distinguishedPair, false) +
      D.baseCoefficient k (D.distinguishedPair, true) := by
  classical
  simp [QuadraticLiftParameters.pairedBaseValue, pairPoint, coordinatePoint, mul_add,
    Finset.sum_add_distrib, mul_ite]

@[simp] theorem restrictParameters_pairedBaseValue (D : QuadraticLiftParameters K P J)
    (e : Fin 2 ↪ J) (k : Fin 3) :
    (restrictParameters D e).pairedBaseValue k = D.pairedBaseValue k := by
  rw [pairedBaseValue_eq, pairedBaseValue_eq]
  rfl

@[simp] theorem restrictParameters_layerCoefficients (D : QuadraticLiftParameters K P J)
    (e : Fin 2 ↪ J) (k : Fin 3) (j : Fin 2) :
    (restrictParameters D e).layerCoefficients k j = D.layerCoefficients k (e j) := by
  simp only [QuadraticLiftParameters.layerCoefficients, restrictParameters_pairedBaseValue]
  rfl

end PairedBaseValue

@[simp] theorem restrictParameters_firstCorrection (D : QuadraticLiftParameters K P J)
    (e : Fin 2 ↪ J) (i : Unit × Bool) (j : Fin 2) :
    (restrictParameters D e).firstCorrection i j =
      D.firstCorrection (baseEmbedding D.distinguishedPair i) (e j) := by
  rcases i with ⟨u, b⟩
  cases u
  simp [QuadraticLiftParameters.firstCorrection, layerCorrection, restrictParameters]

@[simp] theorem restrictParameters_secondCorrection (D : QuadraticLiftParameters K P J)
    (e : Fin 2 ↪ J) (i : Unit × Bool) (j : Fin 2) :
    (restrictParameters D e).secondCorrection i j =
      D.secondCorrection (baseEmbedding D.distinguishedPair i) (e j) := by
  rcases i with ⟨u, b⟩
  cases u
  simp [QuadraticLiftParameters.secondCorrection, layerCorrection, restrictParameters]

theorem firstCorrection_off (D : QuadraticLiftParameters K P J) (i : P × Bool) (j : J)
    (hi : i.1 ≠ D.distinguishedPair) : D.firstCorrection i j = 0 := by
  exact congrArg Prod.fst (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair
    D.normal₀ D.normal₁ i j hi)

theorem secondCorrection_off (D : QuadraticLiftParameters K P J) (i : P × Bool) (j : J)
    (hi : i.1 ≠ D.distinguishedPair) : D.secondCorrection i j = 0 := by
  exact congrArg Prod.snd (layerCorrection_eq_zero_of_ne D.slope D.distinguishedPair
    D.normal₀ D.normal₁ i j hi)

end IdealGeneration.QuadraticCoreRestriction
