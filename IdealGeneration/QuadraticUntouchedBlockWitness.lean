module

public import IdealGeneration.QuadraticPairProjection
public import IdealGeneration.QuadraticBlockEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Actual correction maps for the untouched evaluation blocks in (A.5). -/

noncomputable section
namespace IdealGeneration.QuadraticElimination.QuadraticLiftParameters
open MvPolynomial QuadraticFlag QuadraticBlockEvaluation Module

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

/-- Identify the two normal lift combinations with the Boolean form labels. -/
def boolFormIndex (b : Bool) : Fin 2 := if b then 1 else 0

variable (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)

/-- The actual projected elimination image, i.e. the space (W'). -/
abbrev projectedPairSpace := (D.actualProjectedPairMap hc).range

local instance projectedPairSpaceGroup : AddCommGroup (D.projectedPairSpace hc) :=
  Module.addCommMonoidToAddCommGroup K

/-- Evaluate both polynomial components of one projected pair at a point. -/
def projectedEvaluation (x : (P × Bool) ⊕ J → K) : D.projectedPairSpace hc →ₗ[K] K × K where
  toFun w := (eval x w.val.1.val, eval x w.val.2.val)
  map_add' w z := by apply Prod.ext <;> simp
  map_smul' a w := by apply Prod.ext <;> simp

@[simp] theorem projectedEvaluation_apply (x : (P × Bool) ⊕ J → K)
    (w : D.projectedPairSpace hc) :
    D.projectedEvaluation hc x w = (eval x w.val.1.val, eval x w.val.2.val) := rfl

/-- Evaluate an indexed family of points in the actual image. -/
def projectedEvaluationFamily {A : Type*} (x : A → (P × Bool) ⊕ J → K) :
    D.projectedPairSpace hc →ₗ[K] (A → K × K) :=
  LinearMap.pi fun a => D.projectedEvaluation hc (x a)

@[simp] theorem projectedEvaluationFamily_apply {A : Type*}
    (x : A → (P × Bool) ⊕ J → K) (w : D.projectedPairSpace hc) (a : A) :
    D.projectedEvaluationFamily hc x w a = D.projectedEvaluation hc (x a) w := rfl

/-- The actual projected generator (one of the four in an untouched pair). -/
def pairBlockGenerator (p : P) (t : Bool × Bool) : D.projectedPairSpace hc :=
  ⟨D.actualProjectedPairMap hc (untouchedOmega (K := K) (p, t.1) (boolFormIndex t.2)),
    ⟨_, rfl⟩⟩

/-- Vary the four coefficients of the projected generators in a base pair. -/
def pairCorrection (p : P) : (Bool × Bool → K) →ₗ[K] D.projectedPairSpace hc :=
  Fintype.linearCombination K (D.pairBlockGenerator hc p)

/-- The two probes assigned to a base pair. -/
def pairBlockEvaluation (layers : Bool → J) (p : P) :
    D.projectedPairSpace hc →ₗ[K] (Bool → K × K) :=
  D.projectedEvaluationFamily hc (fun j => pairProbe p (layers j))

/-- The coefficient matrix of the actual four-generator block. -/
def pairBlockCoefficients (layers : Bool → J) (p : P) : Bool → Bool → Bool → K :=
  fun b j r => D.pairGamma (p, b) (boolFormIndex r) (layers j)

private theorem pairBlockGenerator_eval_same (p : P) (hp : p ≠ D.distinguishedPair)
    (t : Bool × Bool) (j : J) :
    D.projectedEvaluation hc (pairProbe p j) (D.pairBlockGenerator hc p t) =
      if t.1 then
        (-(D.pairGamma (p, true) (boolFormIndex t.2) j),
          D.slope (p, false) * (-(D.pairGamma (p, true) (boolFormIndex t.2) j)))
      else
        (D.pairGamma (p, false) (boolFormIndex t.2) j,
          D.slope (p, true) * D.pairGamma (p, false) (boolFormIndex t.2) j) := by
  rcases t with ⟨b, r⟩
  cases b
  · simpa [pairBlockGenerator, partner, Bool.false_ne_true, Bool.not_false] using
      D.eval_actualProjectedPairMap_pairProbe hc (p, false) (boolFormIndex r) hp p j
  · simpa [pairBlockGenerator, partner, Bool.not_true] using
      D.eval_actualProjectedPairMap_pairProbe hc (p, true) (boolFormIndex r) hp p j

private theorem pairBlockGenerator_eval_other (p q : P) (hp : p ≠ D.distinguishedPair)
    (hpq : p ≠ q) (t : Bool × Bool) (j : J) :
    D.projectedEvaluation hc (pairProbe q j) (D.pairBlockGenerator hc p t) = 0 := by
  simpa [pairBlockGenerator, hpq] using
    D.eval_actualProjectedPairMap_pairProbe hc (p, t.1) (boolFormIndex t.2) hp q j

/-- The actual diagonal block is exactly the four-form evaluation of its two slopes and layer matrices. -/
theorem pairBlockEvaluation_comp_pairCorrection (layers : Bool → J)
    (p : P) (hp : p ≠ D.distinguishedPair) :
    (D.pairBlockEvaluation hc layers p).comp (D.pairCorrection hc p) =
      localBlockEvaluation (D.slope (p, false)) (D.slope (p, true))
        (D.pairBlockCoefficients layers p) := by
  apply LinearMap.ext
  intro a
  funext j
  rw [localBlockEvaluation_apply]
  change D.projectedEvaluation hc (pairProbe p (layers j)) (D.pairCorrection hc p a) = _
  rw [pairCorrection, Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, D.pairBlockGenerator_eval_same hc p hp]
  rw [Fintype.sum_prod_type]
  apply Prod.ext <;>
    simp [pairBlockCoefficients, Fintype.univ_bool, smul_eq_mul] <;> ring

/-- The height determinant conditions make the actual diagonal block onto. -/
theorem pairBlockEvaluation_comp_pairCorrection_surjective (layers : Bool → J)
    (p : P) (hp : p ≠ D.distinguishedPair)
    (hL : ∀ b, let L := D.pairBlockCoefficients layers p b
      L false false * L true true - L true false * L false true ≠ 0) :
    Function.Surjective ((D.pairBlockEvaluation hc layers p).comp (D.pairCorrection hc p)) := by
  rw [D.pairBlockEvaluation_comp_pairCorrection hc layers p hp]
  exact localBlockEvaluation_surjective _ _ _
    (fun h => Bool.false_ne_true (congrArg Prod.snd (hc h))) hL

/-- Corrections on one untouched pair vanish at the probes assigned to all other pairs. -/
theorem pairBlockEvaluation_comp_pairCorrection_eq_zero (layers : Bool → J)
    (p q : P) (hp : p ≠ D.distinguishedPair) (hpq : p ≠ q) :
    (D.pairBlockEvaluation hc layers q).comp (D.pairCorrection hc p) = 0 := by
  apply LinearMap.ext
  intro a
  funext j
  change D.projectedEvaluation hc (pairProbe q (layers j)) (D.pairCorrection hc p a) = 0
  rw [pairCorrection, Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, D.pairBlockGenerator_eval_other hc p q hp hpq, smul_zero, Finset.sum_const_zero]

/-- A pair correction vanishes on any probe family with equal paired coordinates there. -/
theorem projectedEvaluationFamily_comp_pairCorrection_eq_zero {A : Type*}
    (p : P) (hp : p ≠ D.distinguishedPair) (x : A → (P × Bool) ⊕ J → K)
    (hx : ∀ a, x a (.inl (p, false)) = x a (.inl (p, true))) :
    (D.projectedEvaluationFamily hc x).comp (D.pairCorrection hc p) = 0 := by
  apply LinearMap.ext
  intro a
  funext j
  change D.projectedEvaluation hc (x j) (D.pairCorrection hc p a) = 0
  rw [pairCorrection, Fintype.linearCombination_apply, map_sum]
  have hz (t : Bool × Bool) :
      D.projectedEvaluation hc (x j) (D.pairBlockGenerator hc p t) = 0 := by
    rcases t with ⟨b, r⟩
    apply D.eval_actualProjectedPairMap_eq_zero_of_same hc (p, b) (boolFormIndex r) hp (x j)
    cases b
    · exact hx j
    · exact (hx j).symm
  simp_rw [map_smul, hz, smul_zero, Finset.sum_const_zero]

/-- The dimension bound for the actual projected pair space. -/
theorem finrank_projectedPairSpace_le :
    finrank K (D.projectedPairSpace hc) ≤ 2 * Fintype.card (P × Bool) + 2 := by
  apply (LinearMap.finrank_range_le _).trans_eq
  simpa only [Module.finrank_pi] using
    (finrank_explicitOmega (K := K) (H := P × Bool → K))

/-- Joint evaluation on the actual (W') is bijective when the core interpolates
and the actual layer coefficients have nonzero determinants. -/
theorem projectedPairSpace_blockEvaluation_bijective (layers : Bool → J)
    (core : Fin 3 → (P × Bool) ⊕ J → K)
    (hcore : Function.Surjective (D.projectedEvaluationFamily hc core))
    (hcoreCoordinates : ∀ p, p ≠ D.distinguishedPair → ∀ a,
      core a (.inl (p, false)) = core a (.inl (p, true)))
    (hL : ∀ p, p ≠ D.distinguishedPair → ∀ b, let L := D.pairBlockCoefficients layers p b
      L false false * L true true - L true false * L false true ≠ 0) :
    Function.Bijective (jointEvaluation (K := K) (W := D.projectedPairSpace hc)
      (D.projectedEvaluationFamily hc core)
      (fun p : {p : P // p ≠ D.distinguishedPair} => D.pairBlockEvaluation hc layers p.val)) := by
  classical
  apply coreUntouchedEvaluation_bijective D.distinguishedPair _ _
    (fun p => D.pairCorrection hc p.val) hcore
  · intro p
    exact D.projectedEvaluationFamily_comp_pairCorrection_eq_zero hc p.val p.property core
      (hcoreCoordinates p.val p.property)
  · intro p q hpq
    exact D.pairBlockEvaluation_comp_pairCorrection_eq_zero hc layers p.val q.val p.property
      (fun h => hpq (Subtype.ext h))
  · intro p
    exact D.pairBlockEvaluation_comp_pairCorrection_surjective hc layers p.val p.property
      (hL p.val p.property)
  · exact D.finrank_projectedPairSpace_le hc

end IdealGeneration.QuadraticElimination.QuadraticLiftParameters
