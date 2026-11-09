module

public import IdealGeneration.QuadraticCoreProjectionRestriction
public import IdealGeneration.QuadraticCoreFamily
public import IdealGeneration.QuadraticFlagProbeScalar
public import IdealGeneration.QuadraticUntouchedBlockWitness
public import IdealGeneration.QuadraticFixedHeights

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Joint evaluation of the actual projected flag space at the probes in (A.4). -/

noncomputable section
namespace IdealGeneration.QuadraticCoreRestriction
open MvPolynomial Module QuadraticCoreMiddle QuadraticFlag QuadraticFlagFamily QuadraticBlockEvaluation
open QuadraticTraceRestriction QuadraticFlagProbeScalar QuadraticElimination QuadraticLiftParameters
open scoped Classical

variable {K P J : Type*} [Field K] [CharZero K] [Fintype P] [Fintype J]

omit [CharZero K] [Fintype P] [Fintype J] in
private theorem pairProbe_eq_add (p : P) (j : J) :
    pairProbe (K := K) p j = coordinatePoint (.inl (p, false)) + coordinatePoint (.inr j) := by
  classical
  funext i
  cases i <;> simp [pairProbe, coordinatePoint]

omit [CharZero K] [Fintype P] [Fintype J] in
/-- The three full core probes are the zero extensions of the corresponding core points. -/
theorem extendPoint_coreProbePoint (p : P) (layers : Bool → J) (hne : layers false ≠ layers true)
    (i : Fin 3) : extendPoint K (traceEmbedding p (selectedLayerEmbedding layers hne))
      (coreProbePoint K i) = flagCoreProbes p layers i := by
  classical
  fin_cases i <;> simp [coreProbePoint, flagCoreProbes, pairProbe_eq_add, layerPairProbe]

/-- Every vector value on the three core probes is realized by the actual projected image. -/
theorem projectedEvaluationFamily_core_surjective
    (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (layers : Bool → J) (hne : layers false ≠ layers true)
    (hD : restrictParameters D (selectedLayerEmbedding layers hne) = coreParameters K) :
    Function.Surjective (D.projectedEvaluationFamily hc (flagCoreProbes D.distinguishedPair layers)) := by
  intro v
  let e := selectedLayerEmbedding layers hne
  obtain ⟨x, hx⟩ := fullCoreProbeEvaluation_surjective D e hc hD
    (fun i => (v i).1, fun i => (v i).2)
  refine ⟨⟨actualProjectedMap D hc x, ⟨x, rfl⟩⟩, ?_⟩
  funext i
  simp only [projectedEvaluationFamily_apply, projectedEvaluation_apply, ← extendPoint_coreProbePoint
    D.distinguishedPair layers hne i]
  apply Prod.ext
  · exact congrFun (congrArg Prod.fst hx) i
  · exact congrFun (congrArg Prod.snd hx) i

local instance projectedPairSpaceGroup (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) : AddCommGroup (D.projectedPairSpace hc) :=
  Module.addCommMonoidToAddCommGroup K

variable (K) [DecidableEq J]
variable (p : P) (layers : Bool → J)

local notation "D" => parameters K p layers
local notation "hc" => parameters_slope_injective K p layers

/-- The actual vector evaluation at every probe in (A.4), for the canonical flag. -/
def canonicalJointEvaluation : (D).projectedPairSpace hc →ₗ[K]
    ((Fin 3 → K × K) × ({q : P // q ≠ p} → Bool → K × K)) :=
  jointEvaluation ((D).projectedEvaluationFamily hc (flagCoreProbes p layers))
    (fun q => (D).pairBlockEvaluation hc layers q.val)

/-- All probe values are independent coordinates on the actual projected flag space. -/
theorem canonicalJointEvaluation_bijective (hne : layers false ≠ layers true) :
    Function.Bijective (canonicalJointEvaluation K p layers) := by
  have hcore := projectedEvaluationFamily_core_surjective D hc layers hne
    (restrict_canonical_parameters (K := K) p layers hne)
  refine (D).projectedPairSpace_blockEvaluation_bijective hc layers _ hcore ?_ ?_
  · intro q hq i
    exact (flagCoreProbes_apply_of_ne p q hq layers i false).trans
      (flagCoreProbes_apply_of_ne p q hq layers i true).symm
  · intro q _ b
    exact gammaPair_fixed_det_ne K p layers hne (q, b)

/-- The projected elimination image attains its full dimension `2h+2`. -/
theorem finrank_canonicalProjectedPairSpace (hne : layers false ≠ layers true) :
    Module.finrank K ((D).projectedPairSpace hc) = 2 * Fintype.card (P × Bool) + 2 := by
  exact (LinearEquiv.ofBijective (canonicalJointEvaluation K p layers)
    (canonicalJointEvaluation_bijective K p layers hne)).finrank_eq.trans
    (finrank_coreUntouchedTarget (K := K) p)

/-- The actual projection is injective on the normal-cubic kernel. -/
theorem canonicalActualProjectedMap_injective (hne : layers false ≠ layers true) :
    Function.Injective ((D).actualProjectedPairMap hc) := by
  have hdim : Module.finrank K (FullOmega K P) = Module.finrank K ((D).projectedPairSpace hc) := by
    rw [finrank_canonicalProjectedPairSpace K p layers hne]
    simpa only [Module.finrank_pi] using
      (finrank_explicitOmega (K := K) (H := P × Bool → K))
  let f := ((D).actualProjectedPairMap hc).rangeRestrict
  have hi : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (LinearMap.surjective_rangeRestrict ((D).actualProjectedPairMap hc))
  exact fun _ _ h => hi (Subtype.ext h)

/-- The probe labels number exactly `h+1` trace points. -/
theorem card_probeIndex : Fintype.card (ProbeIndex p) = Fintype.card (P × Bool) + 1 := by
  classical
  have hcard : Fintype.card {q : P // q ≠ p} = Fintype.card P - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun q : P => q = p))
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, hcard]
  have hp : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨p⟩
  omega

/-- A list of at most `h+1` probes can be selected without repetition. -/
theorem exists_selectedProbes (q : ℕ) (hq : q ≤ Fintype.card (P × Bool) + 1) :
    Nonempty (Fin q ↪ ProbeIndex p) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fin, card_probeIndex p]
  exact hq

section SelectedProbes

variable {q : ℕ} (e : Fin q ↪ ProbeIndex p)

/-- Vector evaluation at any selected list of probes in (A.4). -/
def canonicalSelectedEvaluation : (D).projectedPairSpace hc →ₗ[K] (Fin q → K × K) :=
  LinearMap.pi fun i => (D).projectedEvaluation hc (probePoint p layers (e i))

/-- Every vector value on a selected list extends to a value on all probes. -/
theorem canonicalSelectedEvaluation_surjective (hne : layers false ≠ layers true)
    (e : Fin q ↪ ProbeIndex p) :
    Function.Surjective (canonicalSelectedEvaluation K p layers e) := by
  intro v
  let y : ProbeIndex p → K × K := Function.extend e v 0
  obtain ⟨w, hw⟩ := (canonicalJointEvaluation_bijective K p layers hne).2
    (fun i => y (.inl i), fun a b => y (.inr (a, b)))
  refine ⟨w, ?_⟩
  have he (a : ProbeIndex p) : (D).projectedEvaluation hc (probePoint p layers a) w = y a := by
    cases a with
    | inl i => exact congrFun (congrArg Prod.fst hw) i
    | inr a => exact congrFun (congrFun (congrArg Prod.snd hw) a.1) a.2
  funext i
  rw [canonicalSelectedEvaluation, LinearMap.pi_apply, he]
  exact e.injective.extend_apply v 0 i

/-- The independent vector conditions on the selected probes have codimension `2q`. -/
theorem finrank_ker_canonicalSelectedEvaluation (hne : layers false ≠ layers true)
    (e : Fin q ↪ ProbeIndex p) :
    Module.finrank K (canonicalSelectedEvaluation K p layers e).ker =
      2 * Fintype.card (P × Bool) + 2 - 2 * q := by
  have htarget : finrank K (Fin q → K × K) = 2 * q := by
    simp [Module.finrank_pi_fintype]
    omega
  have h := (canonicalSelectedEvaluation K p layers e).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (canonicalSelectedEvaluation_surjective K p layers hne e),
    finrank_top, htarget, finrank_canonicalProjectedPairSpace K p layers hne] at h
  omega

/-- Scalar evaluation on the genuine quadratic flag ideal at the selected probes. -/
def selectedScalarEvaluation : quadraticFlagVanishing (K := K) (P := P) (J := J) →ₗ[K] (Fin q → K) :=
  LinearMap.pi fun i =>
    { toFun := fun f => eval (probePoint p layers (e i)) f.val.val
      map_add' f g := by simp
      map_smul' r f := by simp }

omit [CharZero K] [DecidableEq J] in
/-- The same selected probes impose independent scalar conditions on the flag ideal. -/
theorem selectedScalarEvaluation_surjective (hne : layers false ≠ layers true)
    (e : Fin q ↪ ProbeIndex p) :
    Function.Surjective (selectedScalarEvaluation K p layers e) := by
  intro v
  let y : ProbeIndex p → K := Function.extend e v 0
  obtain ⟨f, hf⟩ := flagProbeScalarEvaluation_surjective (K := K) p layers hne
    (fun i => y (.inl i), fun a b => y (.inr (a, b)))
  refine ⟨f, ?_⟩
  have he (a : ProbeIndex p) : eval (probePoint p layers a) f.val.val = y a := by
    cases a with
    | inl i => exact congrFun (congrArg Prod.fst hf) i
    | inr a => exact congrFun (congrFun (congrArg Prod.snd hf) a.1) a.2
  funext i
  change eval (probePoint p layers (e i)) f.val.val = v i
  rw [he]
  exact e.injective.extend_apply v 0 i

end SelectedProbes
end IdealGeneration.QuadraticCoreRestriction
