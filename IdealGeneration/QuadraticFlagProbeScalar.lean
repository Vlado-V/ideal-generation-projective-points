module

public import IdealGeneration.QuadraticPairProjection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Scalar independence of the actual probes in (A.4). -/

noncomputable section
namespace IdealGeneration.QuadraticFlagProbeScalar
open MvPolynomial QuadraticFlag
open QuadraticElimination.QuadraticLiftParameters
open scoped Classical

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

/-- The third core probe, with just the two layer coordinates. -/
def layerPairProbe (layers : Bool → J) : (P × Bool) ⊕ J → K :=
  coordinatePoint (.inr (layers false)) + coordinatePoint (.inr (layers true))

/-- The three core probes, placed in the full trace coordinate space. -/
def flagCoreProbes (p₀ : P) (layers : Bool → J) : Fin 3 → (P × Bool) ⊕ J → K :=
  ![pairProbe p₀ (layers false), pairProbe p₀ (layers true), layerPairProbe layers]

omit [Fintype P] [Fintype J] in
/-- The core probes are supported away from all untouched base coordinates. -/
theorem flagCoreProbes_apply_of_ne (p₀ p : P) (hp : p ≠ p₀) (layers : Bool → J)
    (i : Fin 3) (b : Bool) : flagCoreProbes (K := K) p₀ layers i (.inl (p, b)) = 0 := by
  fin_cases i <;> simp [flagCoreProbes, pairProbe, layerPairProbe, coordinatePoint, hp]

/-- A scalar flag equation for one pair and one selected layer. -/
def contrastBasis (layers : Bool → J) (p : P) (b : Bool) :
    quadraticFlagVanishing (K := K) (P := P) (J := J) :=
  ⟨⟨pairContrast (p, false) (coordinatePoint (layers b)), pairContrast_homogeneous _ _⟩,
    pairContrast_mem_flagVanishing _ _⟩

/-- The product of the two selected layer variables is the third core equation. -/
def crossLayerPolynomial (layers : Bool → J) : MvPolynomial ((P × Bool) ⊕ J) K :=
  X (.inr (layers false)) * X (.inr (layers true))

omit [Fintype P] [Fintype J] in
theorem crossLayerPolynomial_mem_flagVanishing (layers : Bool → J)
    (h : layers false ≠ layers true) :
    crossLayerPolynomial (K := K) (P := P) layers ∈ flagVanishing := by
  change ∀ t, eval (flagPoint t) (crossLayerPolynomial layers) = 0
  intro t
  cases t with
  | base i => simp [flagPoint, crossLayerPolynomial, coordinatePoint]
  | basePair i k => simp [flagPoint, crossLayerPolynomial, coordinatePoint]
  | layer j =>
    by_cases hj : layers false = j
    · have hn : layers true ≠ j := fun he => h (hj.trans he.symm)
      simp [flagPoint, crossLayerPolynomial, coordinatePoint, hj, hn]
    · simp [flagPoint, crossLayerPolynomial, coordinatePoint, hj]
  | layerPair p j =>
    by_cases hj : layers false = j
    · have hn : layers true ≠ j := fun he => h (hj.trans he.symm)
      simp [flagPoint, crossLayerPolynomial, coordinatePoint, hj, hn]
    · simp [flagPoint, crossLayerPolynomial, coordinatePoint, hj]

/-- The cross-layer equation, as an element of the actual quadratic flag ideal. -/
def crossLayerBasis (layers : Bool → J) (h : layers false ≠ layers true) :
    quadraticFlagVanishing (K := K) (P := P) (J := J) :=
  ⟨⟨crossLayerPolynomial layers,
    (isHomogeneous_X K (Sum.inr (layers false))).mul
      (isHomogeneous_X K (Sum.inr (layers true)))⟩,
    crossLayerPolynomial_mem_flagVanishing layers h⟩

omit [Fintype J] in
private theorem layers_injective (layers : Bool → J) (h : layers false ≠ layers true) :
    Function.Injective layers := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · exact (h hij).elim
  · exact (h hij.symm).elim
  · rfl

omit [Fintype P] in
@[simp] theorem eval_contrastBasis_pairProbe (layers : Bool → J) (h : layers false ≠ layers true)
    (p q : P) (b c : Bool) :
    eval (pairProbe q (layers c)) (contrastBasis (K := K) layers p b).val.val =
      if (q, c) = (p, b) then 1 else 0 := by
  change eval (pairProbe q (layers c)) (pairContrast (p, false) (coordinatePoint (layers b))) = _
  rw [eval_pairContrast_pairProbe]
  have hinj := layers_injective layers h
  by_cases hp : p = q <;> by_cases hb : b = c <;>
    simp [coordinatePoint, hinj.eq_iff, hp, Ne.symm, hb, eq_comm]

omit [Fintype P] in
@[simp] theorem eval_contrastBasis_layerPairProbe (layers : Bool → J) (p : P) (b : Bool) :
    eval (layerPairProbe layers) (contrastBasis (K := K) layers p b).val.val = 0 := by
  apply eval_pairContrast_eq_zero_of_same
  simp [layerPairProbe, coordinatePoint, partner]

omit [Fintype P] [Fintype J] in
@[simp] theorem eval_crossLayerBasis_pairProbe (layers : Bool → J) (h : layers false ≠ layers true)
    (p : P) (c : Bool) :
    eval (pairProbe p (layers c)) (crossLayerBasis (K := K) (P := P) layers h).val.val = 0 := by
  cases c <;> simp [pairProbe, crossLayerBasis, crossLayerPolynomial, coordinatePoint, h, Ne.symm]

omit [Fintype P] [Fintype J] in
@[simp] theorem eval_crossLayerBasis_layerPairProbe (layers : Bool → J)
    (h : layers false ≠ layers true) :
    eval (layerPairProbe layers) (crossLayerBasis (K := K) (P := P) layers h).val.val = 1 := by
  simp [layerPairProbe, crossLayerBasis, crossLayerPolynomial, coordinatePoint, h, Ne.symm]

/-- The probe labels separate the three core probes from the two probes on each other pair. -/
abbrev ProbeIndex (p₀ : P) := Fin 3 ⊕ ({p : P // p ≠ p₀} × Bool)

/-- The full actual family of probes. -/
def probePoint (p₀ : P) (layers : Bool → J) : ProbeIndex p₀ → (P × Bool) ⊕ J → K
  | .inl i => flagCoreProbes p₀ layers i
  | .inr (p, b) => pairProbe p.val (layers b)

/-- Explicit scalar interpolation quadrics, indexed by the probes. -/
def probeBasis (p₀ : P) (layers : Bool → J) (h : layers false ≠ layers true) :
    ProbeIndex p₀ → quadraticFlagVanishing (K := K) (P := P) (J := J)
  | .inl i => ![contrastBasis layers p₀ false, contrastBasis layers p₀ true, crossLayerBasis layers h] i
  | .inr (p, b) => contrastBasis layers p.val b

omit [Fintype P] in
/-- The explicit scalar equations have the identity evaluation matrix. -/
theorem eval_probeBasis (p₀ : P) (layers : Bool → J) (h : layers false ≠ layers true)
    (a b : ProbeIndex p₀) :
    eval (probePoint p₀ layers a) (probeBasis (K := K) p₀ layers h b).val.val =
      if a = b then 1 else 0 := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      fin_cases i <;> fin_cases j <;> simp [probePoint, flagCoreProbes, probeBasis, h]
    | inr q =>
      rcases q with ⟨q, c⟩
      fin_cases i <;>
        simp [probePoint, flagCoreProbes, probeBasis, h, q.property, Ne.symm]
  | inr t =>
    rcases t with ⟨p, d⟩
    cases b with
    | inl j =>
      fin_cases j <;>
        simp [probePoint, probeBasis, h, p.property, Ne.symm]
    | inr q =>
      rcases q with ⟨q, c⟩
      simp [probePoint, probeBasis, h, Prod.ext_iff, Subtype.ext_iff]

/-- The scalar evaluation map at every probe from (A.4). -/
def flagProbeScalarEvaluation (p₀ : P) (layers : Bool → J) :
    quadraticFlagVanishing (K := K) (P := P) (J := J) →ₗ[K]
      ((Fin 3 → K) × ({p : P // p ≠ p₀} → Bool → K)) where
  toFun f := (fun i => eval (flagCoreProbes p₀ layers i) f.val.val,
    fun p b => eval (pairProbe p.val (layers b)) f.val.val)
  map_add' f g := by apply Prod.ext <;> funext <;> simp
  map_smul' r f := by apply Prod.ext <;> funext <;> simp

/-- All scalar values on the core and untouched probes can be prescribed. -/
theorem flagProbeScalarEvaluation_surjective (p₀ : P) (layers : Bool → J)
    (h : layers false ≠ layers true) :
    Function.Surjective (flagProbeScalarEvaluation (K := K) p₀ layers) := by
  rintro ⟨v, w⟩
  let coeff : ProbeIndex p₀ → K := Sum.elim v (fun p => w p.1 p.2)
  refine ⟨∑ b, coeff b • probeBasis p₀ layers h b, ?_⟩
  have he (a : ProbeIndex p₀) :
      eval (probePoint p₀ layers a)
        (∑ b, coeff b • probeBasis p₀ layers h b :
          quadraticFlagVanishing (K := K) (P := P) (J := J)).val.val = coeff a := by
    cases a <;> simp [eval_probeBasis p₀ layers h]
  apply Prod.ext
  · funext i
    exact he (.inl i)
  · funext p b
    exact he (.inr (p, b))

end IdealGeneration.QuadraticFlagProbeScalar
