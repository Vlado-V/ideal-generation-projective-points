module

public import IdealGeneration.QuadraticFlagAssembly
public import IdealGeneration.QuadraticConeLinearEvaluation
public import IdealGeneration.QuadraticJointProbeEvaluation
public import Mathlib.Data.Sym.Card

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Scalar postulation for the actual quadratic trace labels

An unordered pair labels one base point. A repeated member labels its
coordinate point. Distinct members label the sum of their coordinate points.
The layer labels and the selected extra probes retain their actual coordinates.
-/

noncomputable section
namespace IdealGeneration.QuadraticTracePostulation
open MvPolynomial QuadraticFlag QuadraticElimination
open scoped Classical

variable {K I T E P J : Type*} [Field K]

/-- Scalar evaluation of homogeneous quadrics on an actual point family. -/
def quadraticEvaluation (x : E → T → K) : Quadrics K T →ₗ[K] (E → K) :=
  LinearMap.pi fun e => (aeval (x e)).toLinearMap.comp (homogeneousSubmodule T K 2).subtype

@[simp] theorem quadraticEvaluation_apply (x : E → T → K) (f : Quadrics K T) (e : E) :
    quadraticEvaluation x f e = eval (x e) f.val := by
  simp [quadraticEvaluation, aeval_eq_eval]

/-- The characteristic vector of the support of an unordered pair. -/
def baseLabelPoint (s : Sym2 I) : I → K := fun i => if i ∈ s then 1 else 0

@[simp] theorem baseLabelPoint_diag (i : I) :
    baseLabelPoint (K := K) (Sym2.diag i) = coordinatePoint i := by
  funext j
  simp [baseLabelPoint, coordinatePoint, Sym2.diag]

theorem baseLabelPoint_mk_off {i j : I} (hij : i ≠ j) :
    baseLabelPoint (K := K) (Sym2.mk i j) = coordinatePoint i + coordinatePoint j := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [baseLabelPoint, coordinatePoint, hij]
  · by_cases hj : k = j
    · subst k
      simp [baseLabelPoint, coordinatePoint, hi]
    · simp [baseLabelPoint, coordinatePoint, hi, hj]

/-- Distinct unordered labels have different affine representatives. -/
theorem baseLabelPoint_injective : Function.Injective (baseLabelPoint (K := K) (I := I)) := by
  intro s t h
  apply Sym2.ext
  intro i
  have he := congrFun h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [baseLabelPoint, hs, ht] at he ⊢

/-- The off-diagonal correction subtracts the two values already assigned by squares. -/
private def baseOffCorrection (a : Sym2 I → K) : Sym2 I → MvPolynomial I K :=
  Sym2.lift ⟨fun i j => if i = j then 0 else
    C (a (Sym2.mk i j) - a (Sym2.diag i) - a (Sym2.diag j)) * X i * X j, by
      intro i j
      by_cases hij : i = j
      · subst j
        simp
      · have h : a (Sym2.mk i j) - a (Sym2.diag i) - a (Sym2.diag j) =
            a (Sym2.mk j i) - a (Sym2.diag j) - a (Sym2.diag i) := by
          rw [Sym2.eq_swap (a := i) (b := j)]
          ring
        dsimp only
        rw [ite_eq_right hij, ite_eq_right (fun he : j = i => hij he.symm), h]
        ring⟩

private theorem baseOffCorrection_mk (a : Sym2 I → K) (i j : I) :
    baseOffCorrection a (Sym2.mk i j) = if i = j then 0 else
      C (a (Sym2.mk i j) - a (Sym2.diag i) - a (Sym2.diag j)) * X i * X j := rfl

private theorem baseOffCorrection_homogeneous (a : Sym2 I → K) (s : Sym2 I) :
    (baseOffCorrection a s).IsHomogeneous 2 := by
  refine Sym2.inductionOn s ?_
  intro i j
  rw [baseOffCorrection_mk]
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X _ _)

private theorem eval_baseOffCorrection_mk (a : Sym2 I → K) (s : Sym2 I)
    {i j : I} (hij : i ≠ j) :
    eval (baseLabelPoint s) (baseOffCorrection a (Sym2.mk i j)) =
      if Sym2.mk i j = s then a (Sym2.mk i j) - a (Sym2.diag i) - a (Sym2.diag j) else 0 := by
  rw [baseOffCorrection_mk, ite_eq_right hij, map_mul, map_mul, eval_C, eval_X, eval_X]
  by_cases h : Sym2.mk i j = s
  · subst s
    simp [baseLabelPoint]
  · have hn : ¬(i ∈ s ∧ j ∈ s) := fun hmem => h ((Sym2.mem_and_mem_iff hij).mp hmem).symm
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact (hn ⟨hi, hj⟩).elim
    · simp [baseLabelPoint, hi, hj, h]
    · simp [baseLabelPoint, hi, hj, h]
    · simp [baseLabelPoint, hi, hj, h]

private theorem eval_baseOffCorrection_off (a : Sym2 I → K) (s t : Sym2 I) (h : t ≠ s) :
    eval (baseLabelPoint s) (baseOffCorrection a t) = 0 := by
  induction t using Sym2.inductionOn with
  | _ i j =>
    by_cases hij : i = j
    · simp [baseOffCorrection_mk, hij]
    · rw [eval_baseOffCorrection_mk a s hij, ite_eq_right h]

variable [Fintype I]

private def baseInterpolation (a : Sym2 I → K) : MvPolynomial I K :=
  (∑ i, C (a (Sym2.diag i)) * X i ^ 2) + ∑ s, baseOffCorrection a s

private theorem baseInterpolation_homogeneous (a : Sym2 I → K) :
    (baseInterpolation a).IsHomogeneous 2 := by
  apply IsHomogeneous.add
  · exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X_pow _ _ _)
  · exact IsHomogeneous.sum _ _ _ (fun s _ => baseOffCorrection_homogeneous a s)

private theorem eval_baseInterpolation (a : Sym2 I → K) (s : Sym2 I) :
    eval (baseLabelPoint s) (baseInterpolation a) = a s := by
  simp only [baseInterpolation, map_add, map_sum, map_mul, eval_C, map_pow, eval_X]
  rw [Finset.sum_eq_single s (fun t _ ht => eval_baseOffCorrection_off a s t ht)
    (fun h => (h (Finset.mem_univ s)).elim)]
  induction s using Sym2.inductionOn with
  | _ i j =>
    by_cases hij : i = j
    · subst j
      change (∑ k, a (Sym2.diag k) * (baseLabelPoint (Sym2.diag i) k)^2) +
        eval (baseLabelPoint (Sym2.diag i)) (baseOffCorrection a (Sym2.mk i i)) = a (Sym2.diag i)
      simp [baseLabelPoint_diag, coordinatePoint, baseOffCorrection_mk, mul_ite]
    · rw [eval_baseOffCorrection_mk a (Sym2.mk i j) hij, ite_eq_left rfl]
      have hs : (∑ k, a (Sym2.diag k) * (baseLabelPoint (Sym2.mk i j) k)^2) =
          a (Sym2.diag i) + a (Sym2.diag j) := by
        calc
          _ = ∑ k ∈ ({i, j} : Finset I), a (Sym2.diag k) * (baseLabelPoint (Sym2.mk i j) k)^2 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro k _ hk
            have hk' : k ∉ Sym2.mk i j := by simpa only [Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff] using hk
            simp [baseLabelPoint, hk']
          _ = _ := by simp [Finset.sum_insert, hij, baseLabelPoint]
      rw [hs]
      ring

/-- Coordinate points and unordered coordinate sums interpolate all base values. -/
theorem baseLabelEvaluation_surjective :
    Function.Surjective (quadraticEvaluation (baseLabelPoint (K := K) (I := I))) := by
  intro a
  refine ⟨⟨baseInterpolation a, baseInterpolation_homogeneous a⟩, ?_⟩
  funext s
  rw [quadraticEvaluation_apply]
  exact eval_baseInterpolation a s

/-- The base labels have exactly the quadratic monomial count. -/
theorem card_baseLabel : Fintype.card (Sym2 I) = N (Fintype.card I) 2 := by
  rw [Sym2.card, N, show Fintype.card I + 2 - 1 = Fintype.card I + 1 by omega]

/-- One label per actual flag point. -/
abbrev FlagLabel (P J : Type*) := Sym2 (P × Bool) ⊕ (J ⊕ (P × J))

/-- The full trace representatives of the flag labels. -/
def flagLabelPoint : FlagLabel P J → (P × Bool) ⊕ J → K
  | .inl s => Sum.elim (baseLabelPoint s) (fun _ => 0)
  | .inr (.inl j) => layerPoint j
  | .inr (.inr (p, j)) => pairedLayerPoint p j

@[simp] theorem flagLabelPoint_diag (i : P × Bool) :
    flagLabelPoint (K := K) (J := J) (.inl (Sym2.diag i)) = traceBasePoint i := by
  funext k
  cases k with
  | inl k => by_cases hk : k = i <;>
      simp [flagLabelPoint, traceBasePoint, baseLabelPoint, coordinatePoint, Sym2.diag, hk]
  | inr k => simp [flagLabelPoint, traceBasePoint]

private theorem traceBasePoint_eq_flagPoint (i : P × Bool) :
    traceBasePoint (K := K) (J := J) i = flagPoint (.base i) := by
  funext k
  cases k <;> simp [traceBasePoint, flagPoint, coordinatePoint]

private theorem flagLabelPoint_off_eq_flagPoint {i j : P × Bool} (hij : i ≠ j) :
    flagLabelPoint (K := K) (J := J) (.inl (Sym2.mk i j)) = flagPoint (.basePair i j) := by
  simp only [flagLabelPoint, baseLabelPoint_mk_off hij]
  funext k
  cases k with
  | inl k => by_cases h₀ : k = i <;> by_cases h₁ : k = j <;>
      simp [flagPoint, coordinatePoint, h₀, h₁]
  | inr k => simp [flagPoint, coordinatePoint]

private theorem layerPoint_eq_flagPoint (j : J) :
    layerPoint (K := K) (P := P) j = flagPoint (.layer j) := by
  funext k
  cases k <;> simp [layerPoint, flagPoint, coordinatePoint]

private theorem pairedLayerPoint_eq_flagPoint (p : P) (j : J) :
    pairedLayerPoint (K := K) p j = flagPoint (.layerPair p j) := by
  funext k
  cases k <;> simp [pairedLayerPoint, flagPoint, pairPoint, coordinatePoint]

/-- Evaluation at all the distinct flag labels. -/
def flagLabelEvaluation : Quadrics K ((P × Bool) ⊕ J) →ₗ[K] (FlagLabel P J → K) :=
  quadraticEvaluation flagLabelPoint

/-- Interpolation on the base and the existing layer extension give full flag evaluation. -/
theorem flagLabelEvaluation_surjective [Fintype P] [Fintype J] :
    Function.Surjective (flagLabelEvaluation (K := K) (P := P) (J := J)) := by
  intro v
  obtain ⟨g, hg⟩ := baseLabelEvaluation_surjective (K := K) (I := P × Bool) (fun s => v (.inl s))
  let d : ScalarFlagData (K := K) (P := P) (J := J) :=
    (g, (fun j => v (.inr (.inl j)), fun q => v (.inr (.inr q))))
  obtain ⟨f, hf⟩ := scalarFlagEvaluation_surjective d
  refine ⟨f, ?_⟩
  funext t
  simp only [flagLabelEvaluation, quadraticEvaluation_apply]
  cases t with
  | inl s =>
    change eval (Sum.elim (baseLabelPoint s) (fun _ : J => 0)) f.val = v (.inl s)
    rw [← eval_restrictBase]
    change eval (baseLabelPoint s) (scalarFlagEvaluation f).1.val = v (.inl s)
    rw [congrArg Prod.fst hf]
    simpa only [quadraticEvaluation_apply] using congrFun hg s
  | inr t =>
    cases t with
    | inl j => exact congrFun (congrArg (fun u => u.2.1) hf) j
    | inr q => exact congrFun (congrArg (fun u => u.2.2) hf) q

/-- The distinct label family and the original flag define the same vanishing space. -/
theorem flagLabelEvaluation_ker :
    (flagLabelEvaluation (K := K) (P := P) (J := J)).ker = quadraticFlagVanishing := by
  ext f
  change flagLabelEvaluation f = 0 ↔ ∀ t : FlagIndex P J, eval (flagPoint t) f.val = 0
  rw [funext_iff]
  simp only [flagLabelEvaluation, quadraticEvaluation_apply, Pi.zero_apply]
  constructor
  · intro h t
    cases t with
    | base i =>
      rw [← traceBasePoint_eq_flagPoint, ← flagLabelPoint_diag]
      exact h (.inl (Sym2.diag i))
    | basePair i j =>
      by_cases hij : i = j
      · subst j
        have h₀ : eval (coordinatePoint (Sum.inl i)) f.val = 0 := by
          change eval (flagPoint (.base i)) f.val = 0
          rw [← traceBasePoint_eq_flagPoint, ← flagLabelPoint_diag]
          exact h (.inl (Sym2.diag i))
        have hs := homogeneous_eval_scale f.property (coordinatePoint (Sum.inl i)) (2 : K)
        rw [h₀, mul_zero] at hs
        have hp : (fun k : (P × Bool) ⊕ J => (2 : K) * coordinatePoint (Sum.inl i) k) =
            flagPoint (.basePair i i) := by
          funext k
          by_cases hk : k = Sum.inl i <;> norm_num [flagPoint, coordinatePoint, hk]
        rw [hp] at hs
        exact hs
      · rw [← flagLabelPoint_off_eq_flagPoint hij]
        exact h (.inl (Sym2.mk i j))
    | layer j =>
      rw [← layerPoint_eq_flagPoint]
      exact h (.inr (.inl j))
    | layerPair p j =>
      rw [← pairedLayerPoint_eq_flagPoint]
      exact h (.inr (.inr (p, j)))
  · intro h t
    cases t with
    | inl s =>
      induction s using Sym2.inductionOn with
      | _ i j =>
        by_cases hij : i = j
        · subst j
          change eval (flagLabelPoint (.inl (Sym2.diag i))) f.val = 0
          rw [flagLabelPoint_diag, traceBasePoint_eq_flagPoint]
          exact h (.base i)
        · rw [flagLabelPoint_off_eq_flagPoint hij]
          exact h (.basePair i j)
    | inr t =>
      cases t with
      | inl j =>
        change eval (layerPoint j) f.val = 0
        rw [layerPoint_eq_flagPoint]
        exact h (.layer j)
      | inr q =>
        change eval (pairedLayerPoint q.1 q.2) f.val = 0
        rw [pairedLayerPoint_eq_flagPoint]
        exact h (.layerPair q.1 q.2)

/-- The flag has exactly its prescribed scalar condition count. -/
theorem card_flagLabel [Fintype P] [Fintype J] :
    Fintype.card (FlagLabel P J) = flagCount (Fintype.card (P × Bool)) (Fintype.card J) := by
  rw [Fintype.card_sum, Fintype.card_sum, card_baseLabel, Fintype.card_prod P J, flagCount]
  have hh : Fintype.card (P × Bool) / 2 = Fintype.card P := by
    rw [Fintype.card_prod, Fintype.card_bool]
    omega
  rw [hh]
  ring

/-- The marked trace supports of the actual cone points. -/
def coneFlagLabel (p₀ : P) : ConeIndex P J → FlagLabel P J
  | .inl i => .inl (Sym2.diag i)
  | .inr (j, false) => .inr (.inl j)
  | .inr (j, true) => .inr (.inr (p₀, j))

@[simp] theorem flagLabelPoint_coneFlagLabel (D : QuadraticLiftParameters K P J) (z : ConeIndex P J) :
    flagLabelPoint (coneFlagLabel D.distinguishedPair z) = D.coneTracePoint z := by
  cases z with
  | inl i => exact flagLabelPoint_diag i
  | inr q => rcases q with ⟨j, b⟩; cases b <;> rfl

/-- Trace labels are the flag labels and an arbitrary finite family of extra probes. -/
abbrev TraceLabel (P J E : Type*) := FlagLabel P J ⊕ E

/-- Evaluate the flag and the selected extra representatives in their native labels. -/
def traceLabelPoint (probes : E → (P × Bool) ⊕ J → K) : TraceLabel P J E → (P × Bool) ⊕ J → K :=
  Sum.elim flagLabelPoint probes

/-- Scalar evaluation on the combined trace family. -/
def traceLabelEvaluation (probes : E → (P × Bool) ⊕ J → K) :
    Quadrics K ((P × Bool) ⊕ J) →ₗ[K] (TraceLabel P J E → K) :=
  quadraticEvaluation (traceLabelPoint probes)

/-- After fitting the flag, correct the remaining values in its vanishing space. -/
theorem traceLabelEvaluation_surjective [Fintype P] [Fintype J]
    (probes : E → (P × Bool) ⊕ J → K)
    (hprobes : Function.Surjective ((quadraticEvaluation probes).comp
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).subtype)) :
    Function.Surjective (traceLabelEvaluation probes) := by
  intro v
  obtain ⟨f, hf⟩ := flagLabelEvaluation_surjective (K := K) (P := P) (J := J) (fun s => v (.inl s))
  obtain ⟨g, hg⟩ := hprobes (fun e => v (.inr e) - quadraticEvaluation probes f e)
  have hz : flagLabelEvaluation g.val = 0 := by
    apply LinearMap.mem_ker.mp
    rw [flagLabelEvaluation_ker]
    exact g.property
  refine ⟨f + g.val, ?_⟩
  funext t
  cases t with
  | inl s =>
    change flagLabelEvaluation (f + g.val) s = v (.inl s)
    rw [map_add, hf, hz]
    simp
  | inr e =>
    change quadraticEvaluation probes (f + g.val) e = v (.inr e)
    have he := congrFun hg e
    change quadraticEvaluation probes g.val e = v (.inr e) - quadraticEvaluation probes f e at he
    rw [map_add, Pi.add_apply, he]
    abel

/-- The combined kernel records the actual flag and the actual extra probes. -/
theorem traceLabelEvaluation_ker (probes : E → (P × Bool) ⊕ J → K) :
    (traceLabelEvaluation probes).ker = quadraticFlagVanishing ⊓ (quadraticEvaluation probes).ker := by
  rw [← flagLabelEvaluation_ker]
  ext f
  change traceLabelEvaluation probes f = 0 ↔
    flagLabelEvaluation f = 0 ∧ quadraticEvaluation probes f = 0
  constructor
  · intro h
    exact ⟨funext fun s => congrFun h (.inl s), funext fun e => congrFun h (.inr e)⟩
  · rintro ⟨h₀, h₁⟩
    funext t
    cases t with
    | inl s => exact congrFun h₀ s
    | inr e => exact congrFun h₁ e

/-- The combined trace count is the flag count plus the number of extra probes. -/
theorem card_traceLabel [Fintype P] [Fintype J] [Fintype E] :
    Fintype.card (TraceLabel P J E) = flagCount (Fintype.card (P × Bool)) (Fintype.card J) +
      Fintype.card E := by
  rw [Fintype.card_sum, card_flagLabel]

/-- An independently interpolated quadratic point cannot be the zero vector. -/
theorem point_ne_zero_of_quadraticEvaluation_surjective (x : E → T → K)
    (hx : Function.Surjective (quadraticEvaluation x)) (e : E) : x e ≠ 0 := by
  intro hz
  obtain ⟨f, hf⟩ := hx (fun _ => 1)
  have h := congrFun hf e
  simp only [quadraticEvaluation_apply, hz, eval_zero_quadratic] at h
  exact zero_ne_one h

/-- The actual selected probes from (A.4), including the first-layer subset,
can be adjoined to the flag with full scalar evaluation. -/
theorem selectedTraceLabelEvaluation_surjective [Fintype P] [Fintype J] {q : ℕ}
    (p₀ : P) (layers : Bool → J) (hne : layers false ≠ layers true)
    (e : Fin q ↪ QuadraticFlagProbeScalar.ProbeIndex p₀) :
    Function.Surjective (traceLabelEvaluation (K := K)
      (fun i => QuadraticFlagProbeScalar.probePoint p₀ layers (e i))) := by
  apply traceLabelEvaluation_surjective
  intro v
  obtain ⟨f, hf⟩ := QuadraticCoreRestriction.selectedScalarEvaluation_surjective K p₀ layers hne e v
  refine ⟨f, ?_⟩
  funext i
  change quadraticEvaluation (fun j => QuadraticFlagProbeScalar.probePoint p₀ layers (e j)) f.val i = v i
  rw [quadraticEvaluation_apply]
  exact congrFun hf i

/-- Relabelling the point family preserves its scalar interpolation property. -/
theorem quadraticEvaluation_reindex_surjective {L : Type*} (x : E → T → K) (e : L ≃ E)
    (hx : Function.Surjective (quadraticEvaluation x)) :
    Function.Surjective (quadraticEvaluation (x ∘ e)) := by
  intro v
  obtain ⟨f, hf⟩ := hx (v ∘ e.symm)
  refine ⟨f, ?_⟩
  funext i
  have h := congrFun hf (e i)
  simpa only [quadraticEvaluation_apply, Function.comp_apply, Equiv.symm_apply_apply] using h

/-- One core probe and one first-layer probe for every untouched pair. -/
abbrev FirstLayerProbeLabel (p₀ : P) := Unit ⊕ {p : P // p ≠ p₀}

/-- The A.3 probes are an actual subset of the A.4 probe family. -/
def firstLayerProbeEmbedding (p₀ : P) : FirstLayerProbeLabel p₀ ↪ QuadraticFlagProbeScalar.ProbeIndex p₀ where
  toFun
    | .inl _ => .inl 0
    | .inr p => .inr (p, false)
  inj' := by
    rintro (u | p) (v | q) h
    · cases u
      cases v
      rfl
    · cases h
    · cases h
    · exact congrArg Sum.inr (congrArg Prod.fst (Sum.inr.inj h))

/-- The distinguished core point is the first-layer probe of its pair. -/
@[simp] theorem firstLayerProbeEmbedding_core (p₀ : P) (layers : Bool → J) :
    QuadraticFlagProbeScalar.probePoint (K := K) p₀ layers
      (firstLayerProbeEmbedding p₀ (.inl ())) = QuadraticLiftParameters.pairProbe p₀ (layers false) := rfl

@[simp] theorem firstLayerProbeEmbedding_untouched (p₀ : P) (layers : Bool → J)
    (p : {q : P // q ≠ p₀}) :
    QuadraticFlagProbeScalar.probePoint (K := K) p₀ layers
      (firstLayerProbeEmbedding p₀ (.inr p)) = QuadraticLiftParameters.pairProbe p.val (layers false) := rfl

/-- The injective endpoint adds exactly one scalar point per base pair. -/
theorem card_firstLayerProbeLabel [Fintype P] (p₀ : P) :
    Fintype.card (FirstLayerProbeLabel p₀) = Fintype.card P := by
  have hcard : Fintype.card {p : P // p ≠ p₀} = Fintype.card P - 1 := by
    simpa only [Fintype.card_subtype_eq] using (Fintype.card_subtype_compl (fun p : P => p = p₀))
  rw [Fintype.card_sum, Fintype.card_unit, hcard]
  have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨p₀⟩
  omega

/-- The A.3 probe family with its prescribed finite count. -/
def firstLayerProbeSelection [Fintype P] (p₀ : P) : Fin (Fintype.card P) ↪ QuadraticFlagProbeScalar.ProbeIndex p₀ :=
  (Fintype.equivFinOfCardEq (card_firstLayerProbeLabel p₀)).symm.toEmbedding.trans
    (firstLayerProbeEmbedding p₀)

end IdealGeneration.QuadraticTracePostulation
