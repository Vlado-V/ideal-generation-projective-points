module

public import IdealGeneration.ResponseSelection
public import IdealGeneration.PolynomialTransversality
public import IdealGeneration.ScalarProductTrace
public import IdealGeneration.PointAvoidance
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Selecting scalar conditions

An injective family of scalar evaluations contains every required smaller
independent family, and every required larger family separating the source.
The point condition is allowed to depend on the whole configuration because
the polynomial open condition is imposed on the full product space first.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

section Rows
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Evaluation at a selected subset of the available scalar conditions. -/
def selectedScalarEvaluation (α : ι → Module.Dual K V) (s : Finset ι) :
    V →ₗ[K] (s → K) := LinearMap.pi (fun i => α i)

/-- Any injective family of scalar evaluations spans the dual space. -/
theorem scalarRows_span_of_injective (α : ι → Module.Dual K V)
    (hα : Function.Injective (LinearMap.pi α)) :
    Submodule.span K (Set.range α) = ⊤ := by
  have : Module.IsReflexive K V := Module.IsReflexive.of_finite_of_free K V
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  by_contra! h
  apply hv
  apply hα
  ext i
  simpa using h (α i) ⟨i, rfl⟩

/-- Choose a prescribed number of independent rows of an injective evaluation. -/
theorem exists_independent_scalar_rows (α : ι → Module.Dual K V)
    (hα : Function.Injective (LinearMap.pi α)) (q : ℕ)
    (hq : q ≤ finrank K V) :
    ∃ s : Finset ι, s.card = q ∧
      LinearIndependent K (fun i : s => α i) := by
  classical
  obtain ⟨a, ha⟩ := exists_independent_list_of_spanning α
    (scalarRows_span_of_injective α hα) q (by simpa using hq)
  have hai : Function.Injective a := fun i j hij => ha.injective (congrArg α hij)
  let s : Finset ι := Finset.univ.image a
  have hs : s.card = q := by simp [s, Finset.card_image_of_injective _ hai]
  let b : Fin q → s := fun i => ⟨a i, by simp [s]⟩
  have hb : Function.Bijective b := by
    constructor
    · intro i j hij
      exact hai (congrArg Subtype.val hij)
    · rintro ⟨i, hi⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      exact ⟨j, Subtype.ext hj⟩
  refine ⟨s, hs, ?_⟩
  exact (linearIndependent_equiv (Equiv.ofBijective b hb)).mp ha

/-- A spanning family of scalar rows separates the source. -/
theorem scalarEvaluation_injective_of_span (α : ι → Module.Dual K V)
    (hα : Submodule.span K (Set.range α) = ⊤) :
    Function.Injective (LinearMap.pi α) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hvan : ∀ f ∈ Submodule.span K (Set.range α), f v = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact congrFun hv i
    | zero => simp
    | add f g _ _ hf hg => simp [hf, hg]
    | smul c f _ hf => simp [hf]
  have hsep : ∀ f : Module.Dual K V, f v = 0 := fun f => hvan f (by rw [hα]; trivial)
  exact (Module.forall_dual_apply_eq_zero_iff K v).mp hsep

/-- With at least the source dimension many rows, select any requested number
and retain an injective evaluation. -/
theorem exists_injective_scalar_rows [Fintype ι] (α : ι → Module.Dual K V)
    (hα : Function.Injective (LinearMap.pi α)) (q : ℕ)
    (hq : finrank K V ≤ q) (hcard : q ≤ Fintype.card ι) :
    ∃ s : Finset ι, s.card = q ∧
      Function.Injective (selectedScalarEvaluation α s) := by
  classical
  obtain ⟨s, hs, hLI⟩ := exists_independent_scalar_rows α hα (finrank K V) le_rfl
  have hspan : Submodule.span K (Set.range (fun i : s => α i)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hLI, Fintype.card_coe, hs]
    exact (Subspace.dual_finrank_eq (K := K) (V := V)).symm
  obtain ⟨t, hst, _, ht⟩ := Finset.exists_subsuperset_card_eq (n := q)
    (Finset.subset_univ s) (by omega) (by simpa using hcard)
  refine ⟨t, ht, ?_⟩
  apply scalarEvaluation_injective_of_span
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, hst i.property⟩, rfl⟩

/-- The row-selection conclusion, including the equality case. -/
theorem scalar_row_selection [Fintype ι] (α : ι → Module.Dual K V)
    (hα : Function.Injective (LinearMap.pi α)) (q : ℕ)
    (hq : q ≤ Fintype.card ι) :
    ∃ s : Finset ι, s.card = q ∧
      (q ≤ finrank K V → LinearIndependent K (fun i : s => α i)) ∧
      (finrank K V ≤ q → Function.Injective (selectedScalarEvaluation α s)) := by
  classical
  by_cases hsmall : q ≤ finrank K V
  · obtain ⟨s, hs, hLI⟩ := exists_independent_scalar_rows α hα q hsmall
    refine ⟨s, hs, fun _ => hLI, fun hlarge => ?_⟩
    apply scalarEvaluation_injective_of_span
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hLI, Fintype.card_coe, hs]
    have heq : q = finrank K V := Nat.le_antisymm hsmall hlarge
    rw [heq, Subspace.dual_finrank_eq]
  · obtain ⟨s, hs, hinj⟩ := exists_injective_scalar_rows α hα q (by omega) hq
    exact ⟨s, hs, fun h => (hsmall h).elim, fun _ => hinj⟩
end Rows

section PartialCondition
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- Apply a single nonzero evaluation to each vector component. -/
def componentScalarEvaluation (e : W →ₗ[K] K) (m : ℕ) :
    (Fin m → W) →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => e.comp (LinearMap.proj i))

/-- A nonzero scalar evaluation permits arbitrary vector values. -/
theorem componentScalarEvaluation_surjective (e : W →ₗ[K] K)
    (he : ∃ w, e w ≠ 0) (m : ℕ) :
    Function.Surjective (componentScalarEvaluation e m) := by
  obtain ⟨w, hw⟩ := he
  intro y
  refine ⟨fun i => ((e w)⁻¹ * y i) • w, ?_⟩
  ext i
  simp [componentScalarEvaluation, mul_assoc, mul_left_comm, hw]

/-- The vector values required to lie in a prescribed partial fiber. -/
def partialScalarSpace (e : W →ₗ[K] K) {m : ℕ}
    (L : Submodule K (Fin m → K)) : Submodule K (Fin m → W) :=
  L.comap (componentScalarEvaluation e m)

/-- A partial point condition has its exact expected codimension. -/
theorem finrank_partialScalarSpace [FiniteDimensional K W] (e : W →ₗ[K] K)
    (he : ∃ w, e w ≠ 0) {m : ℕ} (L : Submodule K (Fin m → K)) :
    finrank K (partialScalarSpace e L) =
      m * finrank K W - (m - finrank K L) := by
  let f := L.mkQ.comp (componentScalarEvaluation e m)
  have hf : Function.Surjective f :=
    L.mkQ_surjective.comp (componentScalarEvaluation_surjective e he m)
  have hk : f.ker = partialScalarSpace e L := by
    ext g
    exact Submodule.Quotient.mk_eq_zero L
  have hr : finrank K f.range = m - finrank K L := by
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    have h := L.finrank_quotient_add_finrank
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Module.finrank_self, mul_one] at h
    omega
  have h := f.finrank_range_add_finrank_ker
  rw [hk, hr] at h
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  omega
end PartialCondition

section ResidualConditions
variable {K : Type*} [Field K] {n z p d : ℕ}

/-- Evaluation of a residual equation at a point of the hyperplane. -/
def residualPointValue (a : PointCoordinates K (n + 1) z) (d : ℕ)
    (y : Fin (n + 1) → K) : pointPolynomialPiece a d →ₗ[K] K where
  toFun w := eval (Fin.cons 0 y) w.val
  map_add' w v := map_add _ _ _
  map_smul' c w := by simp

/-- The residual tuples satisfying the prescribed partial condition at `y`. -/
def residualPartialSpace (a : PointCoordinates K (n + 1) z) (d : ℕ)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :
    Submodule K (Fin (n + 1) → pointPolynomialPiece a d) :=
  partialScalarSpace (residualPointValue a d y) L

@[simp] theorem mem_residualPartialSpace (a : PointCoordinates K (n + 1) z)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (g : Fin (n + 1) → pointPolynomialPiece a d) :
    g ∈ residualPartialSpace a d y L ↔
      (fun i => eval (Fin.cons 0 y) (g i).val) ∈ L := Iff.rfl

/-- The scalar condition obtained by evaluating the tangential product. -/
def residualScalarRow (a : PointCoordinates K (n + 1) z) (d : ℕ)
    (P : PointCoordinates K n p) (i : Fin p) :
    (Fin (n + 1) → pointPolynomialPiece a d) →ₗ[K] K :=
  (evaluationLinear K (n + 1) (d + 1) (chartPoint K P i)).comp
    (tangentPointProductForm a d)

/-- The scalar row is the pointwise tangential dot product in the paper. -/
@[simp] theorem residualScalarRow_apply (a : PointCoordinates K (n + 1) z)
    (P : PointCoordinates K n p) (i : Fin p)
    (g : Fin (n + 1) → pointPolynomialPiece a d) :
    residualScalarRow a d P i g =
      ∑ j, chartPoint K P i j * eval (Fin.cons 0 (chartPoint K P i)) (g j).val := by
  simp [residualScalarRow, evaluationLinear, tangentPointProductForm,
    tangentPointProduct, eval_hyperplaneRestrict]

local instance residualPartialGroup (a : PointCoordinates K (n + 1) z)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)) :
    AddCommGroup (residualPartialSpace a d y L) :=
  Module.addCommMonoidToAddCommGroup K

/-- The scalar rows restricted to tuples satisfying the partial condition. -/
def residualPartialScalarRow (a : PointCoordinates K (n + 1) z) (d : ℕ)
    (P : PointCoordinates K n p) (y : Fin (n + 1) → K)
    (L : Submodule K (Fin (n + 1) → K)) (i : Fin p) :
    residualPartialSpace a d y L →ₗ[K] K :=
  (residualScalarRow a d P i).comp (residualPartialSpace a d y L).subtype

/-- All residual tuples are separated on one nonempty principal open of
hyperplane configurations. The open is chosen before any partial fiber. -/
theorem generic_residualScalarEvaluation_injective [Infinite K]
    (a : PointCoordinates K (n + 1) z)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 1 + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (p : ℕ) (hp : (n + 1) * finrank K (pointDegreePiece K a d) ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ P : PointCoordinates K n p, eval P D ≠ 0) ∧
      ∀ P, eval P D ≠ 0 →
        Function.Injective (LinearMap.pi (residualScalarRow a d P)) := by
  let T := tangentPointProductForm a d
  have hT : Function.Injective T := tangentPointProductForm_injective a ha hmul
  have hdim : finrank K T.range ≤ p := by
    rw [finrank_tangentPointProductForm_range a ha hmul]
    exact hp
  obtain ⟨D, hD, hgood⟩ := generic_subspaceEvaluation_injective T.range p hdim
  refine ⟨D, hD, fun P hP f g hfg => ?_⟩
  apply hT
  have he := hgood P hP (show subspaceEvaluation T.range P
      ⟨T f, ⟨f, rfl⟩⟩ = subspaceEvaluation T.range P ⟨T g, ⟨g, rfl⟩⟩ from hfg)
  exact congrArg Subtype.val he

/-- The exact dimension of the residual partial-condition space. -/
theorem finrank_residualPartialSpace (a : PointCoordinates K (n + 1) z)
    (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K))
    (hy : ∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) :
    finrank K (residualPartialSpace a d y L) =
      (n + 1) * finrank K (pointDegreePiece K a d) -
        ((n + 1) - finrank K L) := by
  simpa only [residualPartialSpace, pointPolynomialPiece_finrank] using
    finrank_partialScalarSpace (residualPointValue a d y) hy L

/-- Lemma 3.7. One open set works for every subsequent partial condition,
including a partial subspace depending on the chosen configuration. -/
theorem generic_scalar_condition_selection [Infinite K]
    (a : PointCoordinates K (n + 1) z)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 1 + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (p : ℕ) (hp : (n + 1) * finrank K (pointDegreePiece K a d) ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ P : PointCoordinates K n p, eval P D ≠ 0) ∧
      ∀ P, eval P D ≠ 0 →
        ∀ (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)),
          (∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) →
          finrank K (residualPartialSpace a d y L) =
            (n + 1) * finrank K (pointDegreePiece K a d) -
              ((n + 1) - finrank K L) ∧
          Function.Injective (LinearMap.pi (residualPartialScalarRow a d P y L)) ∧
          ∀ q : ℕ, q ≤ p → ∃ s : Finset (Fin p), s.card = q ∧
            (q ≤ finrank K (residualPartialSpace a d y L) →
              LinearIndependent K (fun i : s => residualPartialScalarRow a d P y L i)) ∧
            (finrank K (residualPartialSpace a d y L) ≤ q →
              Function.Injective (selectedScalarEvaluation (K := K)
                (V := ↥(residualPartialSpace a d y L))
                (residualPartialScalarRow a d P y L) s)) := by
  obtain ⟨D, hD, hgood⟩ := generic_residualScalarEvaluation_injective a ha hmul p hp
  refine ⟨D, hD, fun P hP y L hy => ?_⟩
  have hinj : Function.Injective (LinearMap.pi (residualPartialScalarRow a d P y L)) := by
    intro f g hfg
    apply Subtype.ext
    exact hgood P hP hfg
  refine ⟨finrank_residualPartialSpace a y L hy, hinj, fun q hq => ?_⟩
  let S := residualPartialSpace a d y L
  let α : Fin p → Module.Dual K S := residualPartialScalarRow a d P y L
  have hα : Function.Injective (LinearMap.pi α) := hinj
  change ∃ s : Finset (Fin p), s.card = q ∧
    (q ≤ finrank K S → LinearIndependent K (fun i : s => α i)) ∧
    (finrank K S ≤ q → Function.Injective (selectedScalarEvaluation α s))
  exact scalar_row_selection α hα q (by simpa only [Fintype.card_fin] using hq)

/-- On the distinct-point locus, the selected rows are distinct geometric
points as well as distinct indices. -/
theorem generic_distinct_scalar_condition_selection [Infinite K] [CharZero K]
    (hn : 1 ≤ n) (a : PointCoordinates K (n + 1) z)
    (ha : ∀ i, chartPoint K a i (0 : Fin (n + 1 + 1)) ≠ 0)
    (hmul : Function.Injective (pointMultiplication a d))
    (p : ℕ) (hp : (n + 1) * finrank K (pointDegreePiece K a d) ≤ p) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ P : PointCoordinates K n p, eval P D ≠ 0) ∧
      ∀ P, eval P D ≠ 0 → DistinctPoints K P ∧
        ∀ (y : Fin (n + 1) → K) (L : Submodule K (Fin (n + 1) → K)),
          (∃ w : pointPolynomialPiece a d, eval (Fin.cons 0 y) w.val ≠ 0) →
          finrank K (residualPartialSpace a d y L) =
            (n + 1) * finrank K (pointDegreePiece K a d) -
              ((n + 1) - finrank K L) ∧
          Function.Injective (LinearMap.pi (residualPartialScalarRow a d P y L)) ∧
          ∀ q : ℕ, q ≤ p → ∃ s : Finset (Fin p), s.card = q ∧
            (q ≤ finrank K (residualPartialSpace a d y L) →
              LinearIndependent K (fun i : s => residualPartialScalarRow a d P y L i)) ∧
            (finrank K (residualPartialSpace a d y L) ≤ q →
              Function.Injective (selectedScalarEvaluation (K := K)
                (V := ↥(residualPartialSpace a d y L))
                (residualPartialScalarRow a d P y L) s)) := by
  obtain ⟨D, hD, hgood⟩ := generic_scalar_condition_selection a ha hmul p hp
  let E := distinctnessPolynomial K hn p
  obtain ⟨P₀, hP₀, hE₀⟩ := principal_opens_meet D E hD
    (distinctnessPolynomial_nonempty hn p)
  refine ⟨D * E, ⟨P₀, ?_⟩, fun P hP => ?_⟩
  · simpa only [map_mul] using mul_ne_zero hP₀ hE₀
  · have hparts : eval P D ≠ 0 ∧ eval P E ≠ 0 := by simpa only [map_mul, mul_ne_zero_iff] using hP
    exact ⟨distinctPoints_of_polynomial_ne_zero hn P hparts.2, hgood P hparts.1⟩

end ResidualConditions

end IdealGeneration
