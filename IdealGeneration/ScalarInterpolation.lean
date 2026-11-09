module

public import IdealGeneration.Points
public import IdealGeneration.RankOpen
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
Scalar postulation, including one nonempty principal open for all degrees.
Adapted from `ChoppedPlane/GeneralPoints.lean` in the author's Apache-2.0
development, with the number of projective coordinates made arbitrary.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module
variable {K : Type*} [Field K]

def chartEvaluationPolynomial {n p d : ℕ} (f : Forms K (n + 1) d) (i : Fin p) :
    MvPolynomial (Fin p × Fin n) K :=
  eval₂ C (Fin.snoc (α := fun _ : Fin (n + 1) => MvPolynomial (Fin p × Fin n) K)
    (fun j : Fin n => X (i, j)) 1) f.val

@[simp] theorem eval_chartEvaluationPolynomial {n p d : ℕ} (f : Forms K (n + 1) d)
    (i : Fin p) (a : PointCoordinates K n p) :
    eval a (chartEvaluationPolynomial f i) = pointEvaluation K a d f i := by
  rw [chartEvaluationPolynomial, MvPolynomial.eval_eval₂]
  change eval₂ ((eval a).comp C)
    (fun j => eval a ((Fin.snoc
      (α := fun _ : Fin (n + 1) => MvPolynomial (Fin p × Fin n) K)
      (fun l : Fin n => X (i, l)) 1) j)) f.val = eval (chartPoint K a i) f.val
  have hc : (eval a).comp C = RingHom.id K := by ext c; simp
  rw [hc]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [chartPoint]

theorem pointEvaluation_isPolynomialFamily (n p d : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K n p => pointEvaluation K a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have hterm (i : Fin p) : IsPolynomialFamily (fun a : PointCoordinates K n p =>
      pointEvaluation K a d f i • (Pi.single i 1 : Fin p → K)) := by
    have hi : IsPolynomialFamily (fun a : PointCoordinates K n p =>
        pointEvaluation K a d f i) := by
      simpa only [eval_chartEvaluationPolynomial] using
        isPolynomialFamily_eval (chartEvaluationPolynomial f i)
    exact hi.smul (isPolynomialFamily_const (Pi.single i 1))
  have hs := IsPolynomialFamily.sum hterm
  have heq : (fun a : PointCoordinates K n p =>
      ∑ i, pointEvaluation K a d f i • (Pi.single i 1 : Fin p → K)) =
      (fun a => pointEvaluation K a d f) := by
    funext a i
    simp [Pi.single_apply]
  exact heq ▸ hs

/-- In each degree the expected scalar Hilbert function holds on a nonempty open. -/
theorem generic_pointHilbertFunction_at [Infinite K] (n p d : ℕ) :
    ∃ E : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a E ≠ 0) ∧
      ∀ a, eval a E ≠ 0 → pointHilbertFunction K a d = min ((n + d).choose d) p := by
  obtain ⟨a₀, ha₀⟩ := exists_pointHilbertFunction_maximal (K := K) n p d
  obtain ⟨E, hE, hgood⟩ := rank_polynomial_principal_open
    (fun a : PointCoordinates K n p => pointEvaluation K a d)
    (pointEvaluation_isPolynomialFamily n p d) a₀
  refine ⟨E, ⟨a₀, hE⟩, fun a ha => le_antisymm (pointHilbertFunction_le a) ?_⟩
  have hl := hgood a ha
  rw [← pointHilbertFunction_eq_rank, ← pointHilbertFunction_eq_rank, ha₀] at hl
  exact hl

theorem pointEvaluation_surjective_above {n p q t : ℕ} (a : PointCoordinates K n p)
    (hqt : q ≤ t) (h : Function.Surjective (pointEvaluation K a q)) :
    Function.Surjective (pointEvaluation K a t) := by
  intro y
  obtain ⟨f, hf⟩ := h y
  let g : Forms K (n + 1) t := ⟨f.val * X (Fin.last n) ^ (t - q), by
    have hh := f.property.mul
      ((isHomogeneous_X (R := K) (Fin.last n)).pow (t - q))
    simpa [Nat.add_sub_of_le hqt] using hh⟩
  refine ⟨g, ?_⟩
  ext i
  change eval (chartPoint K a i) (f.val * X (Fin.last n) ^ (t - q)) = y i
  simpa using congrFun hf i

theorem pointEvaluation_surjective_of_hilbert_eq {n p q : ℕ}
    (a : PointCoordinates K n p) (h : pointHilbertFunction K a q = p) :
    Function.Surjective (pointEvaluation K a q) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [pointHilbertFunction_eq_rank, Module.finrank_pi_fintype] using h

theorem pointHilbertFunction_constant_above {n p q t : ℕ}
    (a : PointCoordinates K n p) (hqt : q ≤ t) (h : pointHilbertFunction K a q = p) :
    pointHilbertFunction K a t = p := by
  rw [pointHilbertFunction_eq_rank,
    LinearMap.range_eq_top.mpr (pointEvaluation_surjective_above a hqt
      (pointEvaluation_surjective_of_hilbert_eq a h)), finrank_top]
  simp

theorem chart_formsCount_mono {n s t : ℕ} (h : s ≤ t) :
    (n + s).choose s ≤ (n + t).choose t := by
  rw [← Nat.choose_symm (by omega : s ≤ n + s),
    ← Nat.choose_symm (by omega : t ≤ n + t)]
  simp only [Nat.add_sub_cancel]
  exact Nat.choose_le_choose n (by omega)

theorem point_count_le_chart_forms {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    p ≤ (n + p).choose p := by
  have h := Nat.choose_le_choose p (show p + 1 ≤ n + p by omega)
  rw [Nat.choose_succ_self_right] at h
  omega

def distinctnessPolynomial (K : Type*) [Field K] {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    MvPolynomial (Fin p × Fin n) K :=
  ∏ ij : {ij : Fin p × Fin p // ij.1 < ij.2},
    (X (ij.val.1, ⟨0, hn⟩) - X (ij.val.2, ⟨0, hn⟩))

theorem distinctnessPolynomial_nonempty [CharZero K] {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    ∃ a : PointCoordinates K n p, eval a (distinctnessPolynomial K hn p) ≠ 0 := by
  classical
  refine ⟨fun ij => (ij.1.val : K), ?_⟩
  simp only [distinctnessPolynomial, map_prod, map_sub, eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  apply sub_ne_zero.mpr
  exact_mod_cast (ne_of_lt ij.property : ij.val.1.val ≠ ij.val.2.val)

theorem distinctPoints_of_polynomial_ne_zero {n p : ℕ} (hn : 1 ≤ n)
    (a : PointCoordinates K n p) (h : eval a (distinctnessPolynomial K hn p) ≠ 0) :
    DistinctPoints K a := by
  classical
  have hall : ∀ ij : {ij : Fin p × Fin p // ij.1 < ij.2},
      a (ij.val.1, ⟨0, hn⟩) - a (ij.val.2, ⟨0, hn⟩) ≠ 0 := by
    simp only [distinctnessPolynomial, map_prod, map_sub, eval_X] at h
    intro ij
    exact (Finset.prod_ne_zero_iff.mp h) ij (Finset.mem_univ ij)
  intro i j hij
  by_contra hne
  have heq := congrFun hij (⟨0, hn⟩ : Fin n)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hall ⟨(i, j), hlt⟩ (by simp [heq])
  · exact hall ⟨(j, i), hgt⟩ (by simp [heq])

/-- Equation (2.1)'s scalar postulation, uniformly in all degrees on one actual open. -/
theorem generic_pointHilbertFunction [CharZero K] {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    ∃ E : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a E ≠ 0) ∧
      ∀ a, eval a E ≠ 0 → DistinctPoints K a ∧
        ∀ t, pointHilbertFunction K a t = min ((n + t).choose t) p := by
  classical
  choose E hE hgood using fun i : Fin (p + 1) =>
    generic_pointHilbertFunction_at (K := K) n p i.val
  let F := distinctnessPolynomial K hn p * ∏ i, E i
  have hne : F ≠ 0 := by
    apply mul_ne_zero
    · obtain ⟨a, ha⟩ := distinctnessPolynomial_nonempty (K := K) hn p
      intro hz
      simp [hz] at ha
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      obtain ⟨a, ha⟩ := hE i
      intro hz
      simp [hz] at ha
  have hex : ∃ a : PointCoordinates K n p, eval a F ≠ 0 := by
    by_contra! h
    exact hne (MvPolynomial.funext h)
  refine ⟨F, hex, ?_⟩
  intro a ha
  have hparts : eval a (distinctnessPolynomial K hn p) ≠ 0 ∧
      ∀ i, eval a (E i) ≠ 0 := by
    simpa only [F, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_true_left] using ha
  refine ⟨distinctPoints_of_polynomial_ne_zero hn a hparts.1, ?_⟩
  intro t
  by_cases ht : t ≤ p
  · exact hgood ⟨t, by omega⟩ a (hparts.2 ⟨t, by omega⟩)
  · have hp : pointHilbertFunction K a p = p := by
      simpa only [min_eq_right (point_count_le_chart_forms hn p)] using
        hgood ⟨p, by omega⟩ a (hparts.2 ⟨p, by omega⟩)
    have hc := pointHilbertFunction_constant_above a (by omega : p ≤ t) hp
    have hle : p ≤ (n + t).choose t :=
      (point_count_le_chart_forms hn p).trans (chart_formsCount_mono (by omega))
    simpa only [min_eq_right hle] using hc

/-- The homogeneous ideal-piece dimension asserted in equation (2.1). -/
theorem ideal_piece_finrank_of_postulation {n p d : ℕ} (a : PointCoordinates K n p)
    (h : pointHilbertFunction K a d = min ((n + d).choose d) p) :
    finrank K (pointDegreePiece K a d) = (n + d).choose d - p := by
  have hd := (pointDegreePiece K a d).finrank_quotient_add_finrank
  rw [finrank_chart_forms] at hd
  change pointHilbertFunction K a d + finrank K (pointDegreePiece K a d) = _ at hd
  rw [h] at hd
  omega

end IdealGeneration
