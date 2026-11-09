module

public import IdealGeneration.SubspaceInterpolation
public import IdealGeneration.TwoGroupLinearCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Two groups of scalar interpolation conditions

For a fixed space of pairs of homogeneous forms, independently choosing equal
numbers of points on the two sides imposes the expected number of conditions.
This is the polynomial-space version of Lemma 4.1.
-/

noncomputable section
namespace IdealGeneration
open MvPolynomial Module

namespace TwoGroupInterpolation

variable {K A B C V : Type*} [Field K]
  [AddCommMonoid A] [Module K A] [AddCommMonoid B] [Module K B]
  [AddCommMonoid C] [Module K C] [AddCommMonoid V] [Module K V]

/-- The first projection of a space of pairs. -/
def leftProjection (U : Submodule K (A × B)) : U →ₗ[K] A :=
  (LinearMap.fst K A B).comp U.subtype

/-- The second projection of a space of pairs. -/
def rightProjection (U : Submodule K (A × B)) : U →ₗ[K] B :=
  (LinearMap.snd K A B).comp U.subtype

theorem projection_pair_injective (U : Submodule K (A × B)) :
    Function.Injective ((leftProjection U).prod (rightProjection U)) := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- On the pure first-coordinate space, the first projection is injective. -/
theorem leftProjection_pure_injective (U : Submodule K (A × B)) :
    Function.Injective ((leftProjection U).comp (rightProjection U).ker.subtype) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · exact (LinearMap.mem_ker.mp x.property).trans (LinearMap.mem_ker.mp y.property).symm

/-- On the pure second-coordinate space, the second projection is injective. -/
theorem rightProjection_pure_injective (U : Submodule K (A × B)) :
    Function.Injective ((rightProjection U).comp (leftProjection U).ker.subtype) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (LinearMap.mem_ker.mp x.property).trans (LinearMap.mem_ker.mp y.property).symm
  · exact h

/-- Passing through the range of a map does not change a subsequent image. -/
theorem range_comp_range_subtype (f : V →ₗ[K] A) (E : A →ₗ[K] C) :
    (E.comp f).range = (E.comp f.range.subtype).range := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨f.rangeRestrict v, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨v, hv⟩ := a.property
    exact ⟨v, congrArg E hv⟩

/-- An injective evaluation on the image preserves injectivity of its source map. -/
theorem comp_injective_of_range_injective (f : V →ₗ[K] A) (E : A →ₗ[K] C)
    (hf : Function.Injective f) (hE : Function.Injective (E.comp f.range.subtype)) :
    Function.Injective (E.comp f) := by
  intro x y hxy
  apply hf
  have h : f.rangeRestrict x = f.rangeRestrict y := hE hxy
  exact congrArg Subtype.val h

end TwoGroupInterpolation

open TwoGroupInterpolation

variable {K : Type*} [Field K] {n d : ℕ}

/-- Two independently witnessed scalar conditions can be imposed on the same points. -/
theorem exists_subspaceEvaluation_rank_and_injective [Infinite K]
    (P Q : Submodule K (Forms K (n + 1) d)) (r : ℕ) (hQ : finrank K Q ≤ r) :
    ∃ a : PointCoordinates K n r,
      finrank K (subspaceEvaluation P a).range = min (finrank K P) r ∧
      Function.Injective (subspaceEvaluation Q a) := by
  obtain ⟨D, hD, hgoodD⟩ := generic_subspaceEvaluation P r
  obtain ⟨E, hE, hgoodE⟩ := generic_subspaceEvaluation_injective Q r hQ
  have hDn : D ≠ 0 := by
    obtain ⟨a, ha⟩ := hD
    intro hz
    simp [hz] at ha
  have hEn : E ≠ 0 := by
    obtain ⟨a, ha⟩ := hE
    intro hz
    simp [hz] at ha
  have hprod : D * E ≠ 0 := mul_ne_zero hDn hEn
  obtain ⟨a, ha⟩ : ∃ a : PointCoordinates K n r, eval a (D * E) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  have hparts : eval a D ≠ 0 ∧ eval a E ≠ 0 := by simpa using ha
  exact ⟨a, hgoodD a hparts.1, hgoodE a hparts.2⟩

variable {nA nB dA dB : ℕ}

/-- Evaluate the first polynomial in each pair at its own point configuration. -/
def leftGroupEvaluation
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    {r : ℕ} (a : PointCoordinates K nA r) : U →ₗ[K] (Fin r → K) :=
  (pointEvaluation K a dA).comp (leftProjection U)

/-- Evaluate the second polynomial in each pair at its own point configuration. -/
def rightGroupEvaluation
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    {r : ℕ} (b : PointCoordinates K nB r) : U →ₗ[K] (Fin r → K) :=
  (pointEvaluation K b dB).comp (rightProjection U)

/-- The full two-group evaluation of the space of polynomial pairs. -/
def twoGroupEvaluation
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    {r : ℕ} (a : PointCoordinates K nA r) (b : PointCoordinates K nB r) :
    U →ₗ[K] ((Fin r → K) × (Fin r → K)) :=
  (leftGroupEvaluation U a).prod (rightGroupEvaluation U b)

/-- Choose the first group to have maximal rank and to kill the pure first side. -/
theorem exists_good_leftGroupEvaluation [Infinite K]
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    (r : ℕ) (hA : finrank K (rightProjection U).ker ≤ r) :
    ∃ a : PointCoordinates K nA r,
      finrank K (leftGroupEvaluation U a).range = min (finrank K (leftProjection U).range) r ∧
      Function.Injective ((leftGroupEvaluation U a).comp (rightProjection U).ker.subtype) := by
  let q := (leftProjection U).comp (rightProjection U).ker.subtype
  have hq : Function.Injective q := leftProjection_pure_injective U
  have hdim : finrank K q.range ≤ r := by
    rw [LinearMap.finrank_range_of_inj hq]
    exact hA
  obtain ⟨a, ha, hinj⟩ :=
    exists_subspaceEvaluation_rank_and_injective (leftProjection U).range q.range r hdim
  refine ⟨a, ?_, ?_⟩
  · change finrank K ((pointEvaluation K a dA).comp (leftProjection U)).range = _
    rw [range_comp_range_subtype (leftProjection U) (pointEvaluation K a dA)]
    exact ha
  · exact comp_injective_of_range_injective q (pointEvaluation K a dA) hq hinj

/-- Once the first kernel embeds in the second side, choose the second group
with maximal rank there and injectivity on the pure second side. -/
theorem exists_good_rightGroupEvaluation [Infinite K]
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    (L : Submodule K U) (r : ℕ)
    (hL : Function.Injective ((rightProjection U).comp L.subtype))
    (hB : finrank K (leftProjection U).ker ≤ r) :
    ∃ b : PointCoordinates K nB r,
      finrank K ((rightGroupEvaluation U b).comp L.subtype).range = min (finrank K L) r ∧
      Function.Injective ((rightGroupEvaluation U b).comp (leftProjection U).ker.subtype) := by
  let q := (rightProjection U).comp L.subtype
  let qPure := (rightProjection U).comp (leftProjection U).ker.subtype
  have hq : Function.Injective q := hL
  have hqPure : Function.Injective qPure := rightProjection_pure_injective U
  have hdim : finrank K qPure.range ≤ r := by
    rw [LinearMap.finrank_range_of_inj hqPure]
    exact hB
  obtain ⟨b, hb, hinj⟩ :=
    exists_subspaceEvaluation_rank_and_injective q.range qPure.range r hdim
  refine ⟨b, ?_, ?_⟩
  · change finrank K ((pointEvaluation K b dB).comp q).range = _
    rw [range_comp_range_subtype q (pointEvaluation K b dB)]
    have hdimq : finrank K q.range = finrank K L := LinearMap.finrank_range_of_inj hq
    rw [hdimq] at hb
    exact hb
  · exact comp_injective_of_range_injective qPure (pointEvaluation K b dB) hqPure hinj

/-- Lemma 4.1 for actual homogeneous polynomial spaces. Equal-size groups
leave the expected kernel and are injective on the two pure-side subspaces. -/
theorem exists_twoGroupInterpolation [Infinite K]
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    (r : ℕ) (hA : finrank K (rightProjection U).ker ≤ r)
    (hB : finrank K (leftProjection U).ker ≤ r) :
    ∃ (a : PointCoordinates K nA r) (b : PointCoordinates K nB r),
      finrank K (twoGroupEvaluation U a b).ker = finrank K U - 2 * r ∧
      Function.Injective ((leftGroupEvaluation U a).comp (rightProjection U).ker.subtype) ∧
      Function.Injective ((rightGroupEvaluation U b).comp (leftProjection U).ker.subtype) := by
  obtain ⟨a, hfirst, hpureA⟩ := exists_good_leftGroupEvaluation U r hA
  have hL : Function.Injective
      ((rightProjection U).comp (leftGroupEvaluation U a).ker.subtype) := by
    exact (TwoGroup.secondStage_injective_symm_monoid
      (leftGroupEvaluation U a) (rightProjection U)).mpr hpureA
  obtain ⟨b, hsecond, hpureB⟩ :=
    exists_good_rightGroupEvaluation U (leftGroupEvaluation U a).ker r hL hB
  refine ⟨a, b, ?_, hpureA, hpureB⟩
  exact TwoGroup.two_group_kernel_finrank_monoid (leftProjection U)
    (leftGroupEvaluation U a) (rightGroupEvaluation U b) r hB hfirst hsecond

/-- Polynomial families remain polynomial after selecting parameter coordinates. -/
theorem polynomialFamily_reindex {ι κ W : Type*} [AddCommGroup W] [Module K W]
    {f : (ι → K) → W} (hf : IsPolynomialFamily f) (j : ι → κ) :
    IsPolynomialFamily (fun c : κ → K => f (c ∘ j)) := by
  intro ell
  obtain ⟨p, hp⟩ := hf ell
  refine ⟨rename j p, fun c => ?_⟩
  rw [eval_rename]
  exact hp (c ∘ j)

/-- The combined evaluation is polynomial in its two independent point groups. -/
theorem twoGroupEvaluation_isPolynomialFamily
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB)) (r : ℕ) :
    IsPolynomialFamily (fun c : ((Fin r × Fin nA) ⊕ (Fin r × Fin nB)) → K =>
      twoGroupEvaluation U (c ∘ Sum.inl) (c ∘ Sum.inr)) := by
  apply isPolynomialFamily_linearMap (K := K) (V := U)
    (W := (Fin r → K) × (Fin r → K))
    (fun c : ((Fin r × Fin nA) ⊕ (Fin r × Fin nB)) → K =>
      twoGroupEvaluation U (c ∘ Sum.inl) (c ∘ Sum.inr))
  intro f
  have hleft : IsPolynomialFamily (fun a : PointCoordinates K nA r =>
      pointEvaluation K a dA (leftProjection U f)) :=
    (pointEvaluation_isPolynomialFamily (K := K) nA r dA).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin r → K) (leftProjection U f))
  have hright : IsPolynomialFamily (fun b : PointCoordinates K nB r =>
      pointEvaluation K b dB (rightProjection U f)) :=
    (pointEvaluation_isPolynomialFamily (K := K) nB r dB).linear_comp
      (LinearMap.applyₗ (R := K) (M₂ := Fin r → K) (rightProjection U f))
  exact (polynomialFamily_reindex hleft Sum.inl).prod_mk
    (polynomialFamily_reindex hright Sum.inr)

/-- Lemma 4.1 holds on a nonempty principal open in the independent point parameters. -/
theorem generic_twoGroupInterpolation [Infinite K]
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    (r : ℕ) (hA : finrank K (rightProjection U).ker ≤ r)
    (hB : finrank K (leftProjection U).ker ≤ r) :
    ∃ P : MvPolynomial ((Fin r × Fin nA) ⊕ (Fin r × Fin nB)) K,
      (∃ c, eval c P ≠ 0) ∧
      ∀ c, eval c P ≠ 0 →
        finrank K (twoGroupEvaluation U (c ∘ Sum.inl) (c ∘ Sum.inr)).ker =
          finrank K U - 2 * r ∧
        Function.Injective ((leftGroupEvaluation U (c ∘ Sum.inl)).comp
          (rightProjection U).ker.subtype) ∧
        Function.Injective ((rightGroupEvaluation U (c ∘ Sum.inr)).comp
          (leftProjection U).ker.subtype) := by
  classical
  obtain ⟨a, b, hker, _, _⟩ := exists_twoGroupInterpolation U r hA hB
  let c₀ : ((Fin r × Fin nA) ⊕ (Fin r × Fin nB)) → K := Sum.elim a b
  let F := fun c : ((Fin r × Fin nA) ⊕ (Fin r × Fin nB)) → K =>
    twoGroupEvaluation U (c ∘ Sum.inl) (c ∘ Sum.inr)
  have hF : IsPolynomialFamily F := twoGroupEvaluation_isPolynomialFamily U r
  let qLeft := (leftProjection U).comp (rightProjection U).ker.subtype
  let qRight := (rightProjection U).comp (leftProjection U).ker.subtype
  have hqLeft : Function.Injective qLeft := leftProjection_pure_injective U
  have hqRight : Function.Injective qRight := rightProjection_pure_injective U
  have hdLeft : finrank K qLeft.range ≤ r := by
    rw [LinearMap.finrank_range_of_inj hqLeft]
    exact hA
  have hdRight : finrank K qRight.range ≤ r := by
    rw [LinearMap.finrank_range_of_inj hqRight]
    exact hB
  obtain ⟨P, hP, hrank⟩ := rank_polynomial_principal_open (K := K) (V := U)
    (W := (Fin r → K) × (Fin r → K)) F hF c₀
  obtain ⟨PL, hPL, hinjL⟩ := generic_subspaceEvaluation_injective qLeft.range r hdLeft
  obtain ⟨PR, hPR, hinjR⟩ := generic_subspaceEvaluation_injective qRight.range r hdRight
  have hnP : P ≠ 0 := by intro hz; simp [hz] at hP
  have hnPL : PL ≠ 0 := by
    obtain ⟨a, ha⟩ := hPL
    intro hz
    simp [hz] at ha
  have hnPR : PR ≠ 0 := by
    obtain ⟨b, hb⟩ := hPR
    intro hz
    simp [hz] at hb
  have hrenameL : rename (Sum.inl : (Fin r × Fin nA) →
      (Fin r × Fin nA) ⊕ (Fin r × Fin nB)) PL ≠ 0 := by
    intro hz
    apply hnPL
    exact (rename_eq_zero_iff_of_injective PL Sum.inl_injective).mp hz
  have hrenameR : rename (Sum.inr : (Fin r × Fin nB) →
      (Fin r × Fin nA) ⊕ (Fin r × Fin nB)) PR ≠ 0 := by
    intro hz
    apply hnPR
    exact (rename_eq_zero_iff_of_injective PR Sum.inr_injective).mp hz
  let Q := P * rename Sum.inl PL * rename Sum.inr PR
  have hnQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hnP hrenameL) hrenameR
  obtain ⟨c, hc⟩ : ∃ c, eval c Q ≠ 0 := by
    by_contra! h
    exact hnQ (MvPolynomial.funext h)
  refine ⟨Q, ⟨c, hc⟩, ?_⟩
  intro c hc
  have hparts : (eval c P ≠ 0 ∧ eval (c ∘ Sum.inl) PL ≠ 0) ∧
      eval (c ∘ Sum.inr) PR ≠ 0 := by
    simpa only [Q, map_mul, mul_ne_zero_iff, eval_rename] using hc
  refine ⟨?_, ?_, ?_⟩
  · have hlow := hrank c hparts.1.1
    have hdim₀ : finrank K (F c₀).range + finrank K (F c₀).ker = finrank K U := by
      exact TwoGroup.rank_nullity_monoid (F c₀)
    have hdim : finrank K (F c).range + finrank K (F c).ker = finrank K U := by
      exact TwoGroup.rank_nullity_monoid (F c)
    have htarget : finrank K (F c).range ≤ finrank K ((Fin r → K) × (Fin r → K)) := by
      exact Submodule.finrank_le (F c).range
    change finrank K (F c).ker = _
    have hker₀ : finrank K (F c₀).ker = finrank K U - 2 * r := hker
    rw [hker₀] at hdim₀
    simp [Module.finrank_prod] at htarget
    omega
  · exact comp_injective_of_range_injective qLeft
      (pointEvaluation K (c ∘ Sum.inl) dA) hqLeft (hinjL _ hparts.1.2)
  · exact comp_injective_of_range_injective qRight
      (pointEvaluation K (c ∘ Sum.inr) dB) hqRight (hinjR _ hparts.2)

/-- When both charts have positive dimension, the witnesses may be required
to consist of pairwise distinct points in each group. -/
theorem exists_distinct_twoGroupInterpolation [CharZero K]
    (hnA : 1 ≤ nA) (hnB : 1 ≤ nB)
    (U : Submodule K (Forms K (nA + 1) dA × Forms K (nB + 1) dB))
    (r : ℕ) (hA : finrank K (rightProjection U).ker ≤ r)
    (hB : finrank K (leftProjection U).ker ≤ r) :
    ∃ (a : PointCoordinates K nA r) (b : PointCoordinates K nB r),
      DistinctPoints K a ∧ DistinctPoints K b ∧
      finrank K (twoGroupEvaluation U a b).ker = finrank K U - 2 * r ∧
      Function.Injective ((leftGroupEvaluation U a).comp (rightProjection U).ker.subtype) ∧
      Function.Injective ((rightGroupEvaluation U b).comp (leftProjection U).ker.subtype) := by
  obtain ⟨P, hP, hgood⟩ := generic_twoGroupInterpolation U r hA hB
  obtain ⟨DA, hDA, hgoodA⟩ := generic_pointHilbertFunction (K := K) hnA r
  obtain ⟨DB, hDB, hgoodB⟩ := generic_pointHilbertFunction (K := K) hnB r
  have hnP : P ≠ 0 := by
    obtain ⟨c, hc⟩ := hP
    intro hz
    simp [hz] at hc
  have hnDA : DA ≠ 0 := by
    obtain ⟨a, ha⟩ := hDA
    intro hz
    simp [hz] at ha
  have hnDB : DB ≠ 0 := by
    obtain ⟨b, hb⟩ := hDB
    intro hz
    simp [hz] at hb
  have hrenameA : rename (Sum.inl : (Fin r × Fin nA) →
      (Fin r × Fin nA) ⊕ (Fin r × Fin nB)) DA ≠ 0 := by
    intro hz
    apply hnDA
    exact (rename_eq_zero_iff_of_injective DA Sum.inl_injective).mp hz
  have hrenameB : rename (Sum.inr : (Fin r × Fin nB) →
      (Fin r × Fin nA) ⊕ (Fin r × Fin nB)) DB ≠ 0 := by
    intro hz
    apply hnDB
    exact (rename_eq_zero_iff_of_injective DB Sum.inr_injective).mp hz
  let Q := P * rename Sum.inl DA * rename Sum.inr DB
  have hnQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hnP hrenameA) hrenameB
  obtain ⟨c, hc⟩ : ∃ c, eval c Q ≠ 0 := by
    by_contra! h
    exact hnQ (MvPolynomial.funext h)
  have hparts : (eval c P ≠ 0 ∧ eval (c ∘ Sum.inl) DA ≠ 0) ∧
      eval (c ∘ Sum.inr) DB ≠ 0 := by
    simpa only [Q, map_mul, mul_ne_zero_iff, eval_rename] using hc
  exact ⟨c ∘ Sum.inl, c ∘ Sum.inr, (hgoodA _ hparts.1.2).1,
    (hgoodB _ hparts.2).1, hgood c hparts.1.1⟩

end IdealGeneration
