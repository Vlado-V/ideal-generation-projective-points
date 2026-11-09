module

public import IdealGeneration.RankOpen
public import IdealGeneration.Rank
public import IdealGeneration.DeformationMatrix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The first-variation rank principle

The proof uses normalized columns in the image of the polynomial family.
It avoids choosing bases adapted to the special fiber.
-/

noncomputable section
namespace IdealGeneration.DeformationGeneral
open Module MvPolynomial

variable {k V W Q : Type*} [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup Q] [Module k Q]

/-- The derivative restricted to the special kernel and projected to a quotient. -/
def response (A₀ D₀ : V →ₗ[k] W) (π : W →ₗ[k] Q) : A₀.ker →ₗ[k] Q :=
  π.comp (D₀.comp A₀.ker.subtype)

/-- A polynomial first-order expansion gains the rank of its induced response. -/
theorem rank_gain_principal_open
    (A D : (Fin 1 → k) → (V →ₗ[k] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (π : W →ₗ[k] Q) (hπ : π.comp (A 0) = 0) :
    ∃ f : MvPolynomial (Fin 1) k, eval 0 f ≠ 0 ∧
      ∀ a : Fin 1 → k, a 0 ≠ 0 → eval a f ≠ 0 →
        finrank k (A 0).range + finrank k (response (A 0) (D 0) π).range ≤
          finrank k (A a).range := by
  classical
  let A₀ := A 0
  let R := response A₀ (D 0) π
  obtain ⟨P, hP⟩ := A₀.rangeRestrict.exists_rightInverse_of_surjective
    A₀.range_rangeRestrict
  obtain ⟨S, hS⟩ := R.rangeRestrict.exists_rightInverse_of_surjective
    R.range_rangeRestrict
  have hPval (u : A₀.range) : A₀ (P u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hP u)
  have hSval (u : R.range) : R (S u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hS u)
  let E : (Fin 1 → k) → (A₀.range × R.range →ₗ[k] W) := fun a =>
    ((A a).comp P).coprod ((D a).comp (A₀.ker.subtype.comp S))
  have hEpoly : IsPolynomialFamily E := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hA.linear_comp (LinearMap.applyₗ (R := k) (M₂ := W) (P x.1))).add
      (hD.linear_comp (LinearMap.applyₗ (R := k) (M₂ := W) (S x.2).val))
  have hπu (u : A₀.range) : π u.val = 0 := by
    rw [← hPval u]
    exact LinearMap.congr_fun hπ (P u)
  have hE₀ : Function.Injective (E 0) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    change A₀ (P x.1) + D 0 (S x.2).val = 0 at hx
    rw [hPval] at hx
    have hy : x.2 = 0 := by
      apply Subtype.ext
      have hh := congrArg π hx
      rw [map_add, map_zero] at hh
      change π x.1.val + R (S x.2) = 0 at hh
      simpa only [hπu, hSval, zero_add, Submodule.coe_zero] using hh
    have hu : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hy, map_zero, Submodule.coe_zero, add_zero] using hx
    exact Prod.ext hu hy
  obtain ⟨f, hf, hgood⟩ := injective_polynomial_principal_open E hEpoly 0 hE₀
  refine ⟨f, hf, ?_⟩
  intro a ha hfa
  have hsub : (E a).range ≤ (A a).range := by
    rintro _ ⟨x, rfl⟩
    have hk : A₀ (S x.2).val = 0 := (S x.2).property
    have hAk : A a (S x.2).val = a 0 • D a (S x.2).val := by
      rw [hfactor a]
      change A₀ (S x.2).val + a 0 • D a (S x.2).val = _
      rw [hk, zero_add]
    refine ⟨P x.1 + (a 0)⁻¹ • (S x.2).val, ?_⟩
    rw [map_add, map_smul, hAk, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rfl
  have hr := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (hgood a hfa), Module.finrank_prod] at hr
  exact hr

/-- A nonzero parameter attains the first-variation rank lower bound. -/
theorem exists_rank_gain [Infinite k]
    (A D : (Fin 1 → k) → (V →ₗ[k] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (π : W →ₗ[k] Q) (hπ : π.comp (A 0) = 0) :
    ∃ a : Fin 1 → k, a 0 ≠ 0 ∧
      finrank k (A 0).range + finrank k (response (A 0) (D 0) π).range ≤
        finrank k (A a).range := by
  obtain ⟨f, hf, hgood⟩ := rank_gain_principal_open A D hA hD hfactor π hπ
  have hfne : f ≠ 0 := by intro h; simp [h] at hf
  have hprod : f * X (0 : Fin 1) ≠ 0 := mul_ne_zero hfne (X_ne_zero _)
  have hex : ∃ a : Fin 1 → k, eval a (f * X 0) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  obtain ⟨a, ha⟩ := hex
  have hparts : eval a f ≠ 0 ∧ a 0 ≠ 0 := by simpa using ha
  exact ⟨a, hparts.2, hgood a hparts.2 hparts.1⟩

/-- Maximal rank of the induced kernel-to-cokernel response gives a rank-open family. -/
theorem maximal_rank_principal_open
    (A D : (Fin 1 → k) → (V →ₗ[k] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (hresponse : HasMaximalRank (response (A 0) (D 0) (A 0).range.mkQ)) :
    ∃ f : MvPolynomial (Fin 1) k, eval 0 f ≠ 0 ∧
      ∀ a : Fin 1 → k, a 0 ≠ 0 → eval a f ≠ 0 → HasMaximalRank (A a) := by
  let R := response (A 0) (D 0) (A 0).range.mkQ
  have hr : finrank k R.range =
      min (finrank k (A 0).ker) (finrank k (W ⧸ (A 0).range)) :=
    (maximalRank_iff_rank_eq_min R).mp hresponse
  have hn := (A 0).finrank_range_add_finrank_ker
  have hq := (A 0).range.finrank_quotient_add_finrank
  have hsum : finrank k (A 0).range + finrank k R.range =
      min (finrank k V) (finrank k W) := by
    rw [hr]
    omega
  obtain ⟨f, hf, hgood⟩ := rank_gain_principal_open A D hA hD hfactor
    (A 0).range.mkQ (LinearMap.range_mkQ_comp (A 0))
  refine ⟨f, hf, fun a ha hfa => ?_⟩
  apply (maximalRank_iff_rank_eq_min (A a)).mpr
  apply le_antisymm (le_min (A a).finrank_range_le (Submodule.finrank_le _))
  have hlow := hgood a ha hfa
  change finrank k (A 0).range + finrank k R.range ≤ _ at hlow
  rwa [hsum] at hlow

/-- A polynomial family with maximal first response is maximal at some nonzero parameter. -/
theorem exists_maximal_rank [Infinite k]
    (A D : (Fin 1 → k) → (V →ₗ[k] W))
    (hA : IsPolynomialFamily A) (hD : IsPolynomialFamily D)
    (hfactor : ∀ a, A a = A 0 + a 0 • D a)
    (hresponse : HasMaximalRank (response (A 0) (D 0) (A 0).range.mkQ)) :
    ∃ a : Fin 1 → k, a 0 ≠ 0 ∧ HasMaximalRank (A a) := by
  obtain ⟨f, hf, hgood⟩ := maximal_rank_principal_open A D hA hD hfactor hresponse
  have hfne : f ≠ 0 := by intro h; simp [h] at hf
  have hprod : f * X (0 : Fin 1) ≠ 0 := mul_ne_zero hfne (X_ne_zero _)
  have hex : ∃ a : Fin 1 → k, eval a (f * X 0) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  obtain ⟨a, ha⟩ := hex
  have hparts : eval a f ≠ 0 ∧ a 0 ≠ 0 := by simpa using ha
  exact ⟨a, hparts.2, hgood a hparts.2 hparts.1⟩

section PolynomialMatrices

open Polynomial Matrix IdealGeneration.DeformationMatrix
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The actual first-derivative map from the special kernel to the special cokernel. -/
def matrixResponse (A : Matrix m n k[X]) :
    (evalMap A 0).ker →ₗ[k] ((m → k) ⧸ (evalMap A 0).range) :=
  response (evalMap A 0) (firstMap A) (evalMap A 0).range.mkQ

omit [Fintype m] in
/-- The response uses the formal derivative of the original matrix, evaluated at zero. -/
theorem matrixResponse_eq_derivative (A : Matrix m n k[X]) :
    matrixResponse A = (evalMap A 0).range.mkQ.comp
      ((A.map (fun p => p.derivative.eval 0)).mulVecLin.comp (evalMap A 0).ker.subtype) := by
  unfold matrixResponse response
  rw [firstMap_eq_derivative]

/-- The general additive rank bound from the actual first derivative. -/
theorem matrix_rank_gain_principal_open (A : Matrix m n k[X]) :
    ∃ f : MvPolynomial (Fin 1) k, MvPolynomial.eval 0 f ≠ 0 ∧
      ∀ t : k, t ≠ 0 → MvPolynomial.eval (fun _ => t) f ≠ 0 →
        finrank k (evalMap A 0).range + finrank k (matrixResponse A).range ≤
          finrank k (evalMap A t).range := by
  let F : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) := fun a => evalMap A (a 0)
  let D : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) :=
    fun a => evalMap (shifted A) (a 0)
  obtain ⟨f, hf, hgood⟩ := rank_gain_principal_open F D
    (evalMap_isPolynomialFamily A) (evalMap_isPolynomialFamily (shifted A))
    (fun a => evalMap_eq_zero_add A (a 0))
    (evalMap A 0).range.mkQ (LinearMap.range_mkQ_comp _)
  exact ⟨f, hf, fun t ht hft => hgood (fun _ => t) ht hft⟩

/-- Lemma 2.3 for arbitrary polynomial matrices, with no chosen adapted bases. -/
theorem matrix_first_variation (A : Matrix m n k[X])
    (hresponse : HasMaximalRank (matrixResponse A)) :
    ∃ f : MvPolynomial (Fin 1) k, MvPolynomial.eval 0 f ≠ 0 ∧
      ∀ t : k, t ≠ 0 → MvPolynomial.eval (fun _ => t) f ≠ 0 →
        HasMaximalRank (evalMap A t) := by
  let F : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) := fun a => evalMap A (a 0)
  let D : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) :=
    fun a => evalMap (shifted A) (a 0)
  have hF : IsPolynomialFamily F := evalMap_isPolynomialFamily A
  have hD : IsPolynomialFamily D := evalMap_isPolynomialFamily (shifted A)
  have hfactor : ∀ a, F a = F 0 + a 0 • D a :=
    fun a => evalMap_eq_zero_add A (a 0)
  obtain ⟨f, hf, hgood⟩ := maximal_rank_principal_open F D hF hD hfactor hresponse
  exact ⟨f, hf, fun t ht hft => hgood (fun _ => t) ht hft⟩

/-- A good nonzero specialization of an arbitrary polynomial matrix exists. -/
theorem exists_maximal_matrix_parameter [Infinite k] (A : Matrix m n k[X])
    (hresponse : HasMaximalRank (matrixResponse A)) :
    ∃ t : k, t ≠ 0 ∧ HasMaximalRank (evalMap A t) := by
  let F : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) := fun a => evalMap A (a 0)
  let D : (Fin 1 → k) → ((n → k) →ₗ[k] (m → k)) :=
    fun a => evalMap (shifted A) (a 0)
  obtain ⟨a, ha, hgood⟩ := exists_maximal_rank F D
    (evalMap_isPolynomialFamily A) (evalMap_isPolynomialFamily (shifted A))
    (fun a => evalMap_eq_zero_add A (a 0)) hresponse
  exact ⟨a 0, ha, hgood⟩

/-- The good specialization has the usual maximal matrix rank. -/
theorem exists_maximal_matrix_rank [Infinite k] (A : Matrix m n k[X])
    (hresponse : HasMaximalRank (matrixResponse A)) :
    ∃ t : k, t ≠ 0 ∧ (A.map (Polynomial.eval t)).rank =
      min (Fintype.card n) (Fintype.card m) := by
  obtain ⟨t, ht, hgood⟩ := exists_maximal_matrix_parameter A hresponse
  refine ⟨t, ht, ?_⟩
  have hr := (maximalRank_iff_rank_eq_min (evalMap A t)).mp hgood
  unfold Matrix.rank
  erw [hr]
  simp

/-- The full first-variation conclusion holds away from finitely many scalar parameters. -/
theorem finite_nonmaximal_parameters (A : Matrix m n k[X])
    (hresponse : HasMaximalRank (matrixResponse A)) :
    Set.Finite {t : k | ¬HasMaximalRank (evalMap A t)} := by
  obtain ⟨f, hf, hgood⟩ := matrix_first_variation A hresponse
  have hfinite : Set.Finite ({0} ∪ {t : k | MvPolynomial.eval (fun _ => t) f = 0}) :=
    (Set.finite_singleton 0).union (finite_zero_parameters f hf)
  apply hfinite.subset
  intro t ht
  by_cases hzero : t = 0
  · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr hzero)
  · apply Set.mem_union_right
    by_contra hnonzero
    exact ht (hgood t hzero hnonzero)

end PolynomialMatrices

end IdealGeneration.DeformationGeneral
