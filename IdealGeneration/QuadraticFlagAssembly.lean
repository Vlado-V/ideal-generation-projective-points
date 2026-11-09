module

public import IdealGeneration.QuadraticFlagParameters
public import IdealGeneration.QuadraticFlagDecomposition
public import IdealGeneration.Numerics
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Dimension assembly for the quadratic flag

The scalar interpolation count and the mixed-product dimension add up to
exactly the dimension prescribed by the point conditions in Appendix A.2.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial Module

variable {K V : Type*} [Field K] [Fintype V]

/-- Homogeneous forms with an arbitrary finite variable set. -/
def homogeneousBasis (d : ℕ) :
    Basis (Sym V d) K (homogeneousSubmodule V K d) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : V →₀ ℕ | e.degree = d}).reindex
    (Sym.equivNatSum V d).symm

instance homogeneousFinite (d : ℕ) : Module.Finite K (homogeneousSubmodule V K d) := by
  classical
  exact Module.Finite.of_basis (homogeneousBasis (K := K) (V := V) d)

/-- The dimension of forms depends only on the number of variables. -/
theorem finrank_homogeneousSubmodule (d : ℕ) :
    finrank K (homogeneousSubmodule V K d) = N (Fintype.card V) d := by
  classical
  rw [Module.finrank_eq_card_basis (homogeneousBasis (K := K) (V := V) d),
    Sym.card_sym_eq_choose]
  rfl

/-- Twice the quadratic monomial count, without natural-number division. -/
theorem two_mul_quadratic_count (n : ℕ) : 2 * N n 2 = n * (n + 1) := by
  cases n with
  | zero => simp [N]
  | succ n =>
    have h := N_degree_recurrence (n + 1) 1 (by omega)
    simpa [Nat.mul_comm] using h

/-- The number of independent scalar conditions in the paired flag. -/
def flagCount (h l : ℕ) : ℕ := N h 2 + l * (h / 2 + 1)

/-- The scalar count has the required codimension in pairs of quadrics. -/
theorem two_mul_flagCount (h l : ℕ) (heven : Even h) :
    2 * flagCount h l = h * (h + l) + (h + 2 * l) := by
  obtain ⟨k, rfl⟩ := heven
  have hn := two_mul_quadratic_count (k + k)
  unfold flagCount
  have hk : (k + k) / 2 = k := by omega
  rw [hk]
  nlinarith

/-- There are enough scalar quadrics for all flag values. -/
theorem flagCount_le_quadratic_count (h l : ℕ) (heven : Even h) :
    flagCount h l ≤ N (h + l) 2 := by
  have hp := two_mul_flagCount h l heven
  have hn := two_mul_quadratic_count (h + l)
  by_cases hl : l = 0
  · subst l
    simp [flagCount]
  · have hl' : 1 ≤ l := by omega
    have hm : l ≤ l * l := by nlinarith
    nlinarith

/-- The numerical dimension identity in Appendix A.2. -/
theorem quadratic_flag_dimension_identity (h l : ℕ) (heven : Even h) :
    h * (h + l) + 2 * (N (h + l) 2 - flagCount h l) =
      2 * N (h + l) 2 - (h + 2 * l) := by
  have hp := two_mul_flagCount h l heven
  have hle := flagCount_le_quadratic_count h l heven
  omega

/-- A disjoint sum contained in a finite-dimensional space fills it once
its dimensions exhaust that space. -/
theorem eq_sup_of_disjoint_finrank {M : Type*} [AddCommGroup M] [Module K M]
    (U W A : Submodule K M) [FiniteDimensional K U]
    [FiniteDimensional K W] [FiniteDimensional K A]
    (hU : U ≤ A) (hW : W ≤ A) (hdisjoint : Disjoint U W)
    (hdim : finrank K U + finrank K W = finrank K A) :
    A = U ⊔ W := by
  apply (Submodule.eq_of_le_of_finrank_eq (sup_le hU hW) ?_).symm
  have hsum := U.finrank_sup_add_finrank_inf_eq W
  rw [hdisjoint.eq_bot, finrank_bot, add_zero] at hsum
  exact hsum.trans hdim

variable {P J : Type*} [Fintype P] [Fintype J]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq P := Classical.decEq P
local instance : DecidableEq J := Classical.decEq J

/-- The quadratic with prescribed values at the base coordinate points. -/
def diagonalQuadratic (v : P × Bool → K) : Quadrics K (P × Bool) :=
  ⟨∑ i, C (v i) * X i ^ 2, by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X_pow _ _ _⟩

@[simp] theorem eval_diagonalQuadratic (v : P × Bool → K) (i : P × Bool) :
    eval (coordinatePoint i) (diagonalQuadratic v).val = v i := by
  classical
  simp [diagonalQuadratic, coordinatePoint]

/-- An explicit right inverse to a nonzero normal functional. -/
def normalSection (n : K × K) (t : K) : K × K :=
  if n.1 = 0 then (0, t / n.2) else (t / n.1, 0)

theorem normalSection_spec (n : K × K) (hn : n ≠ 0) (t : K) :
    n.1 * (normalSection n t).1 + n.2 * (normalSection n t).2 = t := by
  by_cases h : n.1 = 0
  · have hn2 : n.2 ≠ 0 := by
      intro he
      apply hn
      exact Prod.ext h he
    simp [normalSection, h]
    exact mul_div_cancel₀ t hn2
  · simp [normalSection, h]
    exact mul_div_cancel₀ t h

/-- The actual normal conditions at the base and the two designated
points in each layer. -/
def quadraticConditionMap (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K) :
    (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) →ₗ[K]
      ((P × Bool → K) × ((J → K) × (J → K))) where
  toFun F :=
    let f := scalarFlagEvaluation F.1
    let g := scalarFlagEvaluation F.2
    (fun i => eval (coordinatePoint i) g.1.val - c i * eval (coordinatePoint i) f.1.val,
     (fun j => (n₀ j).1 * f.2.1 j + (n₀ j).2 * g.2.1 j,
      fun j => (n₁ j).1 * f.2.2 (p₀, j) + (n₁ j).2 * g.2.2 (p₀, j)))
  map_add' F G := by
    ext i <;> simp <;> ring
  map_smul' r F := by
    ext i <;> simp <;> ring

/-- Each of the `h+2l` point conditions is independent. -/
theorem quadraticConditionMap_surjective (c : P × Bool → K) (p₀ : P)
    (n₀ n₁ : J → K × K) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0) :
    Function.Surjective (quadraticConditionMap c p₀ n₀ n₁) := by
  intro t
  let dF : ScalarFlagData (K := K) (P := P) (J := J) :=
    (0, (fun j => (normalSection (n₀ j) (t.2.1 j)).1,
      fun q => (normalSection (n₁ q.2) (t.2.2 q.2)).1))
  let dG : ScalarFlagData (K := K) (P := P) (J := J) :=
    (diagonalQuadratic t.1, (fun j => (normalSection (n₀ j) (t.2.1 j)).2,
      fun q => (normalSection (n₁ q.2) (t.2.2 q.2)).2))
  obtain ⟨f, hf⟩ := scalarFlagEvaluation_surjective dF
  obtain ⟨g, hg⟩ := scalarFlagEvaluation_surjective dG
  refine ⟨(f, g), ?_⟩
  change (fun i => eval (coordinatePoint i) (scalarFlagEvaluation g).1.val -
      c i * eval (coordinatePoint i) (scalarFlagEvaluation f).1.val,
    (fun j => (n₀ j).1 * (scalarFlagEvaluation f).2.1 j +
      (n₀ j).2 * (scalarFlagEvaluation g).2.1 j,
    fun j => (n₁ j).1 * (scalarFlagEvaluation f).2.2 (p₀, j) +
      (n₁ j).2 * (scalarFlagEvaluation g).2.2 (p₀, j))) = t
  rw [hf, hg]
  apply Prod.ext
  · funext i
    simp [dF, dG]
  · apply Prod.ext <;> funext j
    · exact normalSection_spec (n₀ j) (hn₀ j) _
    · exact normalSection_spec (n₁ j) (hn₁ j) _

/-- Allowed quadratic pairs for the normal point conditions. -/
def allowedQuadraticPairs (c : P × Bool → K) (p₀ : P) (n₀ n₁ : J → K × K) :=
  LinearMap.ker (quadraticConditionMap c p₀ n₀ n₁)

/-- The scalar flag kernel retaining its homogeneous quadratic ambient. -/
def scalarFlagKernel : Submodule K (Quadrics K ((P × Bool) ⊕ J)) :=
  LinearMap.ker scalarFlagEvaluation

/-- Its dimension is the quadratic monomial count minus the flag count. -/
theorem finrank_scalarFlagKernel :
    finrank K (scalarFlagKernel (K := K) (P := P) (J := J)) =
      N (Fintype.card (P × Bool) + Fintype.card J) 2 -
        flagCount (Fintype.card (P × Bool)) (Fintype.card J) := by
  have h := (scalarFlagEvaluation (K := K) (P := P) (J := J)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr scalarFlagEvaluation_surjective, finrank_top] at h
  simp only [ScalarFlagData, Module.finrank_prod, Module.finrank_pi,
    finrank_homogeneousSubmodule, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum] at h ⊢
  unfold scalarFlagKernel flagCount
  have heq : Fintype.card P * 2 / 2 = Fintype.card P := by omega
  rw [heq]
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at h ⊢
  omega

/-- The dimension of the allowed space is determined by all actual point conditions. -/
theorem finrank_allowedQuadraticPairs (c : P × Bool → K) (p₀ : P)
    (n₀ n₁ : J → K × K) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0) :
    finrank K (allowedQuadraticPairs c p₀ n₀ n₁) =
      2 * N (Fintype.card (P × Bool) + Fintype.card J) 2 -
        (Fintype.card (P × Bool) + 2 * Fintype.card J) := by
  have h := (quadraticConditionMap c p₀ n₀ n₁).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quadraticConditionMap_surjective c p₀ n₀ n₁ hn₀ hn₁),
    finrank_top] at h
  simp only [Module.finrank_prod, Module.finrank_pi,
    finrank_homogeneousSubmodule, Fintype.card_sum] at h
  unfold allowedQuadraticPairs
  omega

/-- The polynomial multiplication map with its homogeneous target recorded. -/
def quadraticMultiplication (c : P × Bool → K) (a b : P × Bool → J → K) :
    (P × Bool → (P × Bool) ⊕ J → K) →ₗ[K]
      (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) where
  toFun L := (⟨(multiplication c a b L).1, (multiplication_isHomogeneous c a b L).1⟩,
    ⟨(multiplication c a b L).2, (multiplication_isHomogeneous c a b L).2⟩)
  map_add' L M := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((multiplication c a b).map_add L M)
    · exact congrArg Prod.snd ((multiplication c a b).map_add L M)
  map_smul' r L := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((multiplication c a b).map_smul r L)
    · exact congrArg Prod.snd ((multiplication c a b).map_smul r L)

def quadraticMixedImage (c : P × Bool → K) (a b : P × Bool → J → K) :=
  (quadraticMultiplication c a b).range

theorem quadraticMultiplication_injective (c : P × Bool → K)
    (a b : P × Bool → J → K) (hc : Function.Injective c) :
    Function.Injective (quadraticMultiplication c a b) := by
  intro L M h
  apply multiplication_injective c a b hc
  exact congrArg (fun F => (F.1.val, F.2.val)) h

theorem finrank_quadraticMixedImage (c : P × Bool → K)
    (a b : P × Bool → J → K) (hc : Function.Injective c) :
    finrank K (quadraticMixedImage c a b) =
      Fintype.card (P × Bool) * (Fintype.card (P × Bool) + Fintype.card J) := by
  rw [quadraticMixedImage, LinearMap.finrank_range_of_inj
    (quadraticMultiplication_injective c a b hc)]
  simp [Module.finrank_pi_fintype, Fintype.card_sum]

/-- The genuine flag-vanishing quadrics. -/
def quadraticFlagVanishing : Submodule K (Quadrics K ((P × Bool) ⊕ J)) :=
  (flagVanishing (K := K) (P := P) (J := J)).comap
    (homogeneousSubmodule ((P × Bool) ⊕ J) K 2).subtype

omit [Fintype P] [Fintype J] in
@[simp] private theorem lift_coordinatePoint (i : P × Bool) :
    Sum.elim (coordinatePoint (K := K) i) (fun _ : J => 0) =
      coordinatePoint (Sum.inl i) := by
  funext v
  cases v <;> simp [coordinatePoint]

omit [Fintype P] [Fintype J] in
omit [Fintype P] [Fintype J] in
@[simp] private theorem lift_coordinatePoint_add (i k : P × Bool) :
    Sum.elim (coordinatePoint (K := K) i + coordinatePoint k) (fun _ : J => 0) =
      coordinatePoint (Sum.inl i) + coordinatePoint (Sum.inl k) := by
  funext v
  cases v <;> simp [coordinatePoint]

omit [Fintype P] [Fintype J] in
private theorem layerPoint_eq_flagPoint (j : J) :
    layerPoint (K := K) (P := P) j = flagPoint (.layer j) := by
  classical
  funext v
  cases v <;> simp [layerPoint, flagPoint, coordinatePoint]

omit [Fintype P] [Fintype J] in
private theorem pairedLayerPoint_eq_flagPoint (p : P) (j : J) :
    pairedLayerPoint (K := K) p j = flagPoint (.layerPair p j) := by
  classical
  funext v
  cases v <;> simp [pairedLayerPoint, flagPoint, pairPoint, coordinatePoint]

omit [Fintype P] [Fintype J] in
/-- Recording the full base restriction implies vanishing on every base flag point. -/
theorem scalarFlagKernel_le_quadraticFlagVanishing :
    scalarFlagKernel (K := K) (P := P) (J := J) ≤ quadraticFlagVanishing := by
  classical
  intro f hf
  change scalarFlagEvaluation f = 0 at hf
  have hb := congrArg (fun d : ScalarFlagData (K := K) (P := P) (J := J) => d.1.val) hf
  have hl := congrArg (fun d : ScalarFlagData (K := K) (P := P) (J := J) => d.2.1) hf
  have hp := congrArg (fun d : ScalarFlagData (K := K) (P := P) (J := J) => d.2.2) hf
  change ∀ t, eval (flagPoint t) f.val = 0
  intro t
  cases t with
  | base i =>
    have h := congrArg (eval (coordinatePoint i)) hb
    simpa [scalarFlagEvaluation, eval_restrictBase, flagPoint] using h
  | basePair i k =>
    have h := congrArg (eval (coordinatePoint i + coordinatePoint k)) hb
    simpa [scalarFlagEvaluation, eval_restrictBase, flagPoint] using h
  | layer j =>
    have h := congrFun hl j
    simpa [scalarFlagEvaluation, layerPoint_eq_flagPoint] using h
  | layerPair p j =>
    have h := congrFun hp (p, j)
    simpa [scalarFlagEvaluation, pairedLayerPoint_eq_flagPoint] using h

/-- The mixed image meets the genuine scalar flag ideal only in zero. -/
theorem quadraticMixedImage_disjoint (c : P × Bool → K)
    (a b : P × Bool → J → K) (hc : Function.Injective c) :
    Disjoint (quadraticMixedImage c a b)
      ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
        (quadraticFlagVanishing (K := K) (P := P) (J := J))) := by
  rw [Submodule.disjoint_def]
  rintro F ⟨L, rfl⟩ hF
  have hzero := (Submodule.disjoint_def.mp (mixedImage_disjoint_flagVanishing c a b hc))
    (multiplication c a b L) ⟨L, rfl⟩ hF
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hzero
  · exact congrArg Prod.snd hzero

omit [Fintype P] [Fintype J] in
/-- Genuine flag-vanishing pairs satisfy all selected normal conditions. -/
theorem quadraticFlagVanishing_prod_le_allowed (c : P × Bool → K)
    (p₀ : P) (n₀ n₁ : J → K × K) :
    (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod
      quadraticFlagVanishing ≤ allowedQuadraticPairs c p₀ n₀ n₁ := by
  classical
  rintro ⟨f, g⟩ ⟨hf, hg⟩
  change (∀ t, eval (flagPoint t) f.val = 0) at hf
  change (∀ t, eval (flagPoint t) g.val = 0) at hg
  change quadraticConditionMap c p₀ n₀ n₁ (f, g) = 0
  apply Prod.ext
  · funext i
    have hfi := hf (.base i)
    have hgi := hg (.base i)
    simpa [quadraticConditionMap, scalarFlagEvaluation, eval_restrictBase,
      flagPoint] using show
      eval (flagPoint (.base i)) g.val - c i * eval (flagPoint (.base i)) f.val = 0 by
        rw [hfi, hgi]
        simp
  · apply Prod.ext <;> funext j
    · simp [quadraticConditionMap, scalarFlagEvaluation, layerPoint_eq_flagPoint,
        hf (.layer j), hg (.layer j)]
    · simp [quadraticConditionMap, scalarFlagEvaluation, pairedLayerPoint_eq_flagPoint,
        hf (.layerPair p₀ j), hg (.layerPair p₀ j)]

/-- Membership of each linear generator implies membership of its entire
mixed multiplication image in the normal-condition space. -/
theorem quadraticMixedImage_le_allowed (c : P × Bool → K)
    (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
    (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
      (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0) :
    quadraticMixedImage c a b ≤ allowedQuadraticPairs c p₀ n₀ n₁ := by
  classical
  rintro F ⟨L, rfl⟩
  change quadraticConditionMap c p₀ n₀ n₁ (quadraticMultiplication c a b L) = 0
  apply Prod.ext
  · funext i
    simp [quadraticConditionMap, scalarFlagEvaluation, quadraticMultiplication,
      eval_restrictBase, multiplication, firstGenerator, secondGenerator, coordinatePoint]
  · apply Prod.ext <;> funext j
    · change (n₀ j).1 * eval (layerPoint j) (multiplication c a b L).1 +
        (n₀ j).2 * eval (layerPoint j) (multiplication c a b L).2 = 0
      change (n₀ j).1 * eval (layerPoint j) (∑ i, firstGenerator a i * linearPolynomial (L i)) +
        (n₀ j).2 * eval (layerPoint j) (∑ i, secondGenerator c b i * linearPolynomial (L i)) = 0
      simp only [map_sum, map_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      have hi : (n₀ j).1 * eval (layerPoint j) (firstGenerator a i) +
          (n₀ j).2 * eval (layerPoint j) (secondGenerator c b i) = 0 := by
        simpa [firstGenerator, secondGenerator, layerPoint, coordinatePoint] using h₀ i j
      calc
        _ = ((n₀ j).1 * eval (layerPoint j) (firstGenerator a i) +
            (n₀ j).2 * eval (layerPoint j) (secondGenerator c b i)) *
              eval (layerPoint j) (linearPolynomial (L i)) := by ring
        _ = 0 := by rw [hi, zero_mul]
    · change (n₁ j).1 * eval (pairedLayerPoint p₀ j) (multiplication c a b L).1 +
        (n₁ j).2 * eval (pairedLayerPoint p₀ j) (multiplication c a b L).2 = 0
      change (n₁ j).1 * eval (pairedLayerPoint p₀ j)
          (∑ i, firstGenerator a i * linearPolynomial (L i)) +
        (n₁ j).2 * eval (pairedLayerPoint p₀ j)
          (∑ i, secondGenerator c b i * linearPolynomial (L i)) = 0
      simp only [map_sum, map_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      have hi : (n₁ j).1 * eval (pairedLayerPoint p₀ j) (firstGenerator a i) +
          (n₁ j).2 * eval (pairedLayerPoint p₀ j) (secondGenerator c b i) = 0 := by
        simpa [firstGenerator, secondGenerator, pairedLayerPoint, coordinatePoint] using h₁ i j
      calc
        _ = ((n₁ j).1 * eval (pairedLayerPoint p₀ j) (firstGenerator a i) +
            (n₁ j).2 * eval (pairedLayerPoint p₀ j) (secondGenerator c b i)) *
              eval (pairedLayerPoint p₀ j) (linearPolynomial (L i)) := by ring
        _ = 0 := by rw [hi, zero_mul]

/-- Appendix A.2. The actual normal-condition space is the internal direct sum
of mixed products and pairs of quadrics vanishing on the whole flag. -/
theorem quadratic_flag_direct_sum (c : P × Bool → K)
    (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
    (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
    (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
      (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0) :
    allowedQuadraticPairs c p₀ n₀ n₁ = quadraticMixedImage c a b ⊔
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J)) ∧
    Disjoint (quadraticMixedImage c a b)
      ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J))) := by
  have hU := quadraticMixedImage_le_allowed c a b p₀ n₀ n₁ h₀ h₁
  have hW := quadraticFlagVanishing_prod_le_allowed c p₀ n₀ n₁
  have hSW : (scalarFlagKernel (K := K) (P := P) (J := J)).prod (scalarFlagKernel (K := K) (P := P) (J := J)) ≤
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J)) :=
    Submodule.prod_mono
      (scalarFlagKernel_le_quadraticFlagVanishing (K := K) (P := P) (J := J))
      (scalarFlagKernel_le_quadraticFlagVanishing (K := K) (P := P) (J := J))
  have hdis := quadraticMixedImage_disjoint c a b hc
  have hstrong : allowedQuadraticPairs c p₀ n₀ n₁ = quadraticMixedImage c a b ⊔
      (scalarFlagKernel (K := K) (P := P) (J := J)).prod (scalarFlagKernel (K := K) (P := P) (J := J)) := by
    apply eq_sup_of_disjoint_finrank _ _ _ hU (hSW.trans hW) (hdis.mono_right hSW)
    have : Module.Free K (scalarFlagKernel (K := K) (P := P) (J := J)) := by
      with_unfolding_all exact Module.Free.of_divisionRing K (scalarFlagKernel (K := K) (P := P) (J := J))
    rw [finrank_quadraticMixedImage c a b hc,
      (Submodule.prodEquiv (scalarFlagKernel (K := K) (P := P) (J := J))
        (scalarFlagKernel (K := K) (P := P) (J := J))).finrank_eq,
      Module.finrank_prod, finrank_scalarFlagKernel, finrank_allowedQuadraticPairs c p₀ n₀ n₁ hn₀ hn₁]
    have heven : Even (Fintype.card (P × Bool)) := by
      refine ⟨Fintype.card P, ?_⟩
      simp [Fintype.card_prod, Nat.mul_two]
    simpa only [two_mul] using quadratic_flag_dimension_identity
      (Fintype.card (P × Bool)) (Fintype.card J) heven
  constructor
  · apply le_antisymm
    · rw [hstrong]
      exact sup_le_sup_left hSW _
    · exact sup_le hU hW
  · exact hdis

/-- Independent normal directions produce the full quadratic direct sum with
explicitly solvable layer corrections. -/
theorem exists_quadratic_flag_direct_sum (c : P × Bool → K) (p₀ : P)
    (n₀ n₁ : J → K × K) (hc : Function.Injective c)
    (hdet : ∀ j, (n₀ j).1 * (n₁ j).2 - (n₁ j).1 * (n₀ j).2 ≠ 0) :
    ∃ a b : P × Bool → J → K,
      allowedQuadraticPairs c p₀ n₀ n₁ = quadraticMixedImage c a b ⊔
        (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J)) ∧
      Disjoint (quadraticMixedImage c a b)
        ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J))) := by
  obtain ⟨a, b, h₀, h₁⟩ := exists_layerCorrections c p₀ n₀ n₁ hdet
  have hn₀ (j : J) : n₀ j ≠ 0 := by
    intro hz
    have h := hdet j
    simp [hz] at h
  have hn₁ (j : J) : n₁ j ≠ 0 := by
    intro hz
    have h := hdet j
    simp [hz] at h
  exact ⟨a, b, quadratic_flag_direct_sum c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁⟩

/-- The actual scalar flag imposes the stated number of independent conditions. -/
theorem finrank_quadraticFlagVanishing (c : P × Bool → K) (p₀ : P)
    (hc : Function.Injective c) :
    finrank K (quadraticFlagVanishing (K := K) (P := P) (J := J)) =
      N (Fintype.card (P × Bool) + Fintype.card J) 2 -
        flagCount (Fintype.card (P × Bool)) (Fintype.card J) := by
  let n₀ : J → K × K := fun _ => (1, 0)
  let n₁ : J → K × K := fun _ => (0, 1)
  have hdet : ∀ j, (n₀ j).1 * (n₁ j).2 - (n₁ j).1 * (n₀ j).2 ≠ 0 := by
    intro j
    simp [n₀, n₁]
  obtain ⟨a, b, hA, hdis⟩ := exists_quadratic_flag_direct_sum c p₀ n₀ n₁ hc hdet
  have : Module.Free K (quadraticFlagVanishing (K := K) (P := P) (J := J)) := by
    with_unfolding_all exact Module.Free.of_divisionRing K (quadraticFlagVanishing (K := K) (P := P) (J := J))
  have hsum := (quadraticMixedImage c a b).finrank_sup_add_finrank_inf_eq
    ((quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J)))
  rw [← hA, hdis.eq_bot, finrank_bot, add_zero] at hsum
  rw [finrank_allowedQuadraticPairs c p₀ n₀ n₁ (by simp [n₀]) (by simp [n₁]),
    finrank_quadraticMixedImage c a b hc,
    (Submodule.prodEquiv (quadraticFlagVanishing (K := K) (P := P) (J := J))
      (quadraticFlagVanishing (K := K) (P := P) (J := J))).finrank_eq,
    Module.finrank_prod] at hsum
  have heven : Even (Fintype.card (P × Bool)) := by
    refine ⟨Fintype.card P, ?_⟩
    simp [Fintype.card_prod, Nat.mul_two]
  have hn := quadratic_flag_dimension_identity
    (Fintype.card (P × Bool)) (Fintype.card J) heven
  omega

/-- Whole-base restriction and evaluation on the finite scalar flag have the
same quadratic kernel. -/
theorem scalarFlagKernel_eq_quadraticFlagVanishing (c : P × Bool → K) (p₀ : P)
    (hc : Function.Injective c) :
    scalarFlagKernel (K := K) (P := P) (J := J) = quadraticFlagVanishing := by
  apply Submodule.eq_of_le_of_finrank_eq scalarFlagKernel_le_quadraticFlagVanishing
  rw [finrank_scalarFlagKernel, finrank_quadraticFlagVanishing c p₀ hc]

/-- Addition identifies disjoint submodules with their internal sum. -/
def disjointSumEquiv {M : Type*} [AddCommGroup M] [Module K M]
    (U W : Submodule K M) (hd : Disjoint U W) : (U × W) ≃ₗ[K] ↥(U ⊔ W) := by
  let f := U.subtype.coprod W.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    dsimp only [f]
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ (by simpa using hd)]
    simp
  exact (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofEq _ _ (by simp [f, LinearMap.range_coprod]))

/-- The linear splitting associated to the quadratic direct sum. -/
def quadraticFlagSplitting (c : P × Bool → K)
    (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
    (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
    (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
      (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0) :
    (quadraticMixedImage c a b ×
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J))) ≃ₗ[K]
        allowedQuadraticPairs c p₀ n₀ n₁ :=
  let h := quadratic_flag_direct_sum c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁
  (disjointSumEquiv _ _ h.2).trans (LinearEquiv.ofEq _ _ h.1.symm)

/-- Projection onto the pairs of scalar flag ideals along mixed products. -/
def quadraticFlagProjection (c : P × Bool → K)
    (a b : P × Bool → J → K) (p₀ : P) (n₀ n₁ : J → K × K)
    (hc : Function.Injective c) (hn₀ : ∀ j, n₀ j ≠ 0) (hn₁ : ∀ j, n₁ j ≠ 0)
    (h₀ : ∀ i j, (n₀ j).1 * a i j + (n₀ j).2 * b i j = 0)
    (h₁ : ∀ i j, (n₁ j).1 * (pairPoint p₀ i + a i j) +
      (n₁ j).2 * (c i * pairPoint p₀ i + b i j) = 0) :
    allowedQuadraticPairs c p₀ n₀ n₁ →ₗ[K]
      (quadraticFlagVanishing (K := K) (P := P) (J := J)).prod (quadraticFlagVanishing (K := K) (P := P) (J := J)) :=
  (LinearMap.snd K _ _).comp
    (quadraticFlagSplitting c a b p₀ n₀ n₁ hc hn₀ hn₁ h₀ h₁).symm.toLinearMap

end IdealGeneration.QuadraticFlag
