module

public import IdealGeneration.QuadraticFlag
public import IdealGeneration.QuadraticPairEvaluation

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Directness for the quadratic interpolation flag

The flag contains all base coordinate points and their pairwise sums, and
in each layer contains `z_j` and every paired point `y_(a,0)+y_(a,1)+z_j`.
The mixed image has zero intersection with pairs of quadrics vanishing on
this flag, for arbitrary layer corrections.
-/

noncomputable section
namespace IdealGeneration.QuadraticFlag
open MvPolynomial Module

variable {K I P J : Type*} [Field K] [Fintype I] [Fintype P] [Fintype J]

/-- Vanishing of the mixed pair on the base determines every base coefficient. -/
theorem base_coefficients_zero [DecidableEq I] [DecidableEq J] (c : I → K) (a b : I → J → K)
    (hc : Function.Injective c) (L : I → I ⊕ J → K)
    (hdiag : ∀ i, eval (coordinatePoint (Sum.inl i))
      (multiplication c a b L).1 = 0)
    (hfirst : ∀ i k, eval (coordinatePoint (Sum.inl i) + coordinatePoint (Sum.inl k))
      (multiplication c a b L).1 = 0)
    (hsecond : ∀ i k, eval (coordinatePoint (Sum.inl i) + coordinatePoint (Sum.inl k))
      (multiplication c a b L).2 = 0) :
    ∀ i k, L i (.inl k) = 0 := by
  classical
  have diag (i : I) : L i (.inl i) = 0 := by
    simpa [multiplication, firstGenerator, coordinatePoint] using hdiag i
  intro i k
  by_cases hik : i = k
  · subst k
    exact diag i
  have hp : L i (.inl k) + L k (.inl i) = 0 := by
    have h := hfirst i k
    simp [multiplication, firstGenerator, coordinatePoint, mul_add, add_mul,
      Finset.sum_add_distrib, diag] at h
    simpa only [add_comm] using h
  have hq : c i * L i (.inl k) + c k * L k (.inl i) = 0 := by
    have h := hsecond i k
    simp [multiplication, secondGenerator, coordinatePoint, mul_add, add_mul,
      Finset.sum_add_distrib, diag] at h
    simpa only [add_comm] using h
  have hci : c i - c k ≠ 0 := sub_ne_zero.mpr (fun he => hik (hc he))
  have hm : (c i - c k) * L i (.inl k) = 0 := by
    linear_combination hq - c k * hp
  exact (mul_eq_zero.mp hm).resolve_left hci

/-- Labels for the actual paired interpolation flag. -/
inductive FlagIndex (P J : Type*) where
  | base (i : P × Bool)
  | basePair (i k : P × Bool)
  | layer (j : J)
  | layerPair (p : P) (j : J)

/-- Affine representatives of the flag points. Repetitions in the base labels
have no effect on their common vanishing subspace. -/
def flagPoint (t : FlagIndex P J) : (P × Bool) ⊕ J → K := by
  classical
  exact match t with
  | .base i => coordinatePoint (.inl i)
  | .basePair i k => coordinatePoint (.inl i) + coordinatePoint (.inl k)
  | .layer j => coordinatePoint (.inr j)
  | .layerPair p j => coordinatePoint (.inl (p, false)) +
      coordinatePoint (.inl (p, true)) + coordinatePoint (.inr j)

/-- Polynomials vanishing on a family of affine point representatives. -/
def evaluationKernel {V T : Type*} (points : T → V → K) :
    Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ t, eval (points t) f = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    intro t
    simp [hf t, hg t]
  smul_mem' r f hf := by
    intro t
    simp [hf t]

/-- The quadratic flag's scalar vanishing subspace. -/
def flagVanishing : Submodule K (MvPolynomial ((P × Bool) ⊕ J) K) :=
  evaluationKernel (flagPoint (K := K) (P := P) (J := J))

/-- Flag evaluation is injective on the mixed image. Thus the directness
assertion of (A.2) holds for any number of layers and all layer corrections. -/
theorem mixedImage_disjoint_flagVanishing
    (c : P × Bool → K) (a b : P × Bool → J → K)
    (hc : Function.Injective c) :
    Disjoint (mixedImage c a b) ((flagVanishing (K := K) (P := P) (J := J)).prod
      (flagVanishing (K := K) (P := P) (J := J))) := by
  classical
  rw [Submodule.disjoint_def]
  rintro F ⟨L, rfl⟩ hF
  change (∀ t, eval (flagPoint t) (multiplication c a b L).1 = 0) ∧
    (∀ t, eval (flagPoint t) (multiplication c a b L).2 = 0) at hF
  have hbase : ∀ i k, L i (.inl k) = 0 := base_coefficients_zero c a b hc L
    (fun i => hF.1 (.base i)) (fun i k => hF.1 (.basePair i k))
    (fun i k => hF.2 (.basePair i k))
  have hlayer (p : P) (j : J) :
      L (p, false) (.inr j) = 0 ∧ L (p, true) (.inr j) = 0 := by
    have hf₀ := hF.1 (.layer j)
    have hf₁ := hF.1 (.layerPair p j)
    have hg₀ := hF.2 (.layer j)
    have hg₁ := hF.2 (.layerPair p j)
    simp [flagPoint, multiplication, firstGenerator, coordinatePoint, hbase,
      mul_add, add_mul, Finset.sum_add_distrib] at hf₀ hf₁
    simp [flagPoint, multiplication, secondGenerator, coordinatePoint, hbase,
      mul_add, add_mul, Finset.sum_add_distrib] at hg₀ hg₁
    have hp : L (p, false) (.inr j) + L (p, true) (.inr j) = 0 := by
      linear_combination hf₁ - hf₀
    have hq : c (p, false) * L (p, false) (.inr j) +
        c (p, true) * L (p, true) (.inr j) = 0 := by
      linear_combination hg₁ - hg₀
    have hc' : c (p, false) ≠ c (p, true) := by
      intro h
      have he := congrArg Prod.snd (hc h)
      cases he
    exact coefficients_eq_zero_of_pair_equations hc' hp hq
  have hL : L = 0 := by
    funext i v
    cases v with
    | inl k => exact hbase i k
    | inr j =>
      rcases i with ⟨p, q⟩
      cases q
      · exact (hlayer p j).1
      · exact (hlayer p j).2
  rw [hL, map_zero]

end IdealGeneration.QuadraticFlag
