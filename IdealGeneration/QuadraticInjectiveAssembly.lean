module

public import IdealGeneration.QuadraticPairProjection
public import IdealGeneration.QuadraticInjectiveCore

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# The injective quadratic endpoint

The missing first lift determines the first mixed parameter vector and
both normal parameters. A core probe and the untouched pair probes then
determine the second mixed parameter vector.
-/

noncomputable section
namespace IdealGeneration.QuadraticInjectiveAssembly
open MvPolynomial QuadraticFlag QuadraticElimination QuadraticLiftParameters

variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

abbrev ParameterOmega (K P : Type*) [Field K] :=
  Omega (K := K) (E := (Fin 3 → K) × (P × Bool → K))
    (LinearMap.fst K (Fin 3 → K) (P × Bool → K))

/-- The normal-cubic equations leave two pure coefficients and two mixed vectors. -/
def omegaFromParameters (α β : P × Bool → K) (a b : K) : ParameterOmega K P := by
  refine ⟨((![0, a, b], α), (![-a, -b, 0], β)), ?_⟩
  change normalCubicMap (![0, a, b], ![-a, -b, 0]) = 0
  exact (normalCubicMap_eq_zero_iff _).mpr (by simp)

omit [Fintype P] in
@[simp] theorem omegaFromParameters_val (α β : P × Bool → K) (a b : K) :
    (omegaFromParameters α β a b).val = ((![0, a, b], α), (![-a, -b, 0], β)) := rfl

omit [Fintype P] in
/-- These parameters describe every element of the actual normal-cubic kernel. -/
theorem omegaFromParameters_represents (x : ParameterOmega K P) :
    omegaFromParameters x.val.1.2 x.val.2.2 (x.val.1.1 1) (x.val.1.1 2) = x := by
  have hx : normalCubicMap (x.val.1.1, x.val.2.1) = 0 := x.property
  obtain ⟨h₀, h₁, h₂, h₃⟩ := (normalCubicMap_eq_zero_iff _).mp hx
  apply Subtype.ext
  apply Prod.ext <;> apply Prod.ext
  · funext i
    fin_cases i
    · exact h₀.symm
    · rfl
    · rfl
  · rfl
  · funext i
    fin_cases i
    · change -x.val.1.1 1 = x.val.2.1 0
      linear_combination -h₁
    · change -x.val.1.1 2 = x.val.2.1 1
      linear_combination -h₂
    · exact h₃.symm
  · rfl

/-- The trace and `t` coefficients of the multiplier of the missing first lift. -/
def missingFirstLiftCoefficient
    (U : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g : (P × Bool → K) →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K) :
    ParameterOmega K P →ₗ[K] (MvPolynomial ((P × Bool) ⊕ J) K × K) where
  toFun x := (-lowerPart U g x.val.1, x.val.2.1 0)
  map_add' x y := by
    apply Prod.ext
    · change -lowerPart U g (x.val.1 + y.val.1) = -lowerPart U g x.val.1 + -lowerPart U g y.val.1
      rw [map_add, neg_add]
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · change -lowerPart U g (r • x.val.1) = r • (-lowerPart U g x.val.1)
      rw [map_smul, smul_neg]
    · rfl

omit [Fintype P] [Fintype J] in
@[simp] theorem missingFirstLiftCoefficient_apply
    (U : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g : (P × Bool → K) →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K) (x : ParameterOmega K P) :
    missingFirstLiftCoefficient U g x = (-lowerPart U g x.val.1, x.val.2.1 0) := rfl

/-- The actual multiplier of the omitted generator after normal-degree elimination. -/
def missingFirstLiftMultiplier
    (U : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g : (P × Bool → K) →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K)
    (x : ParameterOmega K P) : MvPolynomial Bool (MvPolynomial ((P × Bool) ⊕ J) K) :=
  C (-lowerPart U g x.val.1) + C (C (x.val.1.1 0)) * X false + C (C (x.val.2.1 0)) * X true

omit [Fintype P] [Fintype J] in
/-- The missing multiplier vanishes precisely when the recorded coefficients vanish. -/
theorem missingFirstLiftMultiplier_eq_zero_iff
    (U : Fin 3 → MvPolynomial ((P × Bool) ⊕ J) K)
    (g : (P × Bool → K) →ₗ[K] MvPolynomial ((P × Bool) ⊕ J) K) (x : ParameterOmega K P) :
    missingFirstLiftMultiplier U g x = 0 ↔ missingFirstLiftCoefficient U g x = 0 := by
  have hx : normalCubicMap (x.val.1.1, x.val.2.1) = 0 := x.property
  have hs : x.val.1.1 0 = 0 := ((normalCubicMap_eq_zero_iff _).mp hx).1
  constructor
  · intro hm
    have ht₀ := congrArg (eval (fun _ : Bool => (0 : MvPolynomial ((P × Bool) ⊕ J) K))) hm
    have ht : -lowerPart U g x.val.1 = 0 := by
      simpa [missingFirstLiftMultiplier] using ht₀
    have hz₀ := congrArg (eval (fun i : Bool => if i then
      (1 : MvPolynomial ((P × Bool) ⊕ J) K) else 0)) hm
    have hz : (C (x.val.2.1 0) : MvPolynomial ((P × Bool) ⊕ J) K) = 0 := by
      simpa [missingFirstLiftMultiplier, ht] using hz₀
    have h := MvPolynomial.C_injective ((P × Bool) ⊕ J) K (hz.trans (map_zero _).symm)
    exact Prod.ext ht h
  · intro hc
    have ht := congrArg Prod.fst hc
    have hz := congrArg Prod.snd hc
    change -lowerPart U g x.val.1 = 0 at ht
    change x.val.2.1 0 = 0 at hz
    simp [missingFirstLiftMultiplier, hs, ht, hz]

/-- Base probes, the normal `t` coefficient, and one nonzero layer value
eliminate the first mixed vector and the two pure parameters. -/
theorem first_parameters_eq_zero (D : QuadraticLiftParameters K P J)
    (α β : P × Bool → K) (a b : K) (j₀ : J)
    (hU₃ : (D.layerCoefficients (2 : Fin 3) j₀).1 ≠ 0)
    (hC : missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)
      (omegaFromParameters α β a b) = 0) : α = 0 ∧ a = 0 ∧ b = 0 := by
  have ha₀ := congrArg Prod.snd hC
  have ha : a = 0 := by
    change -a = 0 at ha₀
    exact neg_eq_zero.mp ha₀
  have htrace₀ := congrArg Prod.fst hC
  change -lowerPart D.firstLift (firstKernelMap D.firstCorrection) (![0, a, b], α) = 0 at htrace₀
  have htrace := neg_eq_zero.mp htrace₀
  have hα : α = 0 := by
    funext i
    have hv := congrArg (eval (traceBasePoint i)) htrace
    simpa [lowerPart, Fin.sum_univ_three, Algebra.smul_def] using hv
  have hb₀ : b • D.firstLift 2 = 0 := by
    simpa [lowerPart, Fin.sum_univ_three, hα, ha] using htrace
  have hv := congrArg (eval (layerPoint j₀)) hb₀
  have hb₁ : b * (D.layerCoefficients (2 : Fin 3) j₀).1 = 0 := by
    simpa [Algebra.smul_def] using hv
  exact ⟨hα, ha, (mul_eq_zero.mp hb₁).resolve_right hU₃⟩

/-- The remaining mixed vector multiplies the kernel generators by `t`. -/
def omegaBeta : (P × Bool → K) →ₗ[K] ParameterOmega K P where
  toFun β := ⟨((0, 0), (0, β)), normalCubicMap.map_zero⟩
  map_add' x y := by
    apply Subtype.ext
    change ((0, 0), (0, x + y)) = ((0, 0), (0, x)) + ((0, 0), (0, y))
    simp
  map_smul' r x := by
    apply Subtype.ext
    change ((0, 0), (0, r • x)) = r • ((0, 0), (0, x))
    simp

omit [Fintype P] in
@[simp] theorem omegaFromParameters_beta (β : P × Bool → K) :
    omegaFromParameters 0 β 0 0 = omegaBeta β := by
  apply Subtype.ext
  have hz : (![0, 0, 0] : Fin 3 → K) = 0 := by
    funext i
    fin_cases i <;> rfl
  change ((![0, 0, 0], 0), (![-0, -0, 0], β)) = ((0, 0), (0, β))
  simp [hz]

/-- The beta vector is the sum of its actual normal multiples of mixed generators. -/
theorem omegaBeta_sum (β : P × Bool → K) :
    omegaBeta β = ∑ i, β i • untouchedOmega (K := K) i (1 : Fin 2) := by
  classical
  have hβ : (∑ i, β i • Pi.single i (1 : K)) = β := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have hsingle (i : P × Bool) :
      omegaBeta (Pi.single i (1 : K)) = untouchedOmega (K := K) i (1 : Fin 2) := by
    apply Subtype.ext
    simp [omegaBeta, untouchedOmega]
  calc
    omegaBeta β = omegaBeta (∑ i, β i • Pi.single i (1 : K)) := congrArg omegaBeta hβ.symm
    _ = _ := by simp only [map_sum, map_smul, hsingle]

/-- Evaluate the two homogeneous components at the same trace representative. -/
def tracePairEvaluation (x : (P × Bool) ⊕ J → K) :
    (Quadrics K ((P × Bool) ⊕ J) × Quadrics K ((P × Bool) ⊕ J)) →ₗ[K] (K × K) :=
  let e := (aeval x).toLinearMap.comp (homogeneousSubmodule ((P × Bool) ⊕ J) K 2).subtype
  e.prodMap e

/-- Evaluate an actual projected eliminated pair. -/
def projectedProbe (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (x : (P × Bool) ⊕ J → K) : ParameterOmega K P →ₗ[K] (K × K) :=
  (tracePairEvaluation x).comp (D.actualProjectedPairMap hc)

@[simp] theorem projectedProbe_apply (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (x : (P × Bool) ⊕ J → K) (w : ParameterOmega K P) :
    projectedProbe D hc x w =
      (eval x (D.actualProjectedPairMap hc w).1.val, eval x (D.actualProjectedPairMap hc w).2.val) := by
  simp [projectedProbe, tracePairEvaluation, MvPolynomial.aeval_eq_eval]

theorem projectedProbe_beta_sum (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (x : (P × Bool) ⊕ J → K) (β : P × Bool → K) :
    projectedProbe D hc x (omegaBeta β) =
      ∑ i, β i • projectedProbe D hc x (untouchedOmega (K := K) i (1 : Fin 2)) := by
  rw [omegaBeta_sum]
  simp only [map_sum, map_smul]

/-- If the other pairs have zero contributions, a probe sees exactly two inputs. -/
theorem projectedProbe_beta_on_pair (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (x : (P × Bool) ⊕ J → K)
    (β : P × Bool → K) (p : P)
    (hoff : ∀ q, q ≠ p → ∀ k : Bool,
      β (q, k) • projectedProbe D hc x (untouchedOmega (q, k) (1 : Fin 2)) = 0) :
    projectedProbe D hc x (omegaBeta β) =
      β (p, false) • projectedProbe D hc x (untouchedOmega (p, false) (1 : Fin 2)) +
      β (p, true) • projectedProbe D hc x (untouchedOmega (p, true) (1 : Fin 2)) := by
  classical
  have sumBool (f : Bool → K × K) : (∑ k, f k) = f false + f true := by
    rw [Fintype.univ_bool, Finset.sum_insert]
    · rw [Finset.sum_singleton, add_comm]
    · decide
  rw [projectedProbe_beta_sum, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · exact sumBool _
  · intro q _ hq
    exact Finset.sum_eq_zero (fun k _ => hoff q hq k)
  · intro h
    exact (h (Finset.mem_univ p)).elim

/-- The determinant-certified core probe recovers both distinguished beta coefficients. -/
theorem beta_core_eq_zero [CharZero K] (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (x : (P × Bool) ⊕ J → K) (β : P × Bool → K)
    (hequal : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
      x (.inl i) = x (.inl (partner i)))
    (hcore₀ : projectedProbe D hc x (untouchedOmega (D.distinguishedPair, false) (1 : Fin 2)) =
      (30, 60))
    (hcore₁ : projectedProbe D hc x (untouchedOmega (D.distinguishedPair, true) (1 : Fin 2)) =
      (75, 75))
    (hz : projectedProbe D hc x (omegaBeta β) = 0) :
    β (D.distinguishedPair, false) = 0 ∧ β (D.distinguishedPair, true) = 0 := by
  have hoff (q : P) (hq : q ≠ D.distinguishedPair) (k : Bool) :
      β (q, k) • projectedProbe D hc x (untouchedOmega (q, k) (1 : Fin 2)) = 0 := by
    have h : projectedProbe D hc x (untouchedOmega (q, k) (1 : Fin 2)) = 0 := by
      simpa using
        D.eval_actualProjectedPairMap_eq_zero_of_same hc (q, k) (1 : Fin 2) hq x
          (hequal (q, k) hq)
    rw [h, smul_zero]
  have hsum := projectedProbe_beta_on_pair D hc x β D.distinguishedPair hoff
  rw [hcore₀, hcore₁] at hsum
  have he := hsum.symm.trans hz
  have hvec : QuadraticInjectiveCore.responseMatrix.mulVec
      ![β (D.distinguishedPair, false), β (D.distinguishedPair, true)] = 0 := by
    funext i
    fin_cases i
    · have h := congrArg Prod.fst he
      change β (D.distinguishedPair, false) * 30 + β (D.distinguishedPair, true) * 75 = 0 at h
      simpa [QuadraticInjectiveCore.responseMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, mul_comm] using h
    · have h := congrArg Prod.snd he
      change β (D.distinguishedPair, false) * 60 + β (D.distinguishedPair, true) * 75 = 0 at h
      simpa [QuadraticInjectiveCore.responseMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, mul_comm] using h
  have hb : (![β (D.distinguishedPair, false), β (D.distinguishedPair, true)] : Fin 2 → K) = 0 :=
    QuadraticInjectiveCore.responseMatrix_injective (hvec.trans (Matrix.mulVec_zero _).symm)
  exact ⟨by simpa using congrFun hb 0, by simpa using congrFun hb 1⟩

/-- Each layer probe separates the two partner slopes in an untouched pair. -/
theorem beta_pair_products_eq_zero (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (β : P × Bool → K)
    (hcore : β (D.distinguishedPair, false) = 0 ∧ β (D.distinguishedPair, true) = 0)
    (p : P) (hp : p ≠ D.distinguishedPair) (j : J)
    (hz : projectedProbe D hc (pairProbe p j) (omegaBeta β) = 0) :
    β (p, false) * D.pairGamma (p, false) (1 : Fin 2) j = 0 ∧
      β (p, true) * D.pairGamma (p, true) (1 : Fin 2) j = 0 := by
  classical
  have hoff (q : P) (hq : q ≠ p) (k : Bool) :
      β (q, k) • projectedProbe D hc (pairProbe p j) (untouchedOmega (q, k) (1 : Fin 2)) = 0 := by
    by_cases hqd : q = D.distinguishedPair
    · subst q
      cases k
      · rw [hcore.1, zero_smul]
      · rw [hcore.2, zero_smul]
    · have he := D.eval_actualProjectedPairMap_pairProbe hc (q, k) (1 : Fin 2) hqd p j
      have h : projectedProbe D hc (pairProbe p j) (untouchedOmega (q, k) (1 : Fin 2)) = 0 := by
        simpa [hq] using he
      rw [h, smul_zero]
  have h₀ : projectedProbe D hc (pairProbe p j) (untouchedOmega (p, false) (1 : Fin 2)) =
      (D.pairGamma (p, false) (1 : Fin 2) j,
        D.slope (p, true) * D.pairGamma (p, false) (1 : Fin 2) j) := by
    simpa [partner] using D.eval_actualProjectedPairMap_pairProbe hc (p, false) (1 : Fin 2) hp p j
  have h₁ : projectedProbe D hc (pairProbe p j) (untouchedOmega (p, true) (1 : Fin 2)) =
      (-D.pairGamma (p, true) (1 : Fin 2) j,
        D.slope (p, false) * (-D.pairGamma (p, true) (1 : Fin 2) j)) := by
    simpa [partner] using D.eval_actualProjectedPairMap_pairProbe hc (p, true) (1 : Fin 2) hp p j
  have hsum := projectedProbe_beta_on_pair D hc (pairProbe p j) β p hoff
  rw [h₀, h₁] at hsum
  have h := hsum.symm.trans hz
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  let a := β (p, false) * D.pairGamma (p, false) (1 : Fin 2) j
  let b := -(β (p, true) * D.pairGamma (p, true) (1 : Fin 2) j)
  have ha : a + b = 0 := by
    dsimp only [a, b]
    change β (p, false) * D.pairGamma (p, false) (1 : Fin 2) j +
      β (p, true) * (-D.pairGamma (p, true) (1 : Fin 2) j) = 0 at hfst
    linear_combination hfst
  have hb : D.slope (p, true) * a + D.slope (p, false) * b = 0 := by
    dsimp only [a, b]
    change β (p, false) * (D.slope (p, true) * D.pairGamma (p, false) (1 : Fin 2) j) +
      β (p, true) * (D.slope (p, false) * (-D.pairGamma (p, true) (1 : Fin 2) j)) = 0 at hsnd
    linear_combination hsnd
  have hne : D.slope (p, true) ≠ D.slope (p, false) := by
    intro he
    have hf : true = false := congrArg Prod.snd (hc he)
    cases hf
  obtain ⟨ha, hb⟩ := coefficients_eq_zero_of_pair_equations hne ha hb
  exact ⟨ha, neg_eq_zero.mp hb⟩

/-- Nonzero layer coefficients on every untouched index complete beta recovery. -/
theorem beta_eq_zero_of_probes [CharZero K] (D : QuadraticLiftParameters K P J)
    (hc : Function.Injective D.slope) (xCore : (P × Bool) ⊕ J → K) (β : P × Bool → K)
    (hequal : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
      xCore (.inl i) = xCore (.inl (partner i)))
    (hcore₀ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, false) (1 : Fin 2)) =
      (30, 60))
    (hcore₁ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, true) (1 : Fin 2)) =
      (75, 75))
    (hγ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∃ j, D.pairGamma i (1 : Fin 2) j ≠ 0)
    (hzCore : projectedProbe D hc xCore (omegaBeta β) = 0)
    (hzPair : ∀ p, p ≠ D.distinguishedPair → ∀ j,
      projectedProbe D hc (pairProbe p j) (omegaBeta β) = 0) : β = 0 := by
  have hcore := beta_core_eq_zero D hc xCore β hequal hcore₀ hcore₁ hzCore
  funext i
  rcases i with ⟨p, k⟩
  change β (p, k) = 0
  by_cases hp : p = D.distinguishedPair
  · subst p
    cases k
    · exact hcore.1
    · exact hcore.2
  · obtain ⟨j, hj⟩ := hγ (p, k) hp
    have hpair := beta_pair_products_eq_zero D hc β hcore p hp j (hzPair p hp j)
    cases k
    · exact (mul_eq_zero.mp hpair.1).resolve_right hj
    · exact (mul_eq_zero.mp hpair.2).resolve_right hj

/-- The coefficient constraint and actual projected probes jointly determine the Omega input. -/
theorem omega_eq_zero_of_constraints_and_probes [CharZero K]
    (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (j₀ : J) (hU₃ : (D.layerCoefficients (2 : Fin 3) j₀).1 ≠ 0)
    (xCore : (P × Bool) ⊕ J → K)
    (hequal : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
      xCore (.inl i) = xCore (.inl (partner i)))
    (hcore₀ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, false) (1 : Fin 2)) =
      (30, 60))
    (hcore₁ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, true) (1 : Fin 2)) =
      (75, 75))
    (hγ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∃ j, D.pairGamma i (1 : Fin 2) j ≠ 0)
    (x : ParameterOmega K P)
    (hC : missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection) x = 0)
    (hzCore : projectedProbe D hc xCore x = 0)
    (hzPair : ∀ p, p ≠ D.distinguishedPair → ∀ j, projectedProbe D hc (pairProbe p j) x = 0) :
    x = 0 := by
  let α := x.val.1.2
  let β := x.val.2.2
  let a := x.val.1.1 1
  let b := x.val.1.1 2
  have hx : omegaFromParameters α β a b = x := omegaFromParameters_represents x
  have hC' : missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)
      (omegaFromParameters α β a b) = 0 := by rw [hx]; exact hC
  obtain ⟨hα, ha, hb⟩ := first_parameters_eq_zero D α β a b j₀ hU₃ hC'
  have hβx : omegaBeta β = x := by simpa only [hα, ha, hb, omegaFromParameters_beta] using hx
  rw [← hβx] at hzCore hzPair
  have hβ := beta_eq_zero_of_probes D hc xCore β hequal hcore₀ hcore₁ hγ hzCore hzPair
  rw [← hβx, hβ, map_zero]

/-- The missing-generator constraint together with the actual projected image is injective. -/
theorem constraintProjected_injective [CharZero K]
    (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (j₀ : J) (hU₃ : (D.layerCoefficients (2 : Fin 3) j₀).1 ≠ 0)
    (xCore : (P × Bool) ⊕ J → K)
    (hequal : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
      xCore (.inl i) = xCore (.inl (partner i)))
    (hcore₀ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, false) (1 : Fin 2)) =
      (30, 60))
    (hcore₁ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, true) (1 : Fin 2)) =
      (75, 75))
    (hγ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∃ j, D.pairGamma i (1 : Fin 2) j ≠ 0) :
    Function.Injective ((missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)).prod
      (D.actualProjectedPairMap hc)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hC := congrArg Prod.fst hx
  have hW := congrArg Prod.snd hx
  change D.actualProjectedPairMap hc x = 0 at hW
  have hz (z : (P × Bool) ⊕ J → K) : projectedProbe D hc z x = 0 := by
    change tracePairEvaluation z (D.actualProjectedPairMap hc x) = 0
    rw [hW, map_zero]
  exact omega_eq_zero_of_constraints_and_probes D hc j₀ hU₃ xCore hequal hcore₀ hcore₁ hγ
    x hC (hz xCore) (fun p _ j => hz (pairProbe p j))

/-- Retain the missing-generator coefficients and only the actual probe values. -/
def constraintProbeMap (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (xCore : (P × Bool) ⊕ J → K) : ParameterOmega K P →ₗ[K]
      ((MvPolynomial ((P × Bool) ⊕ J) K × K) × ((K × K) × (P → J → K × K))) :=
  (missingFirstLiftCoefficient D.firstLift (firstKernelMap D.firstCorrection)).prod
    ((projectedProbe D hc xCore).prod
      (LinearMap.pi fun p => LinearMap.pi fun j => projectedProbe D hc (pairProbe p j)))

/-- The actual coefficient and probe tests are jointly injective. -/
theorem constraintProbe_injective [CharZero K]
    (D : QuadraticLiftParameters K P J) (hc : Function.Injective D.slope)
    (j₀ : J) (hU₃ : (D.layerCoefficients (2 : Fin 3) j₀).1 ≠ 0)
    (xCore : (P × Bool) ⊕ J → K)
    (hequal : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair →
      xCore (.inl i) = xCore (.inl (partner i)))
    (hcore₀ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, false) (1 : Fin 2)) =
      (30, 60))
    (hcore₁ : projectedProbe D hc xCore (untouchedOmega (D.distinguishedPair, true) (1 : Fin 2)) =
      (75, 75))
    (hγ : ∀ i : P × Bool, i.1 ≠ D.distinguishedPair → ∃ j, D.pairGamma i (1 : Fin 2) j ≠ 0) :
    Function.Injective (constraintProbeMap D hc xCore) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hC := congrArg Prod.fst hx
  have hp := congrArg Prod.snd hx
  have hCore := congrArg Prod.fst hp
  have hPairs := congrArg Prod.snd hp
  exact omega_eq_zero_of_constraints_and_probes D hc j₀ hU₃ xCore hequal hcore₀ hcore₁ hγ
    x hC hCore (fun p _ j => congrFun (congrFun hPairs p) j)

end IdealGeneration.QuadraticInjectiveAssembly
