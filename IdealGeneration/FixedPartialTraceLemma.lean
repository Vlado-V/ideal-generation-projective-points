module

public import IdealGeneration.FixedPointEulerWitness

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# A prescribed partial trace condition

This is the fixed-subspace assertion of Lemma 3.6. Adjacent ideal-generation
assertions supply a maximal-rank evaluation at the prescribed point. The
stabilizer acts through the full linear group on its fiber, so the remaining
points can be moved while the point and its prescribed subspace stay fixed.
-/

noncomputable section
namespace IdealGeneration
open Module MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {n p d : ℕ}

local instance partialLemmaRelationGroup : AddCommGroup (EulerRelations K n d) :=
  Module.addCommMonoidToAddCommGroup K

local instance partialLemmaRelationSubmoduleGroup (B : Submodule K (EulerRelations K n d)) :
    AddCommGroup B := Module.addCommMonoidToAddCommGroup K

/-- The stabilizer of the fixed point changes the evaluation image by its
full dual linear action. -/
theorem fixedPartialTrace_stabilizer_finrank [Infinite K]
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (b : PointCoordinates K n p) :
    finrank K (fixedPartialTraceEvaluation y L b d).ker =
      finrank K ((eulerTraceEvaluation (affineCoordinates y y e b) d).prod
        (L.mkQ.comp ((coordinateDualEquiv e).toLinearMap.comp (eulerTraceAt y d)))).ker := by
  let T := affineEulerEquiv y y e d
  let U := (fixedPartialTraceEvaluation y L b d).ker
  have heval (f : EulerRelations K n d) :
      eulerTraceAt y d (T f) = coordinateDualEquiv e (eulerTraceAt y d f) :=
    affineEulerEquiv_evaluation y y e f
  have hfull (f : EulerRelations K n d) :
      eulerTraceEvaluation b d (T f) = 0 ↔
        eulerTraceEvaluation (affineCoordinates y y e b) d f = 0 := by
    change T f ∈ (eulerTraceEvaluation b d).ker ↔
      f ∈ (eulerTraceEvaluation (affineCoordinates y y e b) d).ker
    rw [eulerTraceEvaluation_ker_eq, eulerTraceEvaluation_ker_eq]
    exact affineEulerEquiv_evaluation_eq_zero_iff y y e b f
  have hU : U.comap T.toLinearMap =
      ((eulerTraceEvaluation (affineCoordinates y y e b) d).prod
        (L.mkQ.comp ((coordinateDualEquiv e).toLinearMap.comp (eulerTraceAt y d)))).ker := by
    ext f
    change (eulerTraceEvaluation b d (T f), L.mkQ (eulerTraceAt y d (T f))) = 0 ↔
      (eulerTraceEvaluation (affineCoordinates y y e b) d f,
        L.mkQ (coordinateDualEquiv e (eulerTraceAt y d f))) = 0
    simp only [Prod.mk_eq_zero, heval, hfull]
  exact (T.ofSubmodule' U).finrank_eq.symm.trans
    (LinearEquiv.ofEq _ _ hU).finrank_eq

/-- A maximal-rank kernel dimension characterizes maximal rank. -/
theorem maximalRank_of_kernel_finrank
    {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W)
    (h : finrank K f.ker = finrank K V - finrank K W) : HasMaximalRank f := by
  apply (maximalRank_iff_rank_eq_min f).mpr
  have hr := f.finrank_range_add_finrank_ker
  rw [h] at hr
  have hbound := Submodule.finrank_le f.range
  omega

/-- Every fixed partial subspace admits a witness with the expected dimension
once ideal generation is known at the two adjacent point counts. -/
theorem exists_fixedPartialTrace_witness [CharZero K]
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1)) :
    ∃ b : PointCoordinates K n p,
      HasMaximalRank (fixedPartialTraceEvaluation y L b d) := by
  obtain ⟨a, ha, hg⟩ := exists_fixedPoint_euler_restriction_maximalRank y hp h₀ h₁
  let A := eulerTraceEvaluation a d
  let g := (eulerTraceAt y d).comp A.ker.subtype
  obtain ⟨e, he⟩ := exists_linearEquiv_comp_quotient_maximalRank L g hg
  let E := coordinateDualEquiv e
  let b := affineCoordinates y y E.symm a
  have hback : affineCoordinates y y E b = a := by
    funext ij
    have hv : (fun j => b (ij.1, j)) - y =
        E.symm ((fun j => a (ij.1, j)) - y) := by
      change (E.symm ((fun j => a (ij.1, j)) - y) + y) - y =
        E.symm ((fun j => a (ij.1, j)) - y)
      exact add_sub_cancel_right _ _
    change (E ((fun j => b (ij.1, j)) - y) + y) ij.2 = a ij
    rw [hv, LinearEquiv.apply_symm_apply]
    simp
  let B := L.mkQ.comp (e.toLinearMap.comp (eulerTraceAt y d))
  have hrest : HasMaximalRank (B.comp A.ker.subtype) := he
  have hdim : finrank K (A.prod B).ker =
      finrank K (EulerRelations K n d) - n * p - (n - finrank K L) := by
    rw [finrank_prod_kernel_of_restriction_maximalRank A B hrest, ha]
    have hq : finrank K ((Fin n → K) ⧸ L) = n - finrank K L := by
      simpa using (L.finrank_quotient (R := K))
    rw [hq]
  have hker : ((eulerTraceEvaluation (affineCoordinates y y E b) d).prod
      (L.mkQ.comp ((coordinateDualEquiv E).toLinearMap.comp (eulerTraceAt y d)))).ker =
      (A.prod B).ker := by
    rw [hback, show coordinateDualEquiv E = e from coordinateDualEquiv_involutive e]
  have hk : finrank K (fixedPartialTraceEvaluation y L b d).ker =
      finrank K (EulerRelations K n d) - n * p - (n - finrank K L) :=
    (fixedPartialTrace_stabilizer_finrank y L E b).trans
      ((LinearEquiv.ofEq _ _ hker).finrank_eq.trans hdim)
  refine ⟨b, maximalRank_of_kernel_finrank (fixedPartialTraceEvaluation y L b d) ?_⟩
  have hq : finrank K ((Fin n → K) ⧸ L) =
      finrank K (Fin n → K) - finrank K L := L.finrank_quotient
  have ht : finrank K ((Fin p → Fin n → K) × ((Fin n → K) ⧸ L)) =
      n * p + (n - finrank K L) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_one] at hq ⊢
    rw [hq, Nat.mul_comm]
    norm_num
  simpa only [ht, Nat.sub_sub] using hk

/-- Lemma 3.6 for any prescribed affine point and partial trace subspace. The
nonempty principal open is chosen after both have been fixed. -/
theorem generic_fixedPartialTrace [CharZero K]
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (hp : p + 1 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p) (h₁ : IdealGenerationAt K n d (p + 1)) :
    ∃ D : MvPolynomial (Fin p × Fin n) K,
      (∃ a : PointCoordinates K n p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        finrank K (fixedPartialTraceEvaluation y L a d).ker =
          fixedPartialTraceDimension L d p := by
  obtain ⟨a, ha⟩ := exists_fixedPartialTrace_witness y L hp h₀ h₁
  exact generic_fixedPartialTrace_of_witness y L a ha

/-- The fixed partial condition has its expected dimension before and after
one further general point is added, on a single nonempty principal open. -/
theorem generic_fixedPartialTrace_successive [CharZero K]
    (y : Fin n → K) (L : Submodule K (Fin n → K))
    (hp : p + 2 ≤ N (n + 1) d)
    (h₀ : IdealGenerationAt K n d p)
    (h₁ : IdealGenerationAt K n d (p + 1))
    (h₂ : IdealGenerationAt K n d (p + 2)) :
    ∃ D : MvPolynomial (Fin (p + 1) × Fin n) K,
      (∃ a : PointCoordinates K n (p + 1), eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
        finrank K (fixedPartialTraceEvaluation y L (restrictPoints a Fin.castSucc) d).ker =
          fixedPartialTraceDimension L d p ∧
        finrank K (fixedPartialTraceEvaluation y L a d).ker =
          fixedPartialTraceDimension L d (p + 1) := by
  obtain ⟨D₀, hD₀, hgood₀⟩ := generic_fixedPartialTrace y L (by omega) h₀ h₁
  obtain ⟨D₁, hD₁, hgood₁⟩ := generic_fixedPartialTrace y L
    (show p + 1 + 1 ≤ N (n + 1) d by omega) h₁ (by simpa [Nat.add_assoc] using h₂)
  let D₀' := rename (fun ij : Fin p × Fin n => (ij.1.castSucc, ij.2)) D₀
  have hD₀' : ∃ a : PointCoordinates K n (p + 1), eval a D₀' ≠ 0 := by
    obtain ⟨a, ha⟩ := hD₀
    refine ⟨snocPoints a y, ?_⟩
    simpa only [D₀', eval_rename_castSucc, restrict_snocPoints_castSucc] using ha
  obtain ⟨a, ha₀, ha₁⟩ := principal_opens_meet D₀' D₁ hD₀' hD₁
  refine ⟨D₀' * D₁, ⟨a, by simpa using mul_ne_zero ha₀ ha₁⟩, ?_⟩
  intro b hb
  have hb' : eval b D₀' ≠ 0 ∧ eval b D₁ ≠ 0 := by simpa using hb
  exact ⟨hgood₀ _ (by simpa only [D₀', eval_rename_castSucc] using hb'.1),
    hgood₁ b hb'.2⟩

end IdealGeneration
