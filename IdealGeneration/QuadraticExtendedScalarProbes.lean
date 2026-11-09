module

public import IdealGeneration.QuadraticTracePostulation
public import IdealGeneration.TwoGroupLinearCore
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Additional trace probes preserve independent scalar evaluation up to the dimension of the flag ideal. -/

noncomputable section
namespace IdealGeneration.QuadraticExtendedScalarProbes
open MvPolynomial Module QuadraticFlag QuadraticFlagProbeScalar QuadraticTracePostulation
open scoped Classical

variable {K T L A : Type*} [Field K]

/-- Scalar evaluation restricted to a subspace of quadrics. -/
abbrev scalarEvaluation (V : Submodule K (Quadrics K T)) (x : A → T → K) : V →ₗ[K] (A → K) :=
  (quadraticEvaluation x).comp V.subtype

@[simp] theorem scalarEvaluation_apply (V : Submodule K (Quadrics K T)) (x : A → T → K)
    (f : V) (a : A) : scalarEvaluation V x f a = eval (x a) f.val.val :=
  quadraticEvaluation_apply x f.val a

set_option maxHeartbeats 800000 in
/-- An independent finite set of evaluations on quadrics can be extended to any admissible size. -/
theorem exists_append_scalarEvaluation_surjective [Infinite K] [Fintype L]
    (V : Submodule K (Quadrics K T)) [Module.Finite K V]
    (base : L → T → K) (hbase : Function.Surjective (scalarEvaluation V base))
    (s : ℕ) (hsize : Fintype.card L + s ≤ finrank K V) :
    ∃ extra : Fin s → T → K, Function.Surjective (scalarEvaluation V (Sum.elim base extra)) := by
  classical
  induction s with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro y
    obtain ⟨f, hf⟩ := hbase (fun i => y (.inl i))
    refine ⟨f, ?_⟩
    funext a
    cases a with
    | inl i => exact congrFun hf i
    | inr i => exact Fin.elim0 i
  | succ s ih =>
    obtain ⟨extra, hext⟩ := ih (by omega)
    let old := scalarEvaluation V (Sum.elim base extra)
    have hdim := TwoGroup.rank_nullity_monoid old
    rw [LinearMap.range_eq_top.mpr hext, finrank_top, Module.finrank_pi, Fintype.card_sum,
      Fintype.card_fin] at hdim
    have hker : old.ker ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hdim
      omega
    obtain ⟨f, hf, hfne⟩ := old.ker.ne_bot_iff.mp hker
    have hpoly : f.val.val ≠ 0 := fun h => hfne (Subtype.ext (Subtype.ext h))
    obtain ⟨x, hx⟩ : ∃ x : T → K, eval x f.val.val ≠ 0 := by
      by_contra! hz
      exact hpoly (MvPolynomial.funext (fun x => (hz x).trans (map_zero (eval x)).symm))
    refine ⟨Fin.snoc extra x, ?_⟩
    intro y
    let prev : L ⊕ Fin s → K := Sum.elim (fun i => y (.inl i)) (fun i => y (.inr i.castSucc))
    obtain ⟨g, hg⟩ := hext prev
    let c := (y (.inr (Fin.last s)) - eval x g.val.val) / eval x f.val.val
    let F := g + c • f
    have hprev : old F = prev := by
      rw [show old F = old g + c • old f from by simp [F], hg, LinearMap.mem_ker.mp hf]
      simp
    refine ⟨F, ?_⟩
    funext a
    rw [scalarEvaluation_apply]
    cases a with
    | inl i => exact congrFun hprev (.inl i)
    | inr i =>
      change eval (Fin.snoc (α := fun _ => T → K) extra x i) F.val.val = y (.inr i)
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact congrFun hprev (.inr j)
      · rw [Fin.snoc_last]
        let e := scalarEvaluation V (fun _ : Unit => x)
        change e F () = y (.inr (Fin.last s))
        have he : e F = e g + c • e f := by
          change e (g + c • f) = _
          rw [map_add, map_smul]
        rw [he]
        change eval x g.val.val + c * eval x f.val.val = _
        rw [show c * eval x f.val.val = y (.inr (Fin.last s)) - eval x g.val.val from
          div_mul_cancel₀ _ hx]
        abel

variable {P J : Type*} [Fintype P] [Fintype J]

/-- Scalar evaluation on the full original probe labels. -/
theorem probePoint_scalarEvaluation_surjective (p₀ : P) (layers : Bool → J)
    (hne : layers false ≠ layers true) :
    Function.Surjective (scalarEvaluation (quadraticFlagVanishing (K := K)) (probePoint p₀ layers)) := by
  intro y
  obtain ⟨f, hf⟩ := flagProbeScalarEvaluation_surjective (K := K) p₀ layers hne
    (fun i => y (.inl i), fun p b => y (.inr (p, b)))
  refine ⟨f, ?_⟩
  funext a
  cases a with
  | inl i => exact congrFun (congrArg Prod.fst hf) i
  | inr q => exact congrFun (congrFun (congrArg Prod.snd hf) q.1) q.2

/-- Keep all probes of (A.4) and append an additional finite list. -/
def extendedProbePoints (p₀ : P) (layers : Bool → J) {s : ℕ}
    (extra : Fin s → (P × Bool) ⊕ J → K) : ProbeIndex p₀ ⊕ Fin s → (P × Bool) ⊕ J → K :=
  Sum.elim (probePoint p₀ layers) extra

/-- The full list in (A.4) extends to any length allowed by the scalar flag ideal. -/
theorem exists_extendedProbePoints_scalar_surjective [Infinite K] (p₀ : P) (layers : Bool → J)
    (hne : layers false ≠ layers true) (s : ℕ)
    (hsize : Fintype.card (ProbeIndex p₀) + s ≤
      finrank K (quadraticFlagVanishing (K := K) (P := P) (J := J))) :
    ∃ extra : Fin s → (P × Bool) ⊕ J → K,
      Function.Surjective (scalarEvaluation quadraticFlagVanishing (extendedProbePoints p₀ layers extra)) :=
  exists_append_scalarEvaluation_surjective quadraticFlagVanishing (probePoint p₀ layers)
    (probePoint_scalarEvaluation_surjective (K := K) p₀ layers hne) s hsize

end IdealGeneration.QuadraticExtendedScalarProbes
