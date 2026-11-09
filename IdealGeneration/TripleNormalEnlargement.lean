module

public import IdealGeneration.TripleNormalBaseRank
public import IdealGeneration.TripleNormalFlagStep
public import IdealGeneration.TripleNormalQuadraticTransfer
public import IdealGeneration.PointAvoidance

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Choose the free points and iterate the three-normal quadratic enlargement. -/
noncomputable section
namespace IdealGeneration.TripleNormal

open MvPolynomial NormalizedEdgeColumns

variable {K : Type*} [Field K] [CharZero K] {ω : K}

omit [CharZero K] in
private theorem chordFactor_ne_zero_imp_ne {a b : K} (h : chordFactor a b ≠ 0) : a ≠ b := by
  intro hab
  subst b
  exact h (by simp [chordFactor])

/-- The enlargement chooses the three conic parameters and a common point
of the scalar and vector evaluation opens. -/
theorem FlagWitness.enlarge {h : ℕ} (F : FlagWitness K ω h) (hh : 8 ≤ h) :
    Nonempty (FlagWitness K ω (h + 3)) := by
  obtain ⟨N, rfl⟩ : ∃ N, h = N + 3 := ⟨h - 3, by omega⟩
  have hN : 5 ≤ N := by omega
  obtain ⟨v, hv, hov, hvv, hchords⟩ :=
    exists_ordered_chord_parameters hN (nonrootEmbedding N) F.t F.base_nonzero F.base_injective
  let t' := Fin.append F.t v
  have ht : ∀ i, t' i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun b => ?_) i
    · simpa [t'] using F.base_nonzero j
    · simpa [t'] using hv b
  have hchord : ∀ i j, i ≠ j → chordFactor (t' i) (t' j) ≠ 0 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun b => ?_) i
    · intro j
      refine Fin.addCases (fun j hij => ?_) (fun b _ => ?_) j
      · simpa [t'] using F.chord_nonzero i j (fun h => hij (congrArg (Fin.castAdd 3) h))
      · simpa [t'] using hov i b
    · intro j
      refine Fin.addCases (fun j _ => ?_) (fun c hbc => ?_) j
      · simpa [t', chordFactor_comm (v b) (F.t j)] using hov j b
      · simpa [t'] using hvv b c (fun h => hbc (congrArg (Fin.natAdd (N + 3)) h))
  have hparams : Function.Injective t' := by
    intro i j he
    by_contra hij
    exact chordFactor_ne_zero_imp_ne (hchord i j hij) he
  have hroots (i : Fin 3) : rootParameters F.t i ≠ 0 :=
    F.base_nonzero (i.natAdd N)
  have hrootinj : Function.Injective (rootParameters F.t) := by
    intro i j he
    have h := congrArg Fin.val (F.base_injective he)
    exact Fin.ext (by simp at h; omega)
  have hq (i b : Fin 3) : chordFactor (rootParameters F.t i) (v b) ≠ 0 :=
    hov (i.natAdd N) b
  obtain ⟨P, hP, hPgood⟩ := newBaseRank_principal_open ω F.t v F.primitive
    hroots hrootinj hq hN hparams hchords
  let η : Fin 4 → K := fun _ => 1
  have hη : ∀ j, η j ≠ 0 := fun _ => one_ne_zero
  obtain ⟨Q, hQ, hQgood⟩ := extensionTraceEvaluation_surjective_open
    F.cone.trace η hh hη F.trace_surjective
  obtain ⟨a, ha, hb⟩ := principal_opens_meet P Q hP hQ
  exact ⟨F.extend_of_newBaseRank (by omega) v a η ht hparams hchord hη
    (hPgood a ha) (hQgood a hb)⟩

/-- Starting at eight base coordinates gives every supported flag in A.4. -/
theorem exists_flagWitness_of_initial (F₈ : FlagWitness K ω 8) (s : ℕ) :
    Nonempty (FlagWitness K ω (8 + 3 * s)) := by
  induction s with
  | zero => exact ⟨F₈⟩
  | succ s ih =>
    obtain ⟨F⟩ := ih
    rw [show 8 + 3 * (s + 1) = (8 + 3 * s) + 3 by omega]
    exact F.enlarge (by omega)

/-- The three-normal quadratic step follows from the actual initial flag
and the independently generic trace assertion. -/
theorem quadratic_three_normal_step_of_initial (F₈ : FlagWitness K ω 8)
    (h : ℕ) (hh : 8 ≤ h) (hmod : h % 3 = 2)
    (hinduction : IdealGenerationAt K (h + 3) 2 (flagTraceCount h)) :
    IdealGenerationAt K (h + 6) 2 ((h + 7) * (h + 8) / 3) := by
  obtain ⟨s, hs⟩ : ∃ s, h = 8 + 3 * s := ⟨(h - 8) / 3, by omega⟩
  have hw : Nonempty (FlagWitness K ω h) := hs.symm ▸ exists_flagWitness_of_initial F₈ s
  obtain ⟨F⟩ := hw
  have hm := quadratic_tripleNormal_middle_bijective h hmod F.cone
    F.normal_surjective F.trace_surjective F.middle_injective
  exact quadratic_tripleNormal_endpoint h hmod F.cone F.normal_surjective
    F.trace_surjective hm hinduction

end IdealGeneration.TripleNormal
