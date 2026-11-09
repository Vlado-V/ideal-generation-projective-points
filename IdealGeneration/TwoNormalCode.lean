module

public import IdealGeneration.ScalarSelection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-!
# Coordinate classes in the slice quotient codes

If every full-size selection of evaluation rows determines the source, then
any allowable selection of coordinate classes in the quotient is independent.
The proof uses the complementary evaluation rows.
-/

noncomputable section
namespace IdealGeneration.TwoNormalIntegral
open Module
set_option maxHeartbeats 800000

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι]

/-- The coordinate class of one point in the evaluation quotient. -/
def coordinateClass (E : V →ₗ[K] (ι → K)) (i : ι) :
    (ι → K) ⧸ E.range := by
  classical
  exact E.range.mkQ (Pi.single i 1)

/-- Complementary full-size evaluation sets give independent coordinate
classes in the cokernel, in every length up to its dimension. -/
theorem coordinateClasses_independent
    (E : V →ₗ[K] (ι → K)) (hE : Function.Injective E)
    (hgood : ∀ s : Finset ι, s.card = finrank K V →
      Function.Injective (selectedScalarEvaluation
        (fun i => (LinearMap.proj i).comp E) s))
    (r : ℕ) (f : Fin r ↪ ι)
    (hr : r ≤ finrank K ((ι → K) ⧸ E.range)) :
    LinearIndependent K (coordinateClass E ∘ f) := by
  classical
  have hdim : finrank K V + finrank K ((ι → K) ⧸ E.range) = Fintype.card ι := by
    have h := E.range.finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hE] at h
    have hp : finrank K (ι → K) = Fintype.card ι := by simp
    omega
  let used : Finset ι := Finset.univ.image f
  have hused : used.card = r := by simp [used, Finset.card_image_of_injective _ f.injective]
  let available : Finset ι := Finset.univ \ used
  have havail : available.card = Fintype.card ι - r := by simp [available, Finset.card_sdiff, hused]
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq
    (show finrank K V ≤ available.card by rw [havail]; omega)
  have hselected := hgood s hscard
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let w : ι → K := ∑ i : Fin r, c i • Pi.single (f i) 1
  have hw : E.range.mkQ w = 0 := by
    simpa only [w, map_sum, map_smul, coordinateClass, Function.comp_apply] using hc
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero E.range).mp hw
  have hvzero : v = 0 := by
    apply hselected
    rw [map_zero]
    ext i
    change E v i.val = 0
    rw [hv]
    have hi : i.val ∉ used := (Finset.mem_sdiff.mp (hs i.property)).2
    have hif : ∀ j : Fin r, f j ≠ i.val := by
      intro j hj
      exact hi (by simp [used, ← hj])
    simp only [w, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro j _
    simp [Ne.symm (hif j)]
  have hwzero : w = 0 := by simpa [hvzero] using hv.symm
  have hj := congrFun hwzero (f j)
  simpa [w, Pi.single_apply, f.injective.eq_iff] using hj

end IdealGeneration.TwoNormalIntegral
