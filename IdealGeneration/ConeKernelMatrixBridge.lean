module

public import IdealGeneration.ConeMiddleMatrix
public import IdealGeneration.TripleNormalKernelStages

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A checked matrix of kernel coefficients gives an actual cone middle-map witness. -/
noncomputable section
namespace IdealGeneration.ConeMonomialChart
open MvPolynomial Matrix

variable {K : Type*} [Field K] {c m p q d : ℕ}
variable {ν τ r t o : Type*} [Fintype ν] [Fintype τ] [Fintype r] [Fintype t]

/-- Injectivity of a selected coefficient matrix implies native middle-map
injectivity when its coefficient columns span the two evaluation kernels. -/
theorem middle_injective_of_kernel_chart_matrix (C : ConeConfiguration K c m p q)
    (en : ν → Fin (c + m) →₀ ℕ) (et : τ → Fin m →₀ ℕ)
    (out : o → Fin (c + m) →₀ ℕ) (Kn : Matrix ν r K) (Kt : Matrix τ t K)
    (hnd : ∀ i, (en i).degree = d) (htd : ∀ i, (et i).degree = d)
    (hnn : ∀ i, ∃ j : Fin c, en i (j.castAdd m) ≠ 0)
    (hns : Function.Surjective (normalSynth (K := K) en hnd hnn))
    (hts : Function.Surjective (formSynth (K := K) et htd))
    (hnk : ∀ u, (evaluationMatrix C.point en).mulVec u = 0 → ∃ v, Kn.mulVec v = u)
    (htk : ∀ u, (evaluationMatrix C.trace et).mulVec u = 0 → ∃ v, Kt.mulVec v = u)
    (hm : Function.Injective (middleMatrix en et out Kn Kt).mulVec) :
    Function.Injective (C.middleMultiplication d) := by
  have hzero : ∀ f, C.middleMultiplication d f = 0 → f = 0 := by
    intro f hf
    have hn : ∀ j : Fin (c + m), ∃ v, synth en (Kn.mulVec v) = (f.1 j).val.val := by
      intro j
      obtain ⟨u, hu⟩ := hns ⟨(f.1 j).val, (f.1 j).property.2⟩
      have hsyn : synth en u = (f.1 j).val.val := congrArg (fun g => g.val.val) hu
      have hev : (evaluationMatrix C.point en).mulVec u = 0 := by
        funext i
        change (∑ a, (∏ k, C.point i k ^ en a k) * u a) = 0
        rw [← evaluationMatrix_mulVec, hsyn]
        exact (C.mem_conePiece _).mp (f.1 j).property.1 i
      obtain ⟨v, hv⟩ := hnk u hev
      exact ⟨v, by rw [hv, hsyn]⟩
    have ht : ∀ j : Fin c, ∃ v, synth et (Kt.mulVec v) = (f.2 j).val.val := by
      intro j
      obtain ⟨u, hu⟩ := hts (f.2 j).val
      have hsyn : synth et u = (f.2 j).val.val := congrArg Subtype.val hu
      have hev : (evaluationMatrix C.trace et).mulVec u = 0 := by
        funext i
        change (∑ a, (∏ k, C.trace i k ^ et a k) * u a) = 0
        rw [← evaluationMatrix_mulVec, hsyn]
        exact (C.mem_tracePiece _).mp (f.2 j).property i
      obtain ⟨v, hv⟩ := htk u hev
      exact ⟨v, by rw [hv, hsyn]⟩
    choose xn hxn using hn
    choose xt hxt using ht
    let x : MiddleColumn c m r t → K := Sum.elim (fun j => xn j.1 j.2) (fun j => xt j.1 j.2)
    have hprod : (middleMatrix en et out Kn Kt).mulVec x = 0 := by
      funext i
      rw [middleMatrix_mulVec]
      simp only [x, Sum.elim_inl, Sum.elim_inr, hxn, hxt]
      have hp := congrArg (fun z => z.val.val) hf
      rw [C.middleMultiplication_val] at hp
      simp only [Submodule.coe_add, formMultiplication_val] at hp
      have htail : (∑ j : Fin (c + m), X j * (C.normalTraceCoefficients d f.2 j).val) =
          ∑ j : Fin c, X (j.castAdd m) * coneExtend K c m (f.2 j).val.val := by
        rw [Fin.sum_univ_add]
        simp [ConeConfiguration.normalTraceCoefficients, coneExtendForm]
      rw [htail] at hp
      rw [hp]
      rfl
    have hx : x = 0 := hm (hprod.trans (Matrix.mulVec_zero _).symm)
    apply Prod.ext
    · funext j
      apply Subtype.ext
      apply Subtype.ext
      have hj : xn j = 0 := funext (fun k => congrFun hx (.inl (j, k)))
      simpa [hj] using (hxn j).symm
    · funext j
      apply Subtype.ext
      apply Subtype.ext
      have hj : xt j = 0 := funext (fun k => congrFun hx (.inr (j, k)))
      simpa [hj] using (hxt j).symm
  apply (linearMap_injective_iff_kernel_subsingleton (C.middleMultiplication d)).mpr
  constructor
  intro f g
  apply Subtype.ext
  exact (hzero f.val f.property).trans (hzero g.val g.property).symm

end IdealGeneration.ConeMonomialChart
