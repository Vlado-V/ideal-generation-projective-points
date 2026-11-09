module

public import IdealGeneration.CubicPairC3Future
public import IdealGeneration.CubicPairC3NewEmbedding

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! A primitive open preserving C.3 nonsingularity for the newly created pair. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicParameterCompatibility MvPolynomial

private theorem pairC3Trace_last_ge (k : ℕ) (i : Fin 5) (hi : 3 ≤ i.val) :
    10 + 2 * k ≤ (pairC3Trace (Fin.last k) i).val := by
  fin_cases i <;> simp [pairC3Trace, pairA, pairB] at *

private theorem c3OldAmbientIndex_injective {k : ℕ} (j : Fin k) :
    Function.Injective (c3OldAmbientIndex j) := by
  intro a b h
  have hl : c3OldLocalIndex a = c3OldLocalIndex b :=
    c3PrimitiveImage_injective (pairC3TraceEmbedding j) (pairC3Trace_strictMono j) h
  apply Subtype.ext
  simpa only [oldPrimitiveIndex_c3OldLocalIndex] using congrArg (oldPrimitiveIndex 5) hl

private theorem c3OldAmbientIndex_last_not_mem (k : ℕ) (i : C3OldIndex) :
    c3OldAmbientIndex (Fin.last k) i ∉ Set.range (oldPrimitiveIndex (10 + 2 * k)) := by
  apply not_mem_oldPrimitiveIndex_of_lastVertex_ge
  have h : 3 ≤ primitiveLastVertex (c3OldLocalIndex i) := by
    rcases i with ⟨a, ha⟩
    cases a <;> exact ha.1
  unfold c3OldAmbientIndex
  generalize c3OldLocalIndex i = a at h ⊢
  cases a <;> exact pairC3Trace_last_ge k _ h

/-- The newest pair's retained C.3 parameters are among the current new primitives. -/
def newestPairPrimitiveEmbedding (k : ℕ) : C3OldIndex ↪ NewPrimitiveIndex (10 + 2 * k) where
  toFun i := ⟨c3OldAmbientIndex (Fin.last k) i, c3OldAmbientIndex_last_not_mem k i⟩
  inj' _ _ h := c3OldAmbientIndex_injective (Fin.last k) (congrArg Subtype.val h)

/-- The checked C.3 witness gives a nonzero open condition in the current new primitives. -/
theorem exists_newestPairGuard (k : ℕ) :
    ∃ G : MvPolynomial (NewPrimitiveIndex (10 + 2 * k)) ℚ, G ≠ 0 ∧
      ∀ Q : Parameters ℚ ((10 + 2 * k) + 2),
        eval (fun i => primitiveValue Q i.val) G ≠ 0 → PairGood Q (Fin.last k) := by
  have hCert : intSumPolynomial ℚ c3FutureCertificate ≠ 0 := by
    intro h
    exact c3FutureFiber_oldWitness_ne_zero (by rw [c3FutureFiber, h, specialize, map_zero])
  obtain ⟨D, hD, hgood⟩ := exists_fiber_coefficient (intSumPolynomial ℚ c3FutureCertificate) hCert
  let e := newestPairPrimitiveEmbedding k
  refine ⟨rename e D, ?_, ?_⟩
  · intro h
    exact hD ((rename_eq_zero_iff_of_injective D e.injective).mp h)
  · intro Q h
    let x : C3OldIndex → ℚ := c3OldValue (k := k + 1) Q (Fin.last k)
    have hValue : ((fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val) ∘ e) = x := by
      funext i
      rfl
    have hx : eval x D ≠ 0 := by
      rw [eval_rename, hValue] at h
      exact h
    have hf := hgood x hx
    change specialize x (intSumPolynomial ℚ c3FutureCertificate) ≠ 0
    exact hf

end IdealGeneration.CubicSupported.B5
