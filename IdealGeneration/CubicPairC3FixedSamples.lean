module

public import IdealGeneration.CubicPairC3FutureActual
public import IdealGeneration.CubicPairC3NewEmbedding
public import IdealGeneration.CubicPairLocalSamples

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Fixing the C.3 samples while retaining a nonzero polynomial in the new cone labels. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicParameterCompatibility MvPolynomial

variable {k : ℕ}

/-- Specialize the thirteen local samples, leaving only the new local cone labels. -/
def c3FixedSampleFiber (P : Parameters ℚ (10 + 2 * k)) (j : Fin k)
    (sample : Fin 13 × Fin 7 → ℚ) : MvPolynomial C3NewPrimitiveIndex ℚ :=
  specialize sample (sumAlgEquiv ℚ C3NewPrimitiveIndex (Fin 13 × Fin 7)
    (c3FutureFiber (c3OldValue P j)))

private theorem exists_c3FixedSampleFiber_ne_zero (P : Parameters ℚ (10 + 2 * k))
    (j : Fin k) (hg : PairGood P j) : ∃ sample, c3FixedSampleFiber P j sample ≠ 0 := by
  have he : ∃ z : C3NewIndex → ℚ, eval z (c3FutureFiber (c3OldValue P j)) ≠ 0 := by
    by_contra! hz
    exact hg (MvPolynomial.funext hz)
  obtain ⟨z, hz⟩ := he
  let sample : Fin 13 × Fin 7 → ℚ := z ∘ Sum.inr
  let prim : C3NewPrimitiveIndex → ℚ := z ∘ Sum.inl
  have hsplit : Sum.elim prim sample = z := by
    funext i
    cases i <;> rfl
  refine ⟨sample, ?_⟩
  intro hs
  have hev := eval_specialize_sumPolynomial sample prim (c3FutureFiber (c3OldValue P j))
  change eval prim (c3FixedSampleFiber P j sample) = _ at hev
  rw [hs, map_zero, hsplit] at hev
  exact hz hev.symm

/-- One sample choice makes the actual pair-core determinant nonzero on a
principal open of the new ambient cone. -/
theorem PairGood.fixedSamplesFiber (P : Parameters ℚ (10 + 2 * k)) (j : Fin k)
    (hg : PairGood P j) :
    ∃ (D : PairBlockData ℚ k j) (p : MvPolynomial (NewPrimitiveIndex (10 + 2 * k)) ℚ),
      p ≠ 0 ∧ D.coreColumn = canonicalPairCoreColumn j ∧
      ∀ Q : Parameters ℚ ((10 + 2 * k) + 2), Compatible P Q → Q.single = single →
        eval (fun i => primitiveValue Q i.val) p ≠ 0 →
          (pairCoreMatrix (actualB7Data Q) D).det ≠ 0 := by
  obtain ⟨sample, hs⟩ := exists_c3FixedSampleFiber_ne_zero P j hg
  let D := pairBlockDataOfLocalSamples j sample (fun _ => (1 : ℚ)) (fun _ => one_ne_zero)
  let p := rename (c3NewAmbientEmbedding j) (c3FixedSampleFiber P j sample)
  have hp : p ≠ 0 := by
    intro hp
    apply hs
    apply rename_injective _ (c3NewAmbientEmbedding j).injective
    simpa only [map_zero] using hp
  refine ⟨D, p, hp, rfl, ?_⟩
  intro Q hPQ hQ he
  have hsample : (fun i => pairC3Point j (D.point i) (D.weight i)) =
      fun i t => sample (i, t) := by
    funext i t
    exact pairC3Point_pairBlockDataOfLocalSamples j sample _ _ i t
  apply (eval_c3FutureFiber_ne_zero_iff P Q hPQ hQ j D rfl).mp
  rw [hsample]
  have hvalues :
      Sum.elim ((fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val) ∘
        c3NewAmbientEmbedding j) sample = c3NewValue Q j (fun i t => sample (i, t)) := by
    funext i
    rcases i with i | ⟨r, t⟩ <;> rfl
  have hev : eval (fun i => primitiveValue Q i.val) p =
      eval (c3NewValue Q j (fun i t => sample (i, t))) (c3FutureFiber (c3OldValue P j)) := by
    change eval (fun i => primitiveValue Q i.val)
      (rename (c3NewAmbientEmbedding j) (c3FixedSampleFiber P j sample)) = _
    rw [eval_rename, c3FixedSampleFiber, eval_specialize_sumPolynomial, hvalues]
  exact hev ▸ he

end IdealGeneration.CubicSupported.B5
