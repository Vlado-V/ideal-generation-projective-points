module

public import IdealGeneration.CubicB6Pool
public import IdealGeneration.CubicB5Step
public import IdealGeneration.CubicB22Formulas
public import IdealGeneration.CubicPrimitiveExtension
public import IdealGeneration.CubicSingleSlopeGuard

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The simultaneous parameter choice and actual even-level recurrence in B.6. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B6

open B5 B22 B7Root RationalChart CubicParameterCompatibility CubicRationalFormula MvPolynomial

/-- The C.3 coefficient condition and its two uses in the recurrence. -/
structure PairCertificates where
  good (k : ℕ) (P : Parameters ℚ (10 + 2 * k)) (j : Fin k) : Prop
  fixedSamples (k : ℕ) (P : Parameters ℚ (10 + 2 * k)) (j : Fin k) (hg : good k P j) :
    ∃ (D : PairBlockData ℚ k j) (F : MvPolynomial (NewPrimitiveIndex (10 + 2 * k)) ℚ),
      F ≠ 0 ∧ D.coreColumn = canonicalPairCoreColumn j ∧
      ∀ Q : Parameters ℚ ((10 + 2 * k) + 2), Compatible P Q → Q.single = B5.single →
        eval (newPrimitiveValue Q) F ≠ 0 → (pairCoreMatrix (actualB7Data Q) D).det ≠ 0
  retain (k : ℕ) (P : Parameters ℚ (10 + 2 * k)) (Q : Parameters ℚ ((10 + 2 * k) + 2))
    (h : Compatible P Q) (j : Fin k) : good k P j → good (k + 1) Q j.castSucc
  newestGuard (k : ℕ) :
    ∃ F : MvPolynomial (NewPrimitiveIndex (10 + 2 * k)) ℚ, F ≠ 0 ∧
      ∀ Q : Parameters ℚ ((10 + 2 * k) + 2), eval (newPrimitiveValue Q) F ≠ 0 →
        good (k + 1) Q (Fin.last k)

/-- All old data retained by a step of the actual supported cubic construction. -/
structure GoodLevel (C : PairCertificates) (k : ℕ) where
  cones : Parameters ℚ (10 + 2 * k)
  free : Fin (freeCount k) → Fin (10 + 2 * k) → ℚ
  graph : cones.single = B5.single
  middle : Function.Injective ((cones.toConeConfiguration free).middleMultiplication 3)
  poolAgreement : AgreesInitialPool cones
  distinctSlopes : Set.InjOn (fun e => cones.edgeSlope e 0) {e | cones.single e = true}
  pairGood : ∀ j, C.good k cones j

set_option maxRecDepth 100000 in
private theorem initial_distinct_slopes_nat :
    ∀ e e' : Edge 10, B5.single e = true → B5.single e' = true →
      CubicInitial.slope (CubicInitial.edgeConeIndex e 0) =
        CubicInitial.slope (CubicInitial.edgeConeIndex e' 0) → e = e' := by
  decide +kernel

/-- The two initial single directions have distinct slopes. -/
theorem initial_distinct_slopes :
    Set.InjOn (fun e : Edge 10 => (CubicInitial.initialGraph ℚ).edgeSlope e 0)
      {e | (CubicInitial.initialGraph ℚ).single e = true} := by
  intro e he e' he' hs
  exact initial_distinct_slopes_nat e e' he he' (Nat.cast_injective hs)

/-- The exact initial middle witness starts the B.6 recurrence. -/
def initialGoodLevel (C : PairCertificates)
    (hinit : Function.Injective (((CubicInitial.initialGraph ℚ).toConeConfiguration
      (CubicInitial.initialFree ℚ)).middleMultiplication 3)) : GoodLevel C 0 where
  cones := CubicInitial.initialGraph ℚ
  free := CubicInitial.initialFree ℚ
  graph := rfl
  middle := hinit
  poolAgreement := initialGraph_agreesInitialPool
  distinctSlopes := initial_distinct_slopes
  pairGood j := j.elim0

/-- Choose all new primitive parameters together and perform the actual pair step. -/
theorem goodLevel_succ (C : PairCertificates) (k : ℕ) (old : GoodLevel C k)
    (hroot : (poolMatrix (actualB7Data (parametersCharZero ℚ)) (pool ℚ)).det ≠ 0) :
    Nonempty (GoodLevel C (k + 1)) := by
  classical
  let P := old.cones
  obtain ⟨L, pairing, hPL, hL, h22L⟩ :=
    exists_b5_splitFixedHigherCertificate_ne_zero k P old.graph
  let prim := primitiveExtensionGuard P B5.single
  let distinct := specialize (primitiveValue P) (singleSlopeGuardFiber ℚ B5.single)
  let poolPoly := laterPoolFiber P
  let higher := specialize (primitiveValue P) (intSumPolynomial ℚ (splitFixedHigherCertificate L pairing))
  have hprim : prim ≠ 0 := primitiveExtensionGuard_ne_zero_of_compatible P hPL _ hL
  have hdistinct : distinct ≠ 0 := by
    change specialize (primitiveValue P) (singleSlopeGuardFiber ℚ B5.single) ≠ 0
    rw [← hL]
    exact specialize_singleSlopeGuardFiber_ne_zero_of_compatible hPL old.distinctSlopes
  have hpool : poolPoly ≠ 0 := laterPoolFiber_ne_zero old.poolAgreement hPL hL hroot
  have hhigher : higher ≠ 0 :=
    specialize_intSumPolynomial_ne_zero_of_eval ℚ (primitiveValue P) (newPrimitiveValue L)
      (splitFixedHigherCertificate L pairing) h22L
  choose D p hp hD hpairEval using fun j => C.fixedSamples k P j (old.pairGood j)
  obtain ⟨future, hfuture, hfutureEval⟩ := C.newestGuard k
  obtain ⟨y, hy, hyPair⟩ := exists_shared_extension p hp
    (prim * distinct * poolPoly * higher * future)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hprim hdistinct) hpool) hhigher) hfuture)
  have hys : (((eval y prim ≠ 0 ∧ eval y distinct ≠ 0) ∧ eval y poolPoly ≠ 0) ∧
      eval y higher ≠ 0) ∧ eval y future ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hy
  obtain ⟨⟨⟨⟨hyPrim, hyDistinct⟩, hyPool⟩, hyHigher⟩, hyFuture⟩ := hys
  let Q := extensionOfPrimitiveGuard P B5.single y hyPrim
  have hQ : Q.single = B5.single := rfl
  have hPQ : Compatible P Q := b5_extensionOfPrimitiveGuard_compatible k P old.graph y hyPrim
  have hnew : newPrimitiveValue Q = y := extensionOfPrimitiveGuard_new P B5.single y hyPrim
  have hQSlopes : Set.InjOn (fun e => Q.edgeSlope e 0) {e | B5.single e = true} := by
    have hs := (eval_specialize_singleSlopeGuardFiber_ne_zero_iff (primitiveValue P) y B5.single).mp
      hyDistinct
    have heq : (fun e : Edge ((10 + 2 * k) + 2) =>
        Sum.elim y (primitiveValue P) ((primitiveOldNewEquiv (10 + 2 * k)).symm (.edgeSlope e 0))) =
        fun e => Q.edgeSlope e 0 := by
      funext e
      change splitPrimitiveAssignment P y (.edgeSlope e 0) = primitiveValue Q (.edgeSlope e 0)
      rw [primitiveValue_extensionOfPrimitiveGuard]
    rwa [heq] at hs
  have hQPool : (poolMatrix (actualB7Data Q) (laterPool ℚ k)).det ≠ 0 := by
    apply (eval_laterPoolFiber_ne_zero_iff hPQ hQ).mp
    rw [show (fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val) = y from hnew]
    exact hyPool
  have hQPair (j : Fin k) : (pairCoreMatrix (actualB7Data Q) (D j)).det ≠ 0 := by
    apply hpairEval j Q hPQ hQ
    rw [hnew]
    exact hyPair j
  let pairing' := pairing.trans (incidenceEquivOfGraph L Q (hL.trans hQ.symm))
  have hQHigher : (fixedHigherMatrix Q pairing' c4ProbeValues).det ≠ 0 := by
    apply (eval_specializedFixedHigherCertificate_ne_zero_iff Q pairing' hPQ).mp
    rw [show (fun i : NewPrimitiveIndex (10 + 2 * k) => primitiveValue Q i.val) = y from hnew,
      ← splitFixedHigherCertificate_eq_of_graph L pairing Q (hL.trans hQ.symm)]
    exact hyHigher
  obtain ⟨free, hmiddle⟩ := exists_b5_step_of_witnesses P Q old.graph hQ hPQ old.free
    (by norm_num) (by norm_num) poolSampleIndex (laterPoolPoint ℚ k) (laterPoolWeight ℚ)
    (laterPool ℚ k) D pairing' c4ProbeValues old.middle (by simp [Index])
    (laterPool_probe ℚ k) hD hQPool hQPair hQSlopes hQHigher
  refine ⟨⟨Q, free, hQ, hmiddle, old.poolAgreement.extend hPQ, ?_, ?_⟩⟩
  · rwa [hQ]
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · apply hfutureEval Q
      rw [hnew]
      exact hyFuture
    · exact C.retain k P Q hPQ i (old.pairGood i)

/-- Starting with the two finite C.2 witnesses, the checked C.3 conditions give every even level. -/
theorem goodLevel_all (C : PairCertificates)
    (hinit : Function.Injective (((CubicInitial.initialGraph ℚ).toConeConfiguration
      (CubicInitial.initialFree ℚ)).middleMultiplication 3))
    (hroot : (poolMatrix (actualB7Data (parametersCharZero ℚ)) (pool ℚ)).det ≠ 0)
    (k : ℕ) : Nonempty (GoodLevel C k) := by
  induction k with
  | zero => exact ⟨initialGoodLevel C hinit⟩
  | succ k ih =>
      obtain ⟨old⟩ := ih
      exact goodLevel_succ C k old hroot

end IdealGeneration.CubicSupported.B6
