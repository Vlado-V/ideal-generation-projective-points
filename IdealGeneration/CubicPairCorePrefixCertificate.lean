module

public import IdealGeneration.CubicPairCoreCertificate
public import IdealGeneration.CubicB11Prefix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The pair-core polynomial remains nonzero after fixing an earlier cone prefix. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicParameterCompatibility

variable {k n : ℕ}

/-- The actual core certificate for an arbitrary primitive split. -/
def pairCoreCertificateAlong (e : PrimitiveIndex n ↪ PrimitiveIndex ((10 + 2 * k) + 2))
    (j : Fin k) : MvPolynomial (B11SplitAlong e (PairCoreSampleIndex k)) ℤ :=
  b11CertificateAlong e single (pairCoreSampleProbeAlong e j) (canonicalPairCoreColumn j)

/-- Splitting at the preceding cone gives the two-variable extension certificate. -/
theorem pairCoreCertificateAlong_oldPrimitiveIndex (j : Fin k) :
    pairCoreCertificateAlong (oldPrimitiveIndex (10 + 2 * k)) j = pairCoreSplitCertificate j := rfl

/-- Every actual rational prefix before the pair has a nonzero C.3 fiber polynomial. -/
theorem specialize_pairCoreCertificateAlong_ne_zero_of_earlier
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e)
    (j : Fin k) (hn : n ≤ 10 + 2 * j.val) (h : n ≤ (10 + 2 * k) + 2) :
    specialize (fun i => primitiveValue Q (primitivePrefixIndex h i))
      (intSumPolynomial ℚ (pairCoreCertificateAlong (primitivePrefixIndex h) j)) ≠ 0 := by
  let e := primitivePrefixIndex h
  let Q' := withC3Parameters Q hQ j
  let old : PrimitiveIndex n → ℚ := fun i => primitiveValue Q (e i)
  let D := c3PairBlockData ℚ j (fun _ => 1) (fun _ => one_ne_zero)
  have hQ' : Q'.single = single := funext hQ
  have hold (i : PrimitiveIndex n) : old i = primitiveValue Q' (e i) :=
    (withC3Parameters_primitivePrefix_eq Q hQ j hn h i).symm
  have hdet : (Matrix.of (fun r c => probeEntry (actualB7Data Q') (pairCoreProbe D r)
      (canonicalPairCoreColumn j c))).det ≠ 0 :=
    actual_pairCoreMatrix_det_ne_zero_withC3Parameters Q hQ j _ _
  have hw := specialize_b11CertificateAlong_ne_zero_of_witness e Q' old (pairCoreSampleValue D) hold
    (pairCoreSampleProbeAlong e j) (pairCoreProbe D) (canonicalPairCoreColumn j)
    (pairCoreSampleProbeAlong_matches e Q' old D) hdet
  simpa only [pairCoreCertificateAlong, hQ'] using hw

end IdealGeneration.CubicSupported.B5
