module

public import IdealGeneration.CubicB11Split
public import IdealGeneration.CubicIntegerSpecialization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Nonzero B.11 polynomials after specializing a fixed primitive prefix. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open RationalChart CubicRationalFormula CubicParameterCompatibility

variable {K : Type*} [Field K] {m n : ℕ} {Sample : Type*}

/-- The block polynomial in the primitive prefix and the remaining cone and sample variables. -/
def b11CertificateAlong (e : PrimitiveIndex n ↪ PrimitiveIndex (m + 2))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (single : Edge (m + 2) → Bool)
    (rows : ι → B11ProbeFormula (B11SplitAlong e Sample) m) (cols : ι → B7Column m) :
    MvPolynomial (B11SplitAlong e Sample) ℤ :=
  b11Certificate (b11PrimitiveAlong e) single rows cols

/-- One actual nonsingular block with the specified prefix gives a nonzero polynomial
in the remaining cone and sample variables after specializing that prefix. -/
theorem specialize_b11CertificateAlong_ne_zero_of_witness
    (e : PrimitiveIndex n ↪ PrimitiveIndex (m + 2))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Parameters K (m + 2))
    (old : PrimitiveIndex n → K) (samples : Sample → K)
    (hold : ∀ i, old i = primitiveValue Q (e i))
    (rows : ι → B11ProbeFormula (B11SplitAlong e Sample) m) (probes : ι → B11Probe K m)
    (cols : ι → B7Column m) (hrows : ∀ i, (rows i).Matches (b11AssignmentAlong e Q old samples) (probes i))
    (hdet : (Matrix.of (fun i j => probeEntry (actualB7Data Q) (probes i) (cols j))).det ≠ 0) :
    specialize old (intSumPolynomial K (b11CertificateAlong e Q.single rows cols)) ≠ 0 := by
  apply specialize_intSumPolynomial_ne_zero_of_eval K old
    (Sum.elim (fun i : NewPrimitiveAlong e => primitiveValue Q i.val) samples)
  exact (eval_b11Certificate_ne_zero_iff Q _ _
    (b11PrimitiveAlong_matches e Q old samples hold) rows probes cols hrows).mpr hdet

end IdealGeneration.CubicSupported.B5
