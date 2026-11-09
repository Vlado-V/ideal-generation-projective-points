module

public import IdealGeneration.CubicB11Split
public import IdealGeneration.CubicPairC3Extension

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The C.3 witness for the actual pair-core polynomial of B.6. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicRationalFormula RationalChart

variable {K : Type*} [Field K] {k : ℕ} {j : Fin k}

/-- The two components at each point share its coordinates and weights. -/
abbrev PairCoreSampleIndex (k : ℕ) := Fin 13 × (Fin (10 + 2 * k) ⊕ Fin 2)

/-- The symbolic supported row for a chosen split of the primitive labels. -/
def pairCoreSampleProbeAlong {n : ℕ} (e : PrimitiveIndex n ↪ PrimitiveIndex ((10 + 2 * k) + 2))
    (j : Fin k) (r : Fin 26) : B11ProbeFormula (B11SplitAlong e (PairCoreSampleIndex k)) (10 + 2 * k) :=
  let p := pairCoreRowEquiv r
  ⟨pairSupport j, fun i => .var (.inl (.inr (p.1, .inl i))),
    fun b => .var (.inl (.inr (p.1, .inr b))), p.2⟩

/-- The supported symbolic row in the actual C.3 row order. -/
def pairCoreSampleProbe (j : Fin k) (r : Fin 26) :
    B11ProbeFormula (B11SplitIndex (10 + 2 * k) (PairCoreSampleIndex k)) (10 + 2 * k) :=
  pairCoreSampleProbeAlong (oldPrimitiveIndex (10 + 2 * k)) j r

/-- Actual values for the freely chosen pair-core samples. -/
def pairCoreSampleValue (D : PairBlockData K k j) : PairCoreSampleIndex k → K
  | (r, .inl i) => D.point r i
  | (r, .inr b) => D.weight r b

/-- The component row agrees with the actual sample under any primitive split. -/
theorem pairCoreSampleProbeAlong_matches {n : ℕ}
    (e : PrimitiveIndex n ↪ PrimitiveIndex ((10 + 2 * k) + 2))
    (Q : Parameters K ((10 + 2 * k) + 2)) (old : PrimitiveIndex n → K)
    (D : PairBlockData K k j) (r : Fin 26) :
    (pairCoreSampleProbeAlong e j r).Matches (b11AssignmentAlong e Q old (pairCoreSampleValue D))
      (pairCoreProbe D r) :=
  ⟨fun _ _ => Formula.Matches.var _ _, D.supported (pairCoreRowEquiv r).1,
    fun _ => Formula.Matches.var _ _, rfl⟩

/-- The old cone primitives, new cone primitives and samples of one actual block. -/
def pairCoreSplitAssignment (Q : Parameters K ((10 + 2 * k) + 2)) (D : PairBlockData K k j) :
    B11SplitIndex (10 + 2 * k) (PairCoreSampleIndex k) → K :=
  b11SplitAssignment Q (fun i => primitiveValue Q (oldPrimitiveIndex (10 + 2 * k) i))
    (pairCoreSampleValue D)

/-- Compatibility identifies the old values in the block with the preceding cone. -/
theorem pairCoreSplitAssignment_eq_of_compatible
    {P : Parameters K (10 + 2 * k)} {Q : Parameters K ((10 + 2 * k) + 2)}
    (h : Compatible P Q) (D : PairBlockData K k j) :
    pairCoreSplitAssignment Q D = b11SplitAssignment Q (primitiveValue P) (pairCoreSampleValue D) := by
  have hold : (fun i => primitiveValue Q (oldPrimitiveIndex (10 + 2 * k) i)) = primitiveValue P :=
    funext (primitiveValue_oldPrimitiveIndex h)
  rw [pairCoreSplitAssignment, hold]

/-- The pair-core determinant polynomial with all primitive and sample variables displayed. -/
def pairCoreSplitCertificate (j : Fin k) :
    MvPolynomial (B11SplitIndex (10 + 2 * k) (PairCoreSampleIndex k)) ℤ :=
  b11SplitCertificate single (pairCoreSampleProbe j) (canonicalPairCoreColumn j)

/-- The symbolic row evaluates to the actual component of the supported sample. -/
theorem pairCoreSampleProbe_matches (Q : Parameters K ((10 + 2 * k) + 2))
    (D : PairBlockData K k j) (r : Fin 26) :
    (pairCoreSampleProbe j r).Matches (pairCoreSplitAssignment Q D) (pairCoreProbe D r) :=
  pairCoreSampleProbeAlong_matches _ Q _ D r

/-- The primitive-coordinate certificate detects the actual pair-core block. -/
theorem eval_pairCoreSplitCertificate_ne_zero_iff (Q : Parameters K ((10 + 2 * k) + 2))
    (hQ : Q.single = single) (D : PairBlockData K k j)
    (hD : D.coreColumn = canonicalPairCoreColumn j) :
    evalPolynomial (pairCoreSplitAssignment Q D) (pairCoreSplitCertificate j) ≠ 0 ↔
      (pairCoreMatrix (actualB7Data Q) D).det ≠ 0 := by
  have hs := eval_b11Certificate_ne_zero_iff Q (pairCoreSplitAssignment Q D)
    (b11SplitPrimitive (10 + 2 * k)) (b11SplitPrimitive_matches Q _ (pairCoreSampleValue D) (fun _ => rfl))
    (pairCoreSampleProbe j) (pairCoreProbe D) (canonicalPairCoreColumn j) (pairCoreSampleProbe_matches Q D)
  have hmat : (Matrix.of (fun r c => probeEntry (actualB7Data Q) (pairCoreProbe D r)
      (canonicalPairCoreColumn j c))) = pairCoreMatrix (actualB7Data Q) D := by
    rw [← hD]
    rfl
  rw [hmat] at hs
  simpa only [pairCoreSplitCertificate, b11SplitCertificate, hQ] using hs

/-- The primitive indices belonging entirely to the prefix before the pair. -/
def pairCorePrimitiveEarlier (j : Fin k) {N : ℕ} : PrimitiveIndex N → Prop
  | .vertexSlope i _ | .vertexHeight i _ => i.val < 10 + 2 * j.val
  | .edgeSlope e _ | .edgeHeight e _ | .edgeLambda e => e.val.2.val < 10 + 2 * j.val

/-- The old primitive indices belonging entirely to the prefix before the pair. -/
abbrev pairCoreOldPrefix (j : Fin k) : PrimitiveIndex (10 + 2 * k) → Prop :=
  pairCorePrimitiveEarlier j

private theorem withC3Parameters_primitive_eq_of_earlier
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e)
    (j : Fin k) (i : PrimitiveIndex ((10 + 2 * k) + 2)) (hi : pairCorePrimitiveEarlier j i) :
    primitiveValue (withC3Parameters Q hQ j) i = primitiveValue Q i := by
  cases i with
  | vertexSlope i d =>
    exact congrFun (withC3Parameters_vertex_eq_of_earlier Q hQ j (i := i) hi).1 d
  | vertexHeight i d =>
    exact congrFun (withC3Parameters_vertex_eq_of_earlier Q hQ j (i := i) hi).2 d
  | edgeSlope e d =>
    exact congrFun (withC3Parameters_edge_eq_of_earlier Q hQ j (e := e) hi).1 d
  | edgeHeight e d =>
    exact congrFun (withC3Parameters_edge_eq_of_earlier Q hQ j (e := e) hi).2.1 d
  | edgeLambda e =>
    exact (withC3Parameters_edge_eq_of_earlier Q hQ j (e := e) hi).2.2

/-- Installing C.3 preserves the parameters indexed by any earlier prefix. -/
theorem withC3Parameters_primitivePrefix_eq
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e)
    (j : Fin k) {n : ℕ} (hn : n ≤ 10 + 2 * j.val) (h : n ≤ (10 + 2 * k) + 2)
    (i : PrimitiveIndex n) :
    primitiveValue (withC3Parameters Q hQ j) (primitivePrefixIndex h i) =
      primitiveValue Q (primitivePrefixIndex h i) := by
  apply withC3Parameters_primitive_eq_of_earlier
  cases i with
  | vertexSlope i _ => exact lt_of_lt_of_le i.isLt hn
  | vertexHeight i _ => exact lt_of_lt_of_le i.isLt hn
  | edgeSlope e _ => exact lt_of_lt_of_le e.val.2.isLt hn
  | edgeHeight e _ => exact lt_of_lt_of_le e.val.2.isLt hn
  | edgeLambda e => exact lt_of_lt_of_le e.val.2.isLt hn

/-- The C.3 assignment gives a nonzero value with all earlier primitives fixed. -/
theorem exists_pairCoreSplitCertificate_witness_with_prefix
    (Q : Parameters ℚ ((10 + 2 * k) + 2)) (hQ : ∀ e, Q.single e = single e) (j : Fin k) :
    ∃ x : B11SplitIndex (10 + 2 * k) (PairCoreSampleIndex k) → ℚ,
      evalPolynomial x (pairCoreSplitCertificate j) ≠ 0 ∧
        ∀ i, pairCoreOldPrefix j i → x (.inr i) = primitiveValue Q (oldPrimitiveIndex (10 + 2 * k) i) := by
  let D := c3PairBlockData ℚ j (fun _ => 1) (fun _ => one_ne_zero)
  let Q' := withC3Parameters Q hQ j
  have hQ' : Q'.single = single := funext hQ
  refine ⟨pairCoreSplitAssignment Q' D, ?_, ?_⟩
  · exact (eval_pairCoreSplitCertificate_ne_zero_iff Q' hQ' D rfl).mpr
      (actual_pairCoreMatrix_det_ne_zero_withC3Parameters Q hQ j _ _)
  · intro i hi
    apply withC3Parameters_primitive_eq_of_earlier
    cases i <;> exact hi

private def pairCoreBaseParameters (k : ℕ) : Parameters ℚ ((10 + 2 * k) + 2) where
  single := single
  vertexSlope _ d := if d = 0 then 0 else 1
  vertexHeight _ _ := 1
  edgeSlope _ d := if d = 0 then 0 else 1
  edgeHeight _ _ := 1
  edgeLambda _ := 1
  vertexSlope_ne _ := by norm_num
  vertexHeight_ne _ _ := one_ne_zero
  edgeSlope_ne _ _ := by norm_num
  edgeHeight_ne _ _ := one_ne_zero
  edgeLambda_ne _ := one_ne_zero

/-- The determinant polynomial is nonzero over the integers. -/
theorem pairCoreSplitCertificate_ne_zero (j : Fin k) : pairCoreSplitCertificate j ≠ 0 := by
  obtain ⟨x, hx, _⟩ := exists_pairCoreSplitCertificate_witness_with_prefix
    (pairCoreBaseParameters k) (fun _ => rfl) j
  intro h
  exact hx (by rw [h, map_zero])

/-- The same polynomial is nonzero over every characteristic-zero field. -/
theorem map_pairCoreSplitCertificate_ne_zero [CharZero K] (j : Fin k) :
    MvPolynomial.map (Int.castRingHom K) (pairCoreSplitCertificate j) ≠ 0 := by
  have hinj : Function.Injective (MvPolynomial.map
    (σ := B11SplitIndex (10 + 2 * k) (PairCoreSampleIndex k)) (Int.castRingHom K)) :=
    MvPolynomial.map_injective _ Int.cast_injective
  simpa using hinj.ne (pairCoreSplitCertificate_ne_zero j)

end IdealGeneration.CubicSupported.B5
