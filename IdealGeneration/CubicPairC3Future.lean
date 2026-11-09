module

public import IdealGeneration.CubicPairC3Indices
public import IdealGeneration.CubicPairC3LocalWitness
public import IdealGeneration.CubicPrimitiveChart
public import IdealGeneration.CubicIntegerSpecialization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The local C.3 future condition depends on seven coordinates at every level. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B5

open CubicPair CubicRationalFormula CubicMixedLocality RationalChart CubicParameterCompatibility

variable {K : Type*} [Field K] {ι : Type*} {k : ℕ}

private def c3PrimitiveLast : PrimitiveIndex 7 → ℕ
  | .vertexSlope i _ | .vertexHeight i _ => i.val
  | .edgeSlope e _ | .edgeHeight e _ | .edgeLambda e => e.val.2.val

private theorem c3OldRelevant_iff (i : PrimitiveIndex 7) :
    c3OldRelevant i ↔ 3 ≤ c3PrimitiveLast i ∧ c3PrimitiveLast i < 5 := by
  cases i <;> rfl

private theorem c3NewRelevant_iff (i : PrimitiveIndex 7) :
    c3NewRelevant i ↔ 5 ≤ c3PrimitiveLast i := by
  cases i <;> rfl

private def c3Default : PrimitiveIndex 7 → ℕ
  | .vertexSlope _ d | .edgeSlope _ d => if d = 0 then 0 else 1
  | _ => 1

private def c3MaskedValue (L : Parameters K 7) (i : PrimitiveIndex 7) : K :=
  if 3 ≤ c3PrimitiveLast i then primitiveValue L i else (c3Default i : K)

private theorem c3MaskedValue_admissible (L : Parameters K 7) :
    PrimitiveAdmissible L.single (c3MaskedValue L) where
  vertexSlope_ne i := by
    by_cases h : 3 ≤ i.val
    · simpa [c3MaskedValue, c3PrimitiveLast, primitiveValue, h] using L.vertexSlope_ne i
    · simp [c3MaskedValue, c3PrimitiveLast, c3Default, h]
  vertexHeight_ne i d := by
    by_cases h : 3 ≤ i.val
    · simpa [c3MaskedValue, c3PrimitiveLast, primitiveValue, h] using L.vertexHeight_ne i d
    · simp [c3MaskedValue, c3PrimitiveLast, c3Default, h]
  edgeSlope_ne e he := by
    by_cases h : 3 ≤ e.val.2.val
    · simpa [c3MaskedValue, c3PrimitiveLast, primitiveValue, h] using L.edgeSlope_ne e he
    · simp [c3MaskedValue, c3PrimitiveLast, c3Default, h]
  edgeHeight_ne e d := by
    by_cases h : 3 ≤ e.val.2.val
    · simpa [c3MaskedValue, c3PrimitiveLast, primitiveValue, h] using L.edgeHeight_ne e d
    · simp [c3MaskedValue, c3PrimitiveLast, c3Default, h]
  edgeLambda_ne e := by
    by_cases h : 3 ≤ e.val.2.val
    · simpa [c3MaskedValue, c3PrimitiveLast, primitiveValue, h] using L.edgeLambda_ne e
    · simp [c3MaskedValue, c3PrimitiveLast, c3Default, h]

private def c3MaskedParameters (L : Parameters K 7) : Parameters K 7 :=
  parametersOfPrimitive L.single (c3MaskedValue L) (c3MaskedValue_admissible L)

private theorem c3Masked_agreesAt (L : Parameters K 7) (c : Fin 4) :
    AgreesAt (c3MaskedParameters L) L (Function.Embedding.refl (Fin 7)) strictMono_id (centerIndex c) := by
  have hc : 3 ≤ (centerIndex c).val := by simp [centerIndex]
  constructor
  · funext d
    simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, hc]
  · funext d
    simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, hc]
  · intro e he
    have he3 : 3 ≤ e.val.2.val := by
      rcases he with he | he
      · have hfirst : 3 ≤ e.val.1.val := he ▸ hc
        have helt : e.val.1.val < e.val.2.val := e.property
        exact hfirst.trans helt.le
      · exact he ▸ hc
    have he' : edgeImage (Function.Embedding.refl (Fin 7)) strictMono_id e = e := rfl
    rw [he']
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, he3]
    · funext d
      simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, he3]
    · funext d
      simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, he3]

private theorem localC3Matrix_masked (L : Parameters K 7) (samples : Fin 13 → Fin 7 → K) :
    localC3Matrix (c3MaskedParameters L) samples = localC3Matrix L samples := by
  have hc : localC3Coefficients (c3MaskedParameters L) = localC3Coefficients L := by
    funext c q i r
    exact congrFun (mixedLinear_eq_of_agreesAt (c3Masked_agreesAt L c)
      (normalBasis q) (Fin.castAdd 2 i)) r
  have h1 : (c3MaskedParameters L).edgeSlope c3PairEdgeOne 0 = L.edgeSlope c3PairEdgeOne 0 := by
    have h : 3 ≤ c3PairEdgeOne.val.2.val := by decide
    simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, h]
  have h2 : (c3MaskedParameters L).edgeSlope c3PairEdgeTwo 0 = L.edgeSlope c3PairEdgeTwo 0 := by
    have h : 3 ≤ c3PairEdgeTwo.val.2.val := by decide
    simp [c3MaskedParameters, parametersOfPrimitive, c3MaskedValue, c3PrimitiveLast, primitiveValue, h]
  simp only [localC3Matrix, hc, h1, h2]

/-- Retained variables are old, the two added vertices and their edges are new,
and the unused root data are constants. -/
def c3PrimitiveFormula (i : PrimitiveIndex 7) : Formula (C3NewIndex ⊕ C3OldIndex) := by
  classical
  exact if h : c3OldRelevant i then .var (.inr ⟨i, h⟩)
    else if h : c3NewRelevant i then .var (.inl (.inl ⟨i, h⟩)) else (c3Default i : Formula _)

/-- Read the old labels directly in the seven-coordinate chart. -/
def c3LocalOldValue (L : Parameters K 7) (i : C3OldIndex) : K := primitiveValue L i.val

/-- Read the new cone labels and sample coordinates in the seven-coordinate chart. -/
def c3LocalNewValue (L : Parameters K 7) (samples : Fin 13 → Fin 7 → K) : C3NewIndex → K
  | .inl i => primitiveValue L i.val
  | .inr (r, d) => samples r d

private theorem c3PrimitiveFormula_matches (L : Parameters K 7) (samples : Fin 13 → Fin 7 → K)
    (i : PrimitiveIndex 7) :
    Formula.Matches (Sum.elim (c3LocalNewValue L samples) (c3LocalOldValue L))
      (c3PrimitiveFormula i) (primitiveValue (c3MaskedParameters L) i) := by
  rw [c3MaskedParameters, primitiveValue_parametersOfPrimitive]
  by_cases ho : c3OldRelevant i
  · have h3 := ((c3OldRelevant_iff i).mp ho).1
    rw [c3PrimitiveFormula, dite_eq_left ho, c3MaskedValue, ite_eq_left h3]
    exact Formula.Matches.var _ _
  · by_cases hn : c3NewRelevant i
    · have h3 := le_trans (by decide : 3 ≤ 5) ((c3NewRelevant_iff i).mp hn)
      rw [c3PrimitiveFormula, dite_eq_right ho, dite_eq_left hn, c3MaskedValue, ite_eq_left h3]
      exact Formula.Matches.var _ _
    · have h3 : ¬ 3 ≤ c3PrimitiveLast i := by
        rw [c3OldRelevant_iff] at ho
        rw [c3NewRelevant_iff] at hn
        omega
      rw [c3PrimitiveFormula, dite_eq_right ho, dite_eq_right hn, c3MaskedValue, ite_eq_right h3]
      exact Formula.Matches.natCast _ _

private def c3FormulaHalfFace (t : Formula ι) (i c : Fin 7) (x : Fin 7 → Formula ι) (r : Fin 2) :
    Formula ι := ![t, -1] r * x i * x c

private def c3FormulaColumn (coeff : PairLiftCoefficients (Formula ι)) (t1 t2 : Formula ι)
    (c : Fin 26) (x : Fin 7 → Formula ι) (r : Fin 2) : Formula ι :=
  let L := fun center q => Formula.sumFin (fun j : Fin 5 => coeff center q j r * x (Fin.castAdd 2 j))
  let w1 := fun q => x 4 * (L 2 q - L 1 q)
  let w2 := fun q => x 4 * (L 3 q - L 1 q)
  let b1 := fun q => x 3 * (L 2 q - L 0 q)
  let b2 := fun q => x 3 * (L 3 q - L 0 q)
  let columns : Fin 26 → Formula ι :=
    ![w1 0, w1 1, w1 2,
      x 4 * (t1 * L 2 0 - L 2 1), x 4 * (t1 * L 2 1 - L 2 2),
      b1 0, b1 1, b1 2,
      c3FormulaHalfFace t1 4 4 x r, c3FormulaHalfFace t1 4 3 x r,
      c3FormulaHalfFace t1 4 0 x r, c3FormulaHalfFace t1 4 1 x r, c3FormulaHalfFace t1 4 2 x r,
      w2 0, w2 1, w2 2, b2 0, b2 1, b2 2,
      x 3 * (t2 * L 3 0 - L 3 1), x 3 * (t2 * L 3 1 - L 3 2),
      c3FormulaHalfFace t2 3 3 x r, c3FormulaHalfFace t2 3 4 x r,
      c3FormulaHalfFace t2 3 0 x r, c3FormulaHalfFace t2 3 1 x r, c3FormulaHalfFace t2 3 2 x r]
  (if c.val < 13 then x 5 else x 6) * columns c

set_option maxHeartbeats 1000000 in
private theorem c3FormulaColumn_matches (v : ι → K)
    {coeff : PairLiftCoefficients (Formula ι)} {coeff' : PairLiftCoefficients K}
    (hc : ∀ a q j r, Formula.Matches v (coeff a q j r) (coeff' a q j r))
    {t1 t2 : Formula ι} {t1' t2' : K}
    (ht1 : Formula.Matches v t1 t1') (ht2 : Formula.Matches v t2 t2')
    {x : Fin 7 → Formula ι} {x' : Fin 7 → K} (hx : ∀ i, Formula.Matches v (x i) (x' i))
    (c : Fin 26) (r : Fin 2) :
    Formula.Matches v (c3FormulaColumn coeff t1 t2 c x r) (functionColumn coeff' t1' t2' c x' r) := by
  have hL (a : Fin 4) (q : Fin 3) : Formula.Matches v
      (Formula.sumFin (fun j : Fin 5 => coeff a q j r * x (Fin.castAdd 2 j)))
      (basisLiftValue coeff' a q x' r) :=
    Formula.Matches.sumFin (fun j => (hc a q j r).mul (hx (Fin.castAdd 2 j)))
  have hM (i : Fin 7) (a b : Fin 4) (q : Fin 3) := (hx i).mul ((hL a q).sub (hL b q))
  have hE (i : Fin 7) (a : Fin 4) (q p : Fin 3) {t : Formula ι} {t' : K}
      (ht : Formula.Matches v t t') := (hx i).mul ((ht.mul (hL a q)).sub (hL a p))
  have hF (i j : Fin 7) {t : Formula ι} {t' : K} (ht : Formula.Matches v t t') :
      Formula.Matches v (c3FormulaHalfFace t i j x r) (halfFaceValue t' i j x' r) := by
    have hsign : Formula.Matches v (-1 : Formula ι) (-1 : K) := by
      simpa using (Formula.Matches.ofNat v 1).neg
    fin_cases r
    · exact (ht.mul (hx i)).mul (hx j)
    · exact (hsign.mul (hx i)).mul (hx j)
  have hweight : Formula.Matches v (if c.val < 13 then x 5 else x 6)
      (if c.val < 13 then x' 5 else x' 6) := by
    by_cases h : c.val < 13
    · simpa only [ite_eq_left h] using hx 5
    · simpa only [ite_eq_right h] using hx 6
  refine hweight.mul ?_
  fin_cases c
  · exact hM 4 2 1 0
  · exact hM 4 2 1 1
  · exact hM 4 2 1 2
  · exact hE 4 2 0 1 ht1
  · exact hE 4 2 1 2 ht1
  · exact hM 3 2 0 0
  · exact hM 3 2 0 1
  · exact hM 3 2 0 2
  · exact hF 4 4 ht1
  · exact hF 4 3 ht1
  · exact hF 4 0 ht1
  · exact hF 4 1 ht1
  · exact hF 4 2 ht1
  · exact hM 4 3 1 0
  · exact hM 4 3 1 1
  · exact hM 4 3 1 2
  · exact hM 3 3 0 0
  · exact hM 3 3 0 1
  · exact hM 3 3 0 2
  · exact hE 3 3 0 1 ht2
  · exact hE 3 3 1 2 ht2
  · exact hF 3 3 ht2
  · exact hF 3 4 ht2
  · exact hF 3 0 ht2
  · exact hF 3 1 ht2
  · exact hF 3 2 ht2

private def c3BasisFormula (q d : Fin 3) : Formula (C3NewIndex ⊕ C3OldIndex) :=
  if d = q then 1 else 0

private def c3FutureMatrixFormula : Matrix (Fin 26) (Fin 26) (Formula (C3NewIndex ⊕ C3OldIndex)) :=
  fun r c => c3FormulaColumn
    (fun a q j d => mixedLinearFormula c3PrimitiveFormula c3Parameters.single (centerIndex a)
      (c3BasisFormula q) (Fin.castAdd 2 j) d)
    (c3PrimitiveFormula (.edgeSlope c3PairEdgeOne 0)) (c3PrimitiveFormula (.edgeSlope c3PairEdgeTwo 0))
    c (fun i => .var (.inl (.inr ((pairCoreRowEquiv r).1, i)))) (pairCoreRowEquiv r).2

/-- The same integer certificate is used for every pair at every level. -/
def c3FutureCertificate : MvPolynomial (C3NewIndex ⊕ C3OldIndex) ℤ :=
  matrixCertificate c3FutureMatrixFormula

/-- Fixing the retained values gives the polynomial in new cone data and samples. -/
def c3FutureFiber (x : C3OldIndex → K) : MvPolynomial C3NewIndex K :=
  specialize x (intSumPolynomial K c3FutureCertificate)

/-- The local pair polynomial stays nonzero after fixing its old data. -/
def PairGood (P : Parameters K (10 + 2 * k)) (j : Fin k) : Prop :=
  c3FutureFiber (c3OldValue P j) ≠ 0

/-- Retained local conditions persist under actual compatible extensions. -/
theorem pairGood_castSucc_iff {P : Parameters K (10 + 2 * k)}
    {Q : Parameters K ((10 + 2 * k) + 2)} (h : Compatible P Q) (j : Fin k) :
    PairGood Q j.castSucc ↔ PairGood P j := by
  unfold PairGood
  rw [c3OldValue_compatible h j]

/-- Evaluation of the local certificate is equivalent to nonsingularity of the local block. -/
theorem eval_c3FutureCertificate_ne_zero_iff_local (L : Parameters K 7)
    (hL : L.single = c3Parameters.single) (samples : Fin 13 → Fin 7 → K) :
    evalPolynomial (Sum.elim (c3LocalNewValue L samples) (c3LocalOldValue L)) c3FutureCertificate ≠ 0 ↔
      (localC3Matrix L samples).det ≠ 0 := by
  rw [← localC3Matrix_masked L samples]
  apply eval_matrixCertificate_ne_zero_iff_of_matches
  intro r c
  let v := Sum.elim (c3LocalNewValue L samples) (c3LocalOldValue L)
  let L' := c3MaskedParameters L
  have hL' : L'.single = c3Parameters.single := hL
  have hb (q d : Fin 3) : Formula.Matches v (c3BasisFormula q d) (normalBasis q d) := by
    by_cases h : d = q
    · simpa [c3BasisFormula, normalBasis, h] using Formula.Matches.ofNat v 1
    · simpa [c3BasisFormula, normalBasis, h] using Formula.Matches.ofNat v 0
  have hcoeff (a : Fin 4) (q : Fin 3) (i : Fin 5) (d : Fin 2) : Formula.Matches v
      (mixedLinearFormula c3PrimitiveFormula c3Parameters.single (centerIndex a)
        (c3BasisFormula q) (Fin.castAdd 2 i) d) (localC3Coefficients L' a q i d) := by
    rw [← hL']
    exact mixedLinearFormula_matches c3PrimitiveFormula v L' (c3PrimitiveFormula_matches L samples)
      (hb q) (centerIndex a) (Fin.castAdd 2 i) d
  exact c3FormulaColumn_matches v hcoeff
    (c3PrimitiveFormula_matches L samples (.edgeSlope c3PairEdgeOne 0))
    (c3PrimitiveFormula_matches L samples (.edgeSlope c3PairEdgeTwo 0))
    (fun i => Formula.Matches.var v (.inl (.inr ((pairCoreRowEquiv r).1, i)))) c (pairCoreRowEquiv r).2

/-- The rational values of the retained C.3 witness. -/
def c3OldWitness : C3OldIndex → ℚ := c3LocalOldValue c3Parameters

/-- The rational future coordinates and samples of C.3. -/
def c3NewWitness : C3NewIndex → ℚ := c3LocalNewValue c3Parameters RationalConstruction.samplePointsQ

/-- C.3 gives a nonzero value of the integer certificate. -/
theorem eval_c3FutureCertificate_witness_ne_zero :
    evalPolynomial (Sum.elim c3NewWitness c3OldWitness) c3FutureCertificate ≠ 0 := by
  exact (eval_c3FutureCertificate_ne_zero_iff_local c3Parameters rfl
    RationalConstruction.samplePointsQ).mpr localC3Matrix_c3Parameters_det_ne_zero

/-- The rational old data from C.3 satisfy the retained condition. -/
theorem c3FutureFiber_oldWitness_ne_zero : c3FutureFiber c3OldWitness ≠ 0 :=
  specialize_intSumPolynomial_ne_zero_of_eval ℚ c3OldWitness c3NewWitness _
    eval_c3FutureCertificate_witness_ne_zero

end IdealGeneration.CubicSupported.B5
