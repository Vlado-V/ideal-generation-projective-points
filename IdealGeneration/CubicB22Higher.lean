module

public import IdealGeneration.CubicPairExtensionLabels
public import IdealGeneration.CubicPhiLocalColumns
public import IdealGeneration.CubicMixedLocality
public import IdealGeneration.CubicProbeDeformation
public import IdealGeneration.CubicAllowedValues
public import IdealGeneration.FiniteCertificate
public import IdealGeneration.CubicSupportedConfiguration
public import IdealGeneration.CubicSupportedPattern
public import IdealGeneration.CubicSupportedCounts
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! The higher columns and their pivot supports in the B.22 block of Appendix B. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B22

open MvPolynomial

variable {K : Type*} [Field K] {m : ℕ} (Q : Parameters K (m + 2))

/-- The normal quadratic basis is ordered `s², st, t²`. -/
def basisQuadratic (q : Fin 3) : Fin 3 → K := fun r => if r = q then 1 else 0

/-- The higher column for a new single edge and a new trace multiplier. -/
def edgeColumn (p : NewIncidence Q) (b : Fin 2) (k : Fin 2) : Poly K (m + 2) :=
  X (Fin.natAdd m b) * C (Q.edgeLinear (crossSingleEdge Q p) k) *
    X (Fin.castAdd 2 p.val.1) * X (Fin.natAdd m p.val.2)

/-- The three motion columns between the two new vertices. -/
def motionColumn (q : Fin 3) (k : Fin 2) : Poly K (m + 2) :=
  X (Fin.natAdd m 0) * X (Fin.natAdd m 1) *
    ((∑ j, C (Q.mixedLinear (Fin.natAdd m 1) (basisQuadratic q) j k) * X j) -
      (∑ j, C (Q.mixedLinear (Fin.natAdd m 0) (basisQuadratic q) j k) * X j))

/-- The scalar component of a higher edge column at a trace point. -/
def edgeValue (p : NewIncidence Q) (b : Fin 2) (y : Fin (m + 2) → K) (k : Fin 2) : K :=
  Q.edgeLinear (crossSingleEdge Q p) k * y (Fin.castAdd 2 p.val.1) *
    y (Fin.natAdd m p.val.2) * y (Fin.natAdd m b)

/-- The scalar component of a higher motion column at a trace point. -/
def motionValue (q : Fin 3) (y : Fin (m + 2) → K) (k : Fin 2) : K :=
  y (Fin.natAdd m 0) * y (Fin.natAdd m 1) *
    ((∑ j, Q.mixedLinear (Fin.natAdd m 1) (basisQuadratic q) j k * y j) -
      (∑ j, Q.mixedLinear (Fin.natAdd m 0) (basisQuadratic q) j k * y j))

@[simp] theorem eval_edgeColumn (p : NewIncidence Q) (b k : Fin 2) (y : Fin (m + 2) → K) :
    eval y (edgeColumn Q p b k) = edgeValue Q p b y k := by
  simp [edgeColumn, edgeValue]
  ring

@[simp] theorem eval_motionColumn (q : Fin 3) (k : Fin 2) (y : Fin (m + 2) → K) :
    eval y (motionColumn Q q k) = motionValue Q q y k := by
  simp [motionColumn, motionValue, map_sum]

/-- The actual trace representative of a new single edge. -/
def edgeRow (p : NewIncidence Q) : Fin (m + 2) → K :=
  edgeSupport (crossEdge p.val.1 p.val.2) 1 (Q.edgeLambda (crossEdge p.val.1 p.val.2))

@[simp] theorem traceRepresentative_edgeRow {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (p : NewIncidence Q) :
    Q.traceRepresentative free (.inl (.inr (crossEdge p.val.1 p.val.2))) = edgeRow Q p := rfl

/-- An edge row sees only the edge's own same-direction multiplier. -/
theorem edgeValue_edgeRow (p r : NewIncidence Q) (b k : Fin 2) :
    edgeValue Q r b (edgeRow Q p) k =
      if r = p ∧ b = p.val.2 then Q.edgeLinear (crossSingleEdge Q p) k *
        (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 else 0 := by
  by_cases hr : r = p
  · subst r
    by_cases hb : b = p.val.2 <;> simp [edgeValue, edgeRow, vertexSupport, hb, pow_two, mul_assoc]
  · by_cases hi : r.val.1 = p.val.1
    · have hd : r.val.2 ≠ p.val.2 := fun h => hr (Subtype.ext (Prod.ext hi h))
      simp [edgeValue, edgeRow, vertexSupport, hr, hd]
    · simp [edgeValue, edgeRow, vertexSupport, hr, hi]

/-- The motion columns vanish on an edge support with only one new coordinate. -/
theorem motionValue_edgeRow (p : NewIncidence Q) (q : Fin 3) (k : Fin 2) :
    motionValue Q q (edgeRow Q p) k = 0 := by
  by_cases hb : p.val.2 = 0
  · simp [motionValue, edgeRow, vertexSupport, hb]
  · have hb₁ : p.val.2 = 1 := Fin.eq_one_of_ne_zero _ hb
    simp [motionValue, edgeRow, vertexSupport, hb₁]

/-- In the allowed scalar coordinate `-t`, the same-index pivot is the square of `λ`. -/
theorem edgeRow_pivot (p : NewIncidence Q) :
    -edgeValue Q p p.val.2 (edgeRow Q p) 1 = (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 := by
  rw [edgeValue_edgeRow]
  simp [Parameters.edgeLinear]

theorem edgeRow_pivot_ne_zero (p : NewIncidence Q) :
    -edgeValue Q p p.val.2 (edgeRow Q p) 1 ≠ 0 := by
  rw [edgeRow_pivot]
  exact pow_ne_zero _ (Q.edgeLambda_ne _)

/-- The remaining multiplier is the other direction in the new pair. -/
def crossValue (p : NewIncidence Q) (y : Fin (m + 2) → K) (k : Fin 2) : K :=
  edgeValue Q p p.val.2.rev y k

/-- A paired free probe has unit values at both chosen old vertices and both new vertices. -/
def pairProbe (i j : Fin m) : Fin (m + 2) → K :=
  Fin.addCases (fun r => vertexSupport i 1 r + vertexSupport j 1 r) 1

@[simp] theorem pairProbe_old (i j r : Fin m) :
    pairProbe (K := K) i j (Fin.castAdd 2 r) = vertexSupport i 1 r + vertexSupport j 1 r :=
  Fin.addCases_left r

@[simp] theorem pairProbe_new (i j : Fin m) (b : Fin 2) :
    pairProbe (K := K) i j (Fin.natAdd m b) = 1 := Fin.addCases_right b

/-- A paired free probe reads a cross column only at its old endpoint. -/
theorem crossValue_pairProbe (p : NewIncidence Q) (i j : Fin m) (k : Fin 2) :
    crossValue Q p (pairProbe i j) k = Q.edgeLinear (crossSingleEdge Q p) k *
      (vertexSupport i 1 p.val.1 + vertexSupport j 1 p.val.1) := by
  simp [crossValue, edgeValue]

/-- If the old endpoint is absent, the cross column vanishes on that paired probe. -/
theorem crossValue_pairProbe_off (p : NewIncidence Q) (i j : Fin m) (k : Fin 2)
    (hi : p.val.1 ≠ i) (hj : p.val.1 ≠ j) : crossValue Q p (pairProbe i j) k = 0 := by
  simp [crossValue_pairProbe, vertexSupport, hi, hj]

/-- Distinct old endpoints isolate the two cross columns among all cross columns
when the incidence map to old vertices is injective. -/
theorem crossValue_pairProbe_other (a b p : NewIncidence Q)
    (hinj : Function.Injective (fun r : NewIncidence Q => r.val.1))
    (ha : p ≠ a) (hb : p ≠ b) (k : Fin 2) :
    crossValue Q p (pairProbe a.val.1 b.val.1) k = 0 :=
  crossValue_pairProbe_off Q p _ _ k (fun h => ha (hinj h)) (fun h => hb (hinj h))

/-- The two scalar rows at a paired probe, restricted to its two cross columns. -/
def pairProbeMatrix (a b : NewIncidence Q) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun k c => crossValue Q (![a, b] c) (pairProbe a.val.1 b.val.1) k

/-- The paired rows give exactly the two graph normal lines. -/
theorem pairProbeMatrix_eq (a b : NewIncidence Q) (hab : a.val.1 ≠ b.val.1) :
    pairProbeMatrix Q a b =
      !![Q.edgeSlope (crossEdge a.val.1 a.val.2) 0, Q.edgeSlope (crossEdge b.val.1 b.val.2) 0;
        -1, -1] := by
  ext k c
  fin_cases k <;> fin_cases c <;>
    simp [pairProbeMatrix, crossValue_pairProbe, vertexSupport, Parameters.edgeLinear, hab, hab.symm]

/-- The paired scalar rows are nonsingular when their two slopes differ. -/
theorem pairProbeMatrix_det_ne_zero (a b : NewIncidence Q) (hab : a.val.1 ≠ b.val.1)
    (hτ : Q.edgeSlope (crossEdge a.val.1 a.val.2) 0 ≠
      Q.edgeSlope (crossEdge b.val.1 b.val.2) 0) : (pairProbeMatrix Q a b).det ≠ 0 := by
  rw [pairProbeMatrix_eq Q a b hab, Matrix.det_fin_two]
  simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hτ.symm

/-- A final probe has one old coordinate and the two new coordinates. -/
def finalProbe (i : Fin m) (x : Fin 3 → K) : Fin (m + 2) → K :=
  Fin.addCases (vertexSupport i (x 0)) ![x 1, x 2]

@[simp] theorem finalProbe_old (i j : Fin m) (x : Fin 3 → K) :
    finalProbe i x (Fin.castAdd 2 j) = vertexSupport i (x 0) j := Fin.addCases_left j

@[simp] theorem finalProbe_new (i : Fin m) (b : Fin 2) (x : Fin 3 → K) :
    finalProbe i x (Fin.natAdd m b) = ![x 1, x 2] b := Fin.addCases_right b

/-- Final probes annihilate every cross column at a different old endpoint. -/
theorem crossValue_finalProbe_off (p : NewIncidence Q) (i : Fin m) (x : Fin 3 → K)
    (h : p.val.1 ≠ i) (k : Fin 2) : crossValue Q p (finalProbe i x) k = 0 := by
  simp [crossValue, edgeValue, vertexSupport, h]

/-- The unpaired cross column has the `xuv` factor in the final block. -/
theorem crossValue_finalProbe (p : NewIncidence Q) (x : Fin 3 → K) (k : Fin 2) :
    crossValue Q p (finalProbe p.val.1 x) k =
      Q.edgeLinear (crossSingleEdge Q p) k * x 0 * x 1 * x 2 := by
  rcases p with ⟨⟨i, b⟩, hb⟩
  fin_cases b
  · simp [crossValue, edgeValue, vertexSupport, Fin.rev]
  · simp [crossValue, edgeValue, vertexSupport, Fin.rev]
    ring

/-- The three trace coordinate indices in the final probe. -/
def finalCoordinate (i : Fin m) (j : Fin 3) : Fin (m + 2) :=
  ![Fin.castAdd 2 i, Fin.natAdd m 0, Fin.natAdd m 1] j

private theorem linearSum_finalProbe (a : Fin (m + 2) → K) (i : Fin m) (x : Fin 3 → K) :
    (∑ j, a j * finalProbe i x j) =
      a (Fin.castAdd 2 i) * x 0 + a (Fin.natAdd m 0) * x 1 + a (Fin.natAdd m 1) * x 2 := by
  rw [Fin.sum_univ_add]
  simp [Fin.sum_univ_two, vertexSupport, mul_ite]
  ring

/-- Only the three local lift coefficients enter a motion column at a final probe. -/
theorem motionValue_finalProbe (i : Fin m) (q : Fin 3) (x : Fin 3 → K) (k : Fin 2) :
    motionValue Q q (finalProbe i x) k = x 1 * x 2 *
      ∑ j, (Q.mixedLinear (Fin.natAdd m 1) (basisQuadratic q) (finalCoordinate i j) k -
        Q.mixedLinear (Fin.natAdd m 0) (basisQuadratic q) (finalCoordinate i j) k) * x j := by
  rw [motionValue, linearSum_finalProbe, linearSum_finalProbe]
  simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff, Fin.sum_univ_three, finalCoordinate]
  ring

/-- The four final columns in the order of Appendix C.4. -/
def finalColumnValue (p : NewIncidence Q) (x : Fin 3 → K) (c : Fin 4) (k : Fin 2) : K :=
  ![crossValue Q p (finalProbe p.val.1 x) k,
    motionValue Q 0 (finalProbe p.val.1 x) k,
    motionValue Q 1 (finalProbe p.val.1 x) k,
    motionValue Q 2 (finalProbe p.val.1 x) k] c

/-- The last four rows use the two probes, listing both components of each. -/
def finalProbeMatrix (p : NewIncidence Q) (x : Fin 2 → Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun r c => finalColumnValue Q p
    (x ⟨r.val / 2, by omega⟩) c ⟨r.val % 2, by omega⟩

section Actual

open CubicMiddle

variable {f : ℕ} (free : Fin f → Fin (m + 2) → K) (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0)

/-- The literal higher edge column is the actual independent single-edge parameter column. -/
theorem edgeColumn_parameterPhi (p : NewIncidence Q) (b k : Fin 2) :
    (Q.parameterPhi free h₂ h₆
      (Q.singleEdgeParameter (Fin.natAdd m b) (crossSingleEdge Q p)) k).val =
      edgeColumn Q p b k :=
  Q.parameterPhi_singleEdge free h₂ h₆ (Fin.natAdd m b) (crossSingleEdge Q p) k

/-- The literal motion column is the actual independent antisymmetric parameter column. -/
theorem motionColumn_parameterPhi (q : Fin 3) (k : Fin 2) :
    (Q.parameterPhi free h₂ h₆ (Q.mixedEdgeParameter (newPairEdge m) (basisQuadratic q)) k).val =
      motionColumn Q q k :=
  Q.parameterPhi_mixedEdge free h₂ h₆ (newPairEdge m) (basisQuadratic q) k

variable (hheight : ∀ i, (Q.toConeConfiguration free).height i ≠ 0)

/-- Evaluating the actual explicit parameter map at a trace label evaluates its `Φ` column. -/
theorem parameterEvaluation_atLabel (x : Q.EliminatedParameters) (a : TraceLabel (m + 2) f)
    (k : Fin 2) :
    (Q.parameterEvaluation free h₂ h₆ hheight x).val (traceLabelEquiv (m + 2) f a) k =
      eval (Q.traceRepresentative free a) (Q.parameterPhi free h₂ h₆ x k).val := by
  change eval ((Q.toConeConfiguration free).trace (traceLabelEquiv (m + 2) f a))
    (Q.parameterPhi free h₂ h₆ x k).val = _
  rw [Q.toConeConfiguration_trace]

/-- The free coordinates of the actual allowed evaluation are both evaluations at the free point. -/
theorem parameterEvaluation_free (x : Q.EliminatedParameters) (j : Fin f) (k : Fin 2) :
    (Q.allowedValuesEquiv free (Q.parameterEvaluation free h₂ h₆ hheight x)).2 j k =
      eval (free j) (Q.parameterPhi free h₂ h₆ x k).val :=
  parameterEvaluation_atLabel Q free h₂ h₆ hheight x (.inr j) k

/-- The actual allowed single-edge row has exactly one higher edge pivot. -/
theorem edgeParameterEvaluation_edgeRow (p r : NewIncidence Q) (b : Fin 2) :
    (Q.allowedValuesEquiv free (Q.parameterEvaluation free h₂ h₆ hheight
      (Q.singleEdgeParameter (Fin.natAdd m b) (crossSingleEdge Q r)))).1 (crossSingleEdge Q p) =
      if r = p ∧ b = p.val.2 then (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 else 0 := by
  change -(Q.parameterEvaluation free h₂ h₆ hheight
    (Q.singleEdgeParameter (Fin.natAdd m b) (crossSingleEdge Q r))).val
    (traceLabelEquiv (m + 2) f (.inl (.inr (crossEdge p.val.1 p.val.2)))) 1 = _
  rw [parameterEvaluation_atLabel, traceRepresentative_edgeRow, edgeColumn_parameterPhi,
    eval_edgeColumn, edgeValue_edgeRow]
  split_ifs <;> simp [Parameters.edgeLinear]

/-- The actual allowed single-edge rows annihilate all three higher motion parameters. -/
theorem motionParameterEvaluation_edgeRow (p : NewIncidence Q) (q : Fin 3) :
    (Q.allowedValuesEquiv free (Q.parameterEvaluation free h₂ h₆ hheight
      (Q.mixedEdgeParameter (newPairEdge m) (basisQuadratic q)))).1 (crossSingleEdge Q p) = 0 := by
  change -(Q.parameterEvaluation free h₂ h₆ hheight
    (Q.mixedEdgeParameter (newPairEdge m) (basisQuadratic q))).val
    (traceLabelEquiv (m + 2) f (.inl (.inr (crossEdge p.val.1 p.val.2)))) 1 = 0
  rw [parameterEvaluation_atLabel, traceRepresentative_edgeRow, motionColumn_parameterPhi,
    eval_motionColumn, motionValue_edgeRow, neg_zero]

end Actual

/-- Higher columns consist of two multipliers per new incidence and three motion columns. -/
abbrev HigherColumn (Q : Parameters K (m + 2)) := (NewIncidence Q × Fin 2) ⊕ Fin 3

/-- The independent B.2 parameter representing a higher column. -/
def highParameter : HigherColumn Q → Q.EliminatedParameters
  | .inl (p, b) => Q.singleEdgeParameter (Fin.natAdd m b) (crossSingleEdge Q p)
  | .inr q => Q.mixedEdgeParameter (newPairEdge m) (basisQuadratic q)

/-- The two polynomial components of a higher column. -/
def higherPolynomial : HigherColumn Q → Fin 2 → Poly K (m + 2)
  | .inl (p, b) => edgeColumn Q p b
  | .inr q => motionColumn Q q

/-- Every higher polynomial is the corresponding actual `Φ` column. -/
theorem higherPolynomial_parameterPhi {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (a : HigherColumn Q) (k : Fin 2) :
    (Q.parameterPhi free h₂ h₆ (highParameter Q a) k).val = higherPolynomial Q a k := by
  rcases a with ⟨p, b⟩ | q
  · exact edgeColumn_parameterPhi Q free h₂ h₆ p b k
  · exact motionColumn_parameterPhi Q free h₂ h₆ q k

/-- The actual single-edge rows are diagonal on the same-direction higher parameters. -/
theorem higherParameterEvaluation_edgeRow {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (hheight : ∀ i, (Q.toConeConfiguration free).height i ≠ 0)
    (p : NewIncidence Q) (a : HigherColumn Q) :
    (Q.allowedValuesEquiv free (Q.parameterEvaluation free h₂ h₆ hheight (highParameter Q a))).1
        (crossSingleEdge Q p) =
      if a = .inl (p, p.val.2) then (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 else 0 := by
  rcases a with ⟨r, b⟩ | q
  · simpa [highParameter] using edgeParameterEvaluation_edgeRow Q free h₂ h₆ hheight p r b
  · simpa [highParameter] using motionParameterEvaluation_edgeRow Q free h₂ h₆ hheight p q

/-- The actual free rows evaluate both higher polynomial components. -/
theorem higherParameterEvaluation_free {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (hheight : ∀ i, (Q.toConeConfiguration free).height i ≠ 0)
    (a : HigherColumn Q) (j : Fin f) (k : Fin 2) :
    (Q.allowedValuesEquiv free (Q.parameterEvaluation free h₂ h₆ hheight (highParameter Q a))).2 j k =
      eval (free j) (higherPolynomial Q a k) := by
  rw [parameterEvaluation_free, higherPolynomial_parameterPhi]

/-- A higher edge column has two factors from the new trace coordinates. -/
theorem movingEvaluation_edgeColumn_coeff_lt_two (y : Fin m → K) (c : Fin 2 → K)
    (p : NewIncidence Q) (b k : Fin 2) (d : ℕ) (hd : d < 2) :
    (movingEvaluation y c (edgeColumn Q p b k)).coeff d = 0 := by
  have hf : edgeColumn Q p b k = X (Fin.natAdd m b) * (X (Fin.natAdd m p.val.2) *
      (C (Q.edgeLinear (crossSingleEdge Q p) k) * X (Fin.castAdd 2 p.val.1))) := by
    unfold edgeColumn
    ring
  rw [hf, movingEvaluation_Xnew_Xnew]
  simp [Polynomial.coeff_X_pow_mul', not_le_of_gt hd]

/-- A motion column has both new-coordinate factors. -/
theorem movingEvaluation_motionColumn_coeff_lt_two (y : Fin m → K) (c : Fin 2 → K)
    (q : Fin 3) (k : Fin 2) (d : ℕ) (hd : d < 2) :
    (movingEvaluation y c (motionColumn Q q k)).coeff d = 0 := by
  unfold motionColumn
  rw [mul_assoc, movingEvaluation_Xnew_Xnew]
  simp [Polynomial.coeff_X_pow_mul', not_le_of_gt hd]

/-- The constant and first-order evaluations of every higher column vanish at a moving probe. -/
theorem movingEvaluation_higherPolynomial_coeff_lt_two (y : Fin m → K) (c : Fin 2 → K)
    (a : HigherColumn Q) (k : Fin 2) (d : ℕ) (hd : d < 2) :
    (movingEvaluation y c (higherPolynomial Q a k)).coeff d = 0 := by
  rcases a with ⟨p, b⟩ | q
  · exact movingEvaluation_edgeColumn_coeff_lt_two Q y c p b k d hd
  · exact movingEvaluation_motionColumn_coeff_lt_two Q y c q k d hd

@[simp] theorem movingEvaluation_higherPolynomial_coeff_zero (y : Fin m → K) (c : Fin 2 → K)
    (a : HigherColumn Q) (k : Fin 2) : (movingEvaluation y c (higherPolynomial Q a k)).coeff 0 = 0 :=
  movingEvaluation_higherPolynomial_coeff_lt_two Q y c a k 0 (by decide)

@[simp] theorem movingEvaluation_higherPolynomial_coeff_one (y : Fin m → K) (c : Fin 2 → K)
    (a : HigherColumn Q) (k : Fin 2) : (movingEvaluation y c (higherPolynomial Q a k)).coeff 1 = 0 :=
  movingEvaluation_higherPolynomial_coeff_lt_two Q y c a k 1 (by decide)

section B5

variable (a : ℕ) (R : Parameters K ((10 + 2 * a) + 2)) (hs : R.single = B5.single)

include hs

/-- The two new vertices have disjoint old neighbors in the B.5 pattern. -/
theorem b5_oldEndpoint_injective : Function.Injective (fun p : NewIncidence R => p.val.1) := by
  rintro ⟨⟨i, b⟩, hb⟩ ⟨⟨j, c⟩, hc⟩ hij
  change i = j at hij
  subst j
  have hb' : B5.singleLabels i.val (10 + 2 * a + b.val) := by
    rw [hs] at hb
    exact (B5.single_eq_true _).mp hb
  have hc' : B5.singleLabels i.val (10 + 2 * a + c.val) := by
    rw [hs] at hc
    exact (B5.single_eq_true _).mp hc
  have hbc : b = c := by
    fin_cases b <;> fin_cases c
    · rfl
    · change B5.singleLabels i.val (10 + 2 * a) at hb'
      change B5.singleLabels i.val (10 + 2 * a + 1) at hc'
      exfalso
      unfold B5.singleLabels at hb' hc'
      omega
    · change B5.singleLabels i.val (10 + 2 * a + 1) at hb'
      change B5.singleLabels i.val (10 + 2 * a) at hc'
      exfalso
      unfold B5.singleLabels at hb' hc'
      omega
    · rfl
  exact Subtype.ext (congrArg (Prod.mk i) hbc)

/-- The edge joining the two newly added vertices is double in the B.5 graph. -/
theorem b5_newPair_double : R.single (newPairEdge (10 + 2 * a)) = false := by
  rw [hs]
  apply Bool.eq_false_of_not_eq_true
  intro he
  have h := (B5.single_eq_true _).mp he
  change B5.singleLabels (10 + 2 * a) (10 + 2 * a + 1) at h
  rw [show 10 + 2 * a + 1 = 11 + 2 * a by omega] at h
  exact B5.same_pair_double a h

end B5

section NormalizedC4

/-- The chart `s'=s+2t`, `t'=t` normalizes a C.4 direction to `(1,τ)`. -/
private def c4Chart (σ : Fin 2 → ℚ) (μ : ℚ) : ℚ × ℚ :=
  (σ 1 / (σ 0 + 2 * σ 1), μ / (σ 0 + 2 * σ 1))

private def c4VertexData (i : Fin 3) (d : Fin 2) : ℚ × ℚ :=
  if i = 0 then ![((0 : ℚ), (1 : ℚ)), (1, 1)] d
  else if i = 1 then c4Chart (cubicUDirections (Fin.castAdd 3 d)) (cubicUHeights (Fin.castAdd 3 d))
  else c4Chart (cubicVDirections (Fin.castAdd 4 d)) (cubicVHeights (Fin.castAdd 4 d))

private def c4Single (e : Edge 3) : Bool := e.val.1 == 0 && e.val.2 == 1

private def c4EdgeData (e : Edge 3) (d : Fin 2) : ℚ × ℚ :=
  if e.val.1 = 0 then
    if e.val.2 = 1 then c4Chart (cubicUDirections 2) (cubicUHeights 2)
    else c4Chart (cubicVDirections (![2, 3] d)) (cubicVHeights (![2, 3] d))
  else c4Chart (cubicUDirections (Fin.natAdd 3 d)) (cubicUHeights (Fin.natAdd 3 d))

/-- The C.4 cone data in the slope chart, with arbitrary admissible vertex data at `x`. -/
def normalizedC4Parameters : Parameters ℚ (1 + 2) where
  single := c4Single
  vertexSlope i d := (c4VertexData i d).1
  vertexHeight i d := (c4VertexData i d).2
  edgeSlope e d := (c4EdgeData e d).1
  edgeHeight e d := (c4EdgeData e d).2
  edgeLambda _ := 1
  vertexSlope_ne := by decide +kernel
  vertexHeight_ne := by decide +kernel
  edgeSlope_ne := by decide +kernel
  edgeHeight_ne := by decide +kernel
  edgeLambda_ne := by decide +kernel

/-- The unpaired single incidence at `xu`. -/
def normalizedC4Incidence : NewIncidence (m := 1) normalizedC4Parameters :=
  ⟨(0, 0), by decide +kernel⟩

/-- The two final probe points from Appendix C.4. -/
def c4Probes : Fin 2 → Fin 3 → ℚ := ![![1, 1, 1], ![1, 2, 3]]

/-- The exact C.4 block after normalizing the chart and imposing the graph's zero-`t` gauge. -/
def normalizedC4Block : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2 / 5, 49 / 30, 4 / 5, 1 / 3;
    -1, -31 / 15, -11 / 10, -29 / 60;
    12 / 5, 163 / 10, 103 / 10, 9 / 2;
    -6, -309 / 10, -231 / 10, -119 / 10]

private theorem normalizedC4_entries : ∀ r c,
    finalProbeMatrix normalizedC4Parameters normalizedC4Incidence c4Probes r c = normalizedC4Block r c := by
  intro r c
  fin_cases r <;> fin_cases c <;> decide +kernel

/-- The exact block is the evaluation of the actual normalized graph lifts. -/
theorem normalizedC4Matrix_eq :
    finalProbeMatrix normalizedC4Parameters normalizedC4Incidence c4Probes = normalizedC4Block := by
  ext r c
  exact normalizedC4_entries r c

theorem normalizedC4Block_det : normalizedC4Block.det = -(603 : ℚ) / 200 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [normalizedC4Block, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]

/-- The normalized C.4 block gives a nonsingular witness in the actual graph gauge. -/
theorem normalizedC4Matrix_det_ne_zero :
    (finalProbeMatrix normalizedC4Parameters normalizedC4Incidence c4Probes).det ≠ 0 := by
  rw [normalizedC4Matrix_eq, normalizedC4Block_det]
  norm_num

end NormalizedC4


open CubicMixedLocality

private theorem finalCoordinate_strictMono {m : ℕ} (i : Fin m) : StrictMono (finalCoordinate i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [finalCoordinate, Fin.lt_def] at hab ⊢

/-- The final probe's three local coordinates embed increasingly into the ambient trace space. -/
def finalEmbedding {m : ℕ} (i : Fin m) : Fin 3 ↪ Fin (m + 2) :=
  ⟨finalCoordinate i, (finalCoordinate_strictMono i).injective⟩

theorem finalEmbedding_strictMono {m : ℕ} (i : Fin m) : StrictMono (finalEmbedding i) :=
  finalCoordinate_strictMono i

private theorem finalCoordinate_local (j : Fin 3) : finalCoordinate (0 : Fin 1) j = j := by
  fin_cases j <;> rfl

/-- Agreement at the two new lift centers transports the C.4 block to ambient probes.
The vertex parameters of the unpaired old vertex do not enter this comparison. -/
theorem finalColumnValue_eq_localC4 {m : ℕ} (Q : Parameters ℚ (m + 2))
    (p : NewIncidence Q) (hdir : p.val.2 = 0)
    (hu : AgreesAt normalizedC4Parameters Q (finalEmbedding p.val.1)
      (finalEmbedding_strictMono p.val.1) 1)
    (hv : AgreesAt normalizedC4Parameters Q (finalEmbedding p.val.1)
      (finalEmbedding_strictMono p.val.1) 2)
    (x : Fin 3 → ℚ) (c : Fin 4) (k : Fin 2) :
    finalColumnValue Q p x c k = finalColumnValue normalizedC4Parameters normalizedC4Incidence x c k := by
  have hmap : edgeImage (finalEmbedding p.val.1) (finalEmbedding_strictMono p.val.1)
      (crossEdge (0 : Fin 1) 0) = crossEdge p.val.1 p.val.2 := by
    rw [hdir]
    rfl
  have hSlope : normalizedC4Parameters.edgeSlope (crossEdge (0 : Fin 1) 0) =
      Q.edgeSlope (crossEdge p.val.1 p.val.2) := by
    have hs := (hu.edge_eq (crossEdge (0 : Fin 1) 0) (Or.inr rfl)).2.2.1
    simpa only [hmap] using hs
  have hU (q : Fin 3) (j : Fin 3) (l : Fin 2) :
      normalizedC4Parameters.mixedLinear (Fin.natAdd 1 0) (basisQuadratic q)
          (finalCoordinate (0 : Fin 1) j) l =
        Q.mixedLinear (Fin.natAdd m 0) (basisQuadratic q) (finalCoordinate p.val.1 j) l := by
    rw [finalCoordinate_local]
    exact congrFun (mixedLinear_eq_of_agreesAt hu (basisQuadratic q) j) l
  have hV (q : Fin 3) (j : Fin 3) (l : Fin 2) :
      normalizedC4Parameters.mixedLinear (Fin.natAdd 1 1) (basisQuadratic q)
          (finalCoordinate (0 : Fin 1) j) l =
        Q.mixedLinear (Fin.natAdd m 1) (basisQuadratic q) (finalCoordinate p.val.1 j) l := by
    rw [finalCoordinate_local]
    exact congrFun (mixedLinear_eq_of_agreesAt hv (basisQuadratic q) j) l
  have hCross : crossValue Q p (finalProbe p.val.1 x) k =
      crossValue normalizedC4Parameters normalizedC4Incidence (finalProbe normalizedC4Incidence.val.1 x) k := by
    rw [crossValue_finalProbe, crossValue_finalProbe]
    change ![Q.edgeSlope (crossEdge p.val.1 p.val.2) 0, -1] k * x 0 * x 1 * x 2 =
      ![normalizedC4Parameters.edgeSlope (crossEdge (0 : Fin 1) 0) 0, -1] k * x 0 * x 1 * x 2
    rw [hSlope]
  have hMotion (q : Fin 3) : motionValue Q q (finalProbe p.val.1 x) k =
      motionValue normalizedC4Parameters q (finalProbe (0 : Fin 1) x) k := by
    rw [motionValue_finalProbe, motionValue_finalProbe]
    simp only [hU, hV]
  fin_cases c
  · exact hCross
  · exact hMotion 0
  · exact hMotion 1
  · exact hMotion 2

/-- The normalized witness gives a nonsingular ambient final block whenever the two local lifts agree. -/
theorem finalProbeMatrix_det_ne_zero_of_agreesAt {m : ℕ} (Q : Parameters ℚ (m + 2))
    (p : NewIncidence Q) (hdir : p.val.2 = 0)
    (hu : AgreesAt normalizedC4Parameters Q (finalEmbedding p.val.1)
      (finalEmbedding_strictMono p.val.1) 1)
    (hv : AgreesAt normalizedC4Parameters Q (finalEmbedding p.val.1)
      (finalEmbedding_strictMono p.val.1) 2) :
    (finalProbeMatrix Q p c4Probes).det ≠ 0 := by
  have heq : finalProbeMatrix Q p c4Probes =
      finalProbeMatrix normalizedC4Parameters normalizedC4Incidence c4Probes := by
    ext r c
    exact finalColumnValue_eq_localC4 Q p hdir hu hv _ c _
  rw [heq]
  exact normalizedC4Matrix_det_ne_zero


section Assembled

variable {r : ℕ}


/-- Fixed higher rows are single-edge scalars or components at free probes. -/
abbrev HigherFixedRow (Q : Parameters K (m + 2)) := NewIncidence Q ⊕ ((Fin (m + 2) → K) × Fin 2)

/-- The literal fixed-row evaluation of a higher column. -/
def higherFixedValue (row : HigherFixedRow Q) (a : HigherColumn Q) : K :=
  match row with
  | .inl p => -eval (edgeRow Q p) (higherPolynomial Q a 1)
  | .inr (y, k) => eval y (higherPolynomial Q a k)

/-- This fixed value is the corresponding component of the actual parameter's `Φ` column. -/
theorem higherFixedValue_parameterPhi {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (row : HigherFixedRow Q) (a : HigherColumn Q) :
    higherFixedValue Q row a = match row with
    | .inl p => -eval (edgeRow Q p) (Q.parameterPhi free h₂ h₆ (highParameter Q a) 1).val
    | .inr (y, k) => eval y (Q.parameterPhi free h₂ h₆ (highParameter Q a) k).val := by
  rcases row with p | ⟨y, k⟩ <;> simp [higherFixedValue, higherPolynomial_parameterPhi]

private theorem higherFixedValue_edge (p : NewIncidence Q) (a : HigherColumn Q) :
    higherFixedValue Q (.inl p) a =
      if a = .inl (p, p.val.2) then (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 else 0 := by
  rcases a with ⟨s, b⟩ | q
  · simp only [higherFixedValue, higherPolynomial, eval_edgeColumn, edgeValue_edgeRow,
      Sum.inl.injEq, Prod.mk.injEq]
    split_ifs <;> simp [Parameters.edgeLinear]
  · simp [higherFixedValue, higherPolynomial, motionValue_edgeRow]

variable (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)

/-- The two cross incidences assigned to a paired probe. -/
def pairedIncidence (i : Fin r) (b : Fin 2) : NewIncidence Q := pairing (.inl (i, b))

/-- The unpaired cross incidence handled by the final four rows. -/
def unpairedIncidence : NewIncidence Q := pairing (.inr ())

/-- The higher column labels of the final block in C.4 order. -/
def finalHigherLabel : Fin 4 → HigherColumn Q :=
  ![.inl (unpairedIncidence Q pairing, (unpairedIncidence Q pairing).val.2.rev),
    .inr 0, .inr 1, .inr 2]

private def finalFixedRow (x : Fin 2 → Fin 3 → K) (j : Fin 4) : HigherFixedRow Q :=
  .inr (finalProbe (unpairedIncidence Q pairing).val.1 (x ⟨j.val / 2, by omega⟩),
    ⟨j.val % 2, by omega⟩)

/-- Index the fixed rows by higher columns. Same-direction labels are single-edge rows,
paired cross labels are two-component probes, and the last labels give the C.4 rows. -/
def fixedProbeRow (x : Fin 2 → Fin 3 → K) : HigherColumn Q → HigherFixedRow Q
  | .inl (p, b) => if b = p.val.2 then .inl p else
    match pairing.symm p with
    | .inl (i, k) => .inr (pairProbe (pairedIncidence Q pairing i 0).val.1
        (pairedIncidence Q pairing i 1).val.1, k)
    | .inr _ => finalFixedRow Q pairing x 0
  | .inr q => finalFixedRow Q pairing x q.succ

private theorem rev_ne_self_two : ∀ b : Fin 2, b.rev ≠ b := by decide +kernel

private theorem eq_or_eq_rev_two : ∀ b d : Fin 2, b = d ∨ b = d.rev := by decide +kernel

@[simp] theorem fixedProbeRow_same (x : Fin 2 → Fin 3 → K) (p : NewIncidence Q) :
    fixedProbeRow Q pairing x (.inl (p, p.val.2)) = .inl p := by
  simp [fixedProbeRow]

private theorem fixedProbeRow_pair (x : Fin 2 → Fin 3 → K) (i : Fin r) (k : Fin 2) :
    fixedProbeRow Q pairing x (.inl (pairedIncidence Q pairing i k,
      (pairedIncidence Q pairing i k).val.2.rev)) =
      .inr (pairProbe (pairedIncidence Q pairing i 0).val.1 (pairedIncidence Q pairing i 1).val.1, k) := by
  simp [fixedProbeRow, pairedIncidence, rev_ne_self_two]

private theorem fixedProbeRow_final (x : Fin 2 → Fin 3 → K) (j : Fin 4) :
    fixedProbeRow Q pairing x (finalHigherLabel Q pairing j) = finalFixedRow Q pairing x j := by
  refine Fin.cases ?_ (fun q => ?_) j
  · simp [fixedProbeRow, finalHigherLabel, unpairedIncidence, rev_ne_self_two]
  · fin_cases q <;> rfl

/-- The square B.22 matrix with the paired and final fixed probe rows. -/
def fixedHigherMatrix (x : Fin 2 → Fin 3 → K) : Matrix (HigherColumn Q) (HigherColumn Q) K :=
  Matrix.of fun i j => higherFixedValue Q (fixedProbeRow Q pairing x i) j

private theorem sum_higherFixedValue_free (a : HigherColumn Q → K)
    (hsame : ∀ p, a (.inl (p, p.val.2)) = 0) (y : Fin (m + 2) → K) (k : Fin 2) :
    (∑ c, higherFixedValue Q (.inr (y, k)) c * a c) =
      (∑ p, crossValue Q p y k * a (.inl (p, p.val.2.rev))) +
        ∑ q, motionValue Q q y k * a (.inr q) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [higherFixedValue, higherPolynomial, eval_edgeColumn, eval_motionColumn]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Fin.sum_univ_two]
  by_cases h : p.val.2 = 0
  · have hp : a (.inl (p, 0)) = 0 := by simpa only [h] using hsame p
    simp [crossValue, h, hp, Fin.rev]
  · have h' : p.val.2 = 1 := Fin.eq_one_of_ne_zero _ h
    have hp : a (.inl (p, 1)) = 0 := by simpa only [h'] using hsame p
    simp [crossValue, h', hp, Fin.rev]

private theorem pairedIncidence_ne (i : Fin r) :
    pairedIncidence Q pairing i 0 ≠ pairedIncidence Q pairing i 1 := by
  intro h
  have he := pairing.injective h
  simp at he

/-- Same-direction pivots, the final block, and the paired normal lines force every
coefficient in the kernel of the assembled B.22 matrix to vanish. -/
theorem fixedHigherMatrix_eq_zero_of_mulVec_eq_zero (x : Fin 2 → Fin 3 → K)
    (hinj : Function.Injective (fun p : NewIncidence Q => p.val.1))
    (hslopes : ∀ i,
      Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 0)).val 0 ≠
        Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 1)).val 0)
    (hfinal : (finalProbeMatrix Q (unpairedIncidence Q pairing) x).det ≠ 0)
    (a : HigherColumn Q → K) (ha : (fixedHigherMatrix Q pairing x).mulVec a = 0) : a = 0 := by
  classical
  have hrow (i : HigherColumn Q) :
      (∑ c, higherFixedValue Q (fixedProbeRow Q pairing x i) c * a c) = 0 := congrFun ha i
  have hsame (p : NewIncidence Q) : a (.inl (p, p.val.2)) = 0 := by
    have hp : (Q.edgeLambda (crossEdge p.val.1 p.val.2)) ^ 2 * a (.inl (p, p.val.2)) = 0 := by
      simpa [higherFixedValue_edge, ite_mul] using hrow (.inl (p, p.val.2))
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ (Q.edgeLambda_ne _))
  let p := unpairedIncidence Q pairing
  have hlast : (finalProbeMatrix Q p x).mulVec (a ∘ finalHigherLabel Q pairing) = 0 := by
    funext j
    have hj := hrow (finalHigherLabel Q pairing j)
    rw [fixedProbeRow_final] at hj
    let z := x ⟨j.val / 2, by omega⟩
    let k : Fin 2 := ⟨j.val % 2, by omega⟩
    change (∑ c, higherFixedValue Q (.inr (finalProbe p.val.1 z, k)) c * a c) = 0 at hj
    rw [sum_higherFixedValue_free Q a hsame] at hj
    rw [Finset.sum_eq_single p] at hj
    · change (∑ c, finalColumnValue Q p z c k * a (finalHigherLabel Q pairing c)) = 0
      rw [Fin.sum_univ_four]
      rw [Fin.sum_univ_three] at hj
      simpa [finalColumnValue, finalHigherLabel, p, add_assoc] using hj
    · intro s _ hs
      rw [crossValue_finalProbe_off Q s p.val.1 z (fun h => hs (hinj h)) k, zero_mul]
    · simp
  have hlastZero := Matrix.eq_zero_of_mulVec_eq_zero hfinal hlast
  have hunpaired : a (.inl (p, p.val.2.rev)) = 0 := congrFun hlastZero 0
  have hmotion (q : Fin 3) : a (.inr q) = 0 := by
    fin_cases q
    · exact congrFun hlastZero (1 : Fin 4)
    · exact congrFun hlastZero (2 : Fin 4)
    · exact congrFun hlastZero (3 : Fin 4)
  have hpaired (i : Fin r) (k : Fin 2) :
      a (.inl (pairedIncidence Q pairing i k, (pairedIncidence Q pairing i k).val.2.rev)) = 0 := by
    let p₀ := pairedIncidence Q pairing i 0
    let p₁ := pairedIncidence Q pairing i 1
    have hp : p₀ ≠ p₁ := pairedIncidence_ne Q pairing i
    let z : Fin 2 → K := fun b => a (.inl (pairedIncidence Q pairing i b,
      (pairedIncidence Q pairing i b).val.2.rev))
    have hv : (pairProbeMatrix Q p₀ p₁).mulVec z = 0 := by
      funext b
      have hb := hrow (.inl (pairedIncidence Q pairing i b, (pairedIncidence Q pairing i b).val.2.rev))
      rw [fixedProbeRow_pair, sum_higherFixedValue_free Q a hsame] at hb
      simp only [hmotion, mul_zero, Finset.sum_const_zero, add_zero] at hb
      rw [Finset.sum_eq_add_of_mem p₀ p₁ (Finset.mem_univ _) (Finset.mem_univ _) hp] at hb
      · change (∑ c, crossValue Q (![p₀, p₁] c) (pairProbe p₀.val.1 p₁.val.1) b * z c) = 0
        rw [Fin.sum_univ_two]
        simpa [z, p₀, p₁] using hb
      · intro s _ hs
        rw [crossValue_pairProbe_other Q p₀ p₁ s hinj hs.1 hs.2, zero_mul]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero
      (pairProbeMatrix_det_ne_zero Q p₀ p₁ (fun h => hp (hinj h)) (hslopes i)) hv
    exact congrFun hz k
  funext c
  rcases c with ⟨s, b⟩ | q
  · rcases eq_or_eq_rev_two b s.val.2 with rfl | rfl
    · exact hsame s
    · obtain ⟨label, rfl⟩ := pairing.surjective s
      rcases label with ⟨i, k⟩ | ⟨⟩
      · exact hpaired i k
      · exact hunpaired
  · exact hmotion q

/-- The assembled fixed higher block is nonsingular. -/
theorem fixedHigherMatrix_det_ne_zero (x : Fin 2 → Fin 3 → K)
    (hinj : Function.Injective (fun p : NewIncidence Q => p.val.1))
    (hslopes : ∀ i,
      Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 0)).val 0 ≠
        Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 1)).val 0)
    (hfinal : (finalProbeMatrix Q (unpairedIncidence Q pairing) x).det ≠ 0) :
    (fixedHigherMatrix Q pairing x).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro a b hab
  apply sub_eq_zero.mp
  apply fixedHigherMatrix_eq_zero_of_mulVec_eq_zero Q pairing x hinj hslopes hfinal
  rw [Matrix.mulVec_sub, hab, sub_self]

/-- Nonsingularity holds for the fixed rows of the actual independent parameter columns. -/
theorem actualFixedHigherMatrix_det_ne_zero {f : ℕ} (free : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (x : Fin 2 → Fin 3 → K)
    (hinj : Function.Injective (fun p : NewIncidence Q => p.val.1))
    (hslopes : ∀ i,
      Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 0)).val 0 ≠
        Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 1)).val 0)
    (hfinal : (finalProbeMatrix Q (unpairedIncidence Q pairing) x).det ≠ 0) :
    (Matrix.of (fun i j => match fixedProbeRow Q pairing x i with
      | .inl p => -eval (edgeRow Q p) (Q.parameterPhi free h₂ h₆ (highParameter Q j) 1).val
      | .inr (y, k) => eval y (Q.parameterPhi free h₂ h₆ (highParameter Q j) k).val) :
      Matrix (HigherColumn Q) (HigherColumn Q) K).det ≠ 0 := by
  have heq : (Matrix.of (fun i j => match fixedProbeRow Q pairing x i with
      | .inl p => -eval (edgeRow Q p) (Q.parameterPhi free h₂ h₆ (highParameter Q j) 1).val
      | .inr (y, k) => eval y (Q.parameterPhi free h₂ h₆ (highParameter Q j) k).val) :
      Matrix (HigherColumn Q) (HigherColumn Q) K) = fixedHigherMatrix Q pairing x := by
    ext i j
    exact (higherFixedValue_parameterPhi Q free h₂ h₆ (fixedProbeRow Q pairing x i) j).symm
  rw [heq]
  exact fixedHigherMatrix_det_ne_zero Q pairing x hinj hslopes hfinal


end Assembled


/-- An odd finite label set can be paired with any prescribed unpaired label. -/
theorem exists_pairing_at {I : Type*} [Fintype I] (p : I) (r : ℕ)
    (hc : Fintype.card I = 2 * r + 1) :
    ∃ e : ((Fin r × Fin 2) ⊕ Unit) ≃ I, e (.inr ()) = p := by
  classical
  let e₂ : Unit ≃ {x : I // ¬ x ≠ p} :=
    { toFun := fun _ => ⟨p, by simp⟩
      invFun := fun _ => ()
      left_inv := fun u => by cases u; rfl
      right_inv := fun u => Subtype.ext (Classical.not_not.mp u.property).symm }
  have hc' : Fintype.card {x : I // x ≠ p} = 2 * r := by
    have h := Fintype.card_congr (Equiv.sumCompl (fun x : I => x ≠ p))
    rw [Fintype.card_sum, ← Fintype.card_congr e₂, Fintype.card_unit, hc] at h
    omega
  let e₁ : (Fin r × Fin 2) ≃ {x : I // x ≠ p} := Fintype.equivOfCardEq (by
    simp [hc', Nat.mul_comm])
  exact ⟨(Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (fun x : I => x ≠ p)), rfl⟩

/-- The prescribed unpaired incidence is the single edge from old vertex `1` to the first new vertex. -/
def b5_unpairedIncidence (a : ℕ) (Q : Parameters K ((10 + 2 * a) + 2)) (hQ : Q.single = B5.single) :
    NewIncidence Q :=
  ⟨(⟨1, by omega⟩, 0), by
    rw [hQ]
    apply (B5.single_eq_true _).mpr
    change B5.singleLabels 1 (10 + 2 * a)
    unfold B5.singleLabels
    omega⟩

/-- The B.5 step has an odd number of new incidences, with `a+3` pairs after one is reserved. -/
theorem b5_card_newIncidence (a : ℕ) (P : Parameters K (10 + 2 * a))
    (Q : Parameters K ((10 + 2 * a) + 2)) (h : Compatible P Q)
    (hP : P.single = B5.single) (hQ : Q.single = B5.single) :
    Fintype.card (NewIncidence Q) = 2 * (a + 3) + 1 := by
  rw [h.card_newIncidence (b5_newPair_double a Q hQ), B5.card_singleEdges a P hP]
  have hq : Fintype.card Q.SingleEdge = (a + 1) * (a + 1) + 6 * (a + 1) + 2 :=
    B5.card_singleEdges (a + 1) Q hQ
  rw [hq]
  have he : (a + 1) * (a + 1) + 6 * (a + 1) + 2 =
      (a * a + 6 * a + 2) + (2 * (a + 3) + 1) := by ring
  omega

/-- Pair the remaining B.5 incidences after reserving the prescribed first-root incidence. -/
theorem b5_exists_pairing (a : ℕ) (P : Parameters K (10 + 2 * a))
    (Q : Parameters K ((10 + 2 * a) + 2)) (h : Compatible P Q)
    (hP : P.single = B5.single) (hQ : Q.single = B5.single) :
    ∃ e : ((Fin (a + 3) × Fin 2) ⊕ Unit) ≃ NewIncidence Q,
      e (.inr ()) = b5_unpairedIncidence a Q hQ :=
  exists_pairing_at (b5_unpairedIncidence a Q hQ) (a + 3) (b5_card_newIncidence a P Q h hP hQ)



open CubicMixedLocality

/-- The old vertex retained for the final C.4 probe in B.5. -/
def firstRoot (a : ℕ) : Fin (10 + 2 * a) := ⟨1, by omega⟩

private theorem c4_single_cross (a : ℕ) (b : Fin 2) :
    B5.single (crossEdge (firstRoot a) b) = normalizedC4Parameters.single (crossEdge (0 : Fin 1) b) := by
  fin_cases b
  · change B5.single (crossEdge (firstRoot a) 0) = true
    apply (B5.single_eq_true _).mpr
    change B5.singleLabels 1 (10 + 2 * a)
    unfold B5.singleLabels
    omega
  · change B5.single (crossEdge (firstRoot a) 1) = false
    apply Bool.eq_false_of_not_eq_true
    intro h
    have hh := (B5.single_eq_true _).mp h
    change B5.singleLabels 1 (10 + 2 * a + 1) at hh
    unfold B5.singleLabels at hh
    omega

private theorem c4_single_pair (a : ℕ) :
    B5.single (newPairEdge (10 + 2 * a)) = normalizedC4Parameters.single (newPairEdge 1) := by
  change B5.single (newPairEdge (10 + 2 * a)) = false
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hh := (B5.single_eq_true _).mp h
  change B5.singleLabels (10 + 2 * a) (10 + 2 * a + 1) at hh
  rw [show 10 + 2 * a + 1 = 11 + 2 * a by omega] at hh
  exact B5.same_pair_double a hh

private def c4ExtensionEdgeData (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (e : Edge ((10 + 2 * a) + 2)) : (Fin 2 → ℚ) × (Fin 2 → ℚ) × ℚ :=
  match edgeExtensionEquiv (10 + 2 * a) e with
  | .inl e => (P.edgeSlope e, P.edgeHeight e, P.edgeLambda e)
  | .inr (.inl (i, b)) =>
    if i = firstRoot a then
      (normalizedC4Parameters.edgeSlope (crossEdge (0 : Fin 1) b),
        normalizedC4Parameters.edgeHeight (crossEdge (0 : Fin 1) b), 1)
    else (fun d => (i.val : ℚ) + (d.val : ℚ), 1, 1)
  | .inr (.inr _) =>
    (normalizedC4Parameters.edgeSlope (newPairEdge 1),
      normalizedC4Parameters.edgeHeight (newPairEdge 1), 1)

private theorem c4ExtensionEdgeData_ok (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) (e : Edge ((10 + 2 * a) + 2)) :
    (B5.single e = false → (c4ExtensionEdgeData a P e).1 0 ≠ (c4ExtensionEdgeData a P e).1 1) ∧
      (∀ d, (c4ExtensionEdgeData a P e).2.1 d ≠ 0) ∧ (c4ExtensionEdgeData a P e).2.2 ≠ 0 := by
  obtain ⟨label, rfl⟩ := (edgeExtensionEquiv (10 + 2 * a)).symm.surjective e
  rcases label with e | (⟨i, b⟩ | u)
  · have hs : B5.single (oldEdge (10 + 2 * a) e) = P.single e := (congrFun hP e).symm
    simpa [c4ExtensionEdgeData, hs] using
      And.intro (P.edgeSlope_ne e) (And.intro (P.edgeHeight_ne e) (P.edgeLambda_ne e))
  · by_cases hi : i = firstRoot a
    · subst i
      simpa [c4ExtensionEdgeData, c4_single_cross a b] using
        And.intro (normalizedC4Parameters.edgeSlope_ne (crossEdge (0 : Fin 1) b))
          (And.intro (normalizedC4Parameters.edgeHeight_ne (crossEdge (0 : Fin 1) b))
            (show (1 : ℚ) ≠ 0 by norm_num))
    · exact ⟨fun _ => by simp [c4ExtensionEdgeData, hi],
        by simp [c4ExtensionEdgeData, hi], by simp [c4ExtensionEdgeData, hi]⟩
  · cases u
    simpa [c4ExtensionEdgeData, c4_single_pair a] using
      And.intro (normalizedC4Parameters.edgeSlope_ne (newPairEdge 1))
        (And.intro (normalizedC4Parameters.edgeHeight_ne (newPairEdge 1))
          (show (1 : ℚ) ≠ 0 by norm_num))

/-- Extend any old rational B.5 parameters by the normalized C.4 data and
use distinct old-index slopes for every other new incidence. -/
def c4ExtensionParameters (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) : Parameters ℚ ((10 + 2 * a) + 2) where
  single := B5.single
  vertexSlope := Fin.addCases P.vertexSlope (fun b => normalizedC4Parameters.vertexSlope (Fin.natAdd 1 b))
  vertexHeight := Fin.addCases P.vertexHeight (fun b => normalizedC4Parameters.vertexHeight (Fin.natAdd 1 b))
  edgeSlope e := (c4ExtensionEdgeData a P e).1
  edgeHeight e := (c4ExtensionEdgeData a P e).2.1
  edgeLambda e := (c4ExtensionEdgeData a P e).2.2
  vertexSlope_ne i := by
    refine Fin.addCases (fun j => ?_) (fun b => ?_) i
    · simpa using P.vertexSlope_ne j
    · simpa using normalizedC4Parameters.vertexSlope_ne (Fin.natAdd 1 b)
  vertexHeight_ne i d := by
    refine Fin.addCases (fun j => ?_) (fun b => ?_) i
    · simpa using P.vertexHeight_ne j d
    · simpa using normalizedC4Parameters.vertexHeight_ne (Fin.natAdd 1 b) d
  edgeSlope_ne e := (c4ExtensionEdgeData_ok a P hP e).1
  edgeHeight_ne e := (c4ExtensionEdgeData_ok a P hP e).2.1
  edgeLambda_ne e := (c4ExtensionEdgeData_ok a P hP e).2.2

/-- The rational C.4 extension preserves all old parameters. -/
theorem c4Extension_compatible (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) : Compatible P (c4ExtensionParameters a P hP) where
  single_eq e := (congrFun hP e).symm
  vertexSlope_eq i d := by simp [c4ExtensionParameters]
  vertexHeight_eq i d := by simp [c4ExtensionParameters]
  edgeSlope_eq e d := by simp [c4ExtensionParameters, c4ExtensionEdgeData]
  edgeHeight_eq e d := by simp [c4ExtensionParameters, c4ExtensionEdgeData]
  edgeLambda_eq e := by simp [c4ExtensionParameters, c4ExtensionEdgeData]

private theorem finalEmbedding_new {m : ℕ} (i : Fin m) (b : Fin 2) :
    finalEmbedding i (Fin.natAdd 1 b) = Fin.natAdd m b := by fin_cases b <;> rfl

private theorem finalEmbedding_cross {m : ℕ} (i : Fin m) (b : Fin 2) :
    edgeImage (finalEmbedding i) (finalEmbedding_strictMono i) (crossEdge (0 : Fin 1) b) = crossEdge i b := by
  apply Subtype.ext
  exact Prod.ext rfl (finalEmbedding_new i b)

private theorem finalEmbedding_pair {m : ℕ} (i : Fin m) :
    edgeImage (finalEmbedding i) (finalEmbedding_strictMono i) (newPairEdge 1) = newPairEdge m := rfl

/-- The local C.4 cone data agree at both newly added centers. -/
theorem c4Extension_agreesAt (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) (b : Fin 2) :
    AgreesAt normalizedC4Parameters (c4ExtensionParameters a P hP) (finalEmbedding (firstRoot a))
      (finalEmbedding_strictMono (firstRoot a)) (Fin.natAdd 1 b) := by
  constructor
  · rw [finalEmbedding_new]
    simp [c4ExtensionParameters]
  · rw [finalEmbedding_new]
    simp [c4ExtensionParameters]
  · intro e _
    obtain ⟨label, rfl⟩ := (edgeExtensionEquiv 1).symm.surjective e
    rcases label with e | (⟨j, d⟩ | u)
    · exfalso
      have hlt : e.val.1.val < e.val.2.val := e.property
      omega
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      simp only [edgeExtensionEquiv_symm_cross, finalEmbedding_cross]
      refine ⟨(c4_single_cross a d).symm, ?_, ?_, ?_⟩ <;>
        simp [c4ExtensionParameters, c4ExtensionEdgeData, normalizedC4Parameters]
    · cases u
      simp only [edgeExtensionEquiv_symm_pair, finalEmbedding_pair]
      refine ⟨(c4_single_pair a).symm, ?_, ?_, ?_⟩ <;>
        simp [c4ExtensionParameters, c4ExtensionEdgeData, normalizedC4Parameters]

private theorem c4Extension_crossSlope_of_ne (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) (i : Fin (10 + 2 * a)) (b : Fin 2) (hi : i ≠ firstRoot a) :
    (c4ExtensionParameters a P hP).edgeSlope (crossEdge i b) 0 = (i.val : ℚ) := by
  simp [c4ExtensionParameters, c4ExtensionEdgeData, hi]

/-- The B.5 higher block has a nonsingular rational witness extending arbitrary old parameters. -/
theorem exists_b5_fixedHigherWitness (a : ℕ) (P : Parameters ℚ (10 + 2 * a))
    (hP : P.single = B5.single) :
    ∃ (Q : Parameters ℚ ((10 + 2 * a) + 2))
      (pairing : ((Fin (a + 3) × Fin 2) ⊕ Unit) ≃ NewIncidence Q),
      Compatible P Q ∧ Q.single = B5.single ∧ (fixedHigherMatrix Q pairing c4Probes).det ≠ 0 := by
  let Q := c4ExtensionParameters a P hP
  have hQ : Q.single = B5.single := rfl
  have hcompat : Compatible P Q := c4Extension_compatible a P hP
  obtain ⟨pairing, hp⟩ := b5_exists_pairing a P Q hcompat hP hQ
  let p := unpairedIncidence Q pairing
  have hp₁ : p.val.1 = firstRoot a := congrArg (fun e : NewIncidence Q => e.val.1) hp
  have hp₂ : p.val.2 = 0 := congrArg (fun e : NewIncidence Q => e.val.2) hp
  have hinj := b5_oldEndpoint_injective a Q hQ
  have hslopes (i : Fin (a + 3)) :
      Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 0)).val 0 ≠
        Q.edgeSlope (crossSingleEdge Q (pairedIncidence Q pairing i 1)).val 0 := by
    have hroot (b : Fin 2) : (pairedIncidence Q pairing i b).val.1 ≠ firstRoot a := by
      intro he
      have hEq : pairedIncidence Q pairing i b = p := hinj (he.trans hp₁.symm)
      have hlabel : (Sum.inl (i, b) : (Fin (a + 3) × Fin 2) ⊕ Unit) = .inr () := pairing.injective hEq
      cases hlabel
    have hd : (pairedIncidence Q pairing i 0).val.1 ≠ (pairedIncidence Q pairing i 1).val.1 := by
      intro he
      have hlabel : (Sum.inl (i, (0 : Fin 2)) : (Fin (a + 3) × Fin 2) ⊕ Unit) = .inl (i, 1) :=
        pairing.injective (hinj he)
      simp at hlabel
    simp only [crossSingleEdge_val]
    change (c4ExtensionParameters a P hP).edgeSlope _ 0 ≠
      (c4ExtensionParameters a P hP).edgeSlope _ 0
    rw [c4Extension_crossSlope_of_ne a P hP _ _ (hroot 0),
      c4Extension_crossSlope_of_ne a P hP _ _ (hroot 1)]
    exact_mod_cast (fun h => hd (Fin.ext h) : (pairedIncidence Q pairing i 0).val.1.val ≠
      (pairedIncidence Q pairing i 1).val.1.val)
  have hfinal : (finalProbeMatrix Q p c4Probes).det ≠ 0 := by
    apply finalProbeMatrix_det_ne_zero_of_agreesAt Q p hp₂
    · rw [hp₁]
      have hu := c4Extension_agreesAt a P hP (0 : Fin 2)
      rw [show Fin.natAdd 1 (0 : Fin 2) = (1 : Fin 3) from by decide] at hu
      exact hu
    · rw [hp₁]
      have hv := c4Extension_agreesAt a P hP (1 : Fin 2)
      rw [show Fin.natAdd 1 (1 : Fin 2) = (2 : Fin 3) from by decide] at hv
      exact hv
  exact ⟨Q, pairing, hcompat, hQ, fixedHigherMatrix_det_ne_zero Q pairing c4Probes hinj hslopes hfinal⟩


end IdealGeneration.CubicSupported.B22
