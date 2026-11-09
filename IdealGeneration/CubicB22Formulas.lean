module

public import IdealGeneration.CubicB22Rows
public import IdealGeneration.CubicPrimitiveSplit
public import IdealGeneration.CubicIntegerSpecialization

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true


/-! Rational formulas and denominator clearing for the fixed B.22 block. -/

noncomputable section
namespace IdealGeneration.CubicSupported.B22

open CubicRationalFormula RationalChart

variable {σ : Type*} {m : ℕ}

/-- A higher column label with the incidence proof erased. -/
abbrev HigherFormulaColumn (m : ℕ) := ((Fin m × Fin 2) × Fin 2) ⊕ Fin 3

/-- A fixed row is the allowed scalar on a cross edge or a component at a formula point. -/
abbrev HigherFormulaRow (σ : Type*) (m : ℕ) :=
  (Fin m × Fin 2) ⊕ ((Fin (m + 2) → Formula σ) × Fin 2)

private def indicatorFormula (i j : Fin m) (z : Formula σ) : Formula σ := if j = i then z else 0

private def basisQuadraticFormula (q : Fin 3) (j : Fin 3) : Formula σ := if j = q then 1 else 0

/-- Formula coordinates of the marked trace representative of a cross edge. -/
def edgeRowFormula (a : PrimitiveIndex (m + 2) → Formula σ) (i : Fin m) (b : Fin 2) :
    Fin (m + 2) → Formula σ :=
  Fin.addCases (fun j => indicatorFormula i j 1)
    (fun k => indicatorFormula b k (a (.edgeLambda (crossEdge i b))))

/-- Formula coordinates of a probe at two old endpoints and both new vertices. -/
def pairProbeFormula (i j : Fin m) : Fin (m + 2) → Formula σ :=
  Fin.addCases (fun l => indicatorFormula i l 1 + indicatorFormula j l 1) (fun _ => 1)

/-- Formula coordinates of a probe at one old endpoint and both new vertices. -/
def finalProbeFormula (i : Fin m) (p : Fin 3 → Formula σ) : Fin (m + 2) → Formula σ :=
  Fin.addCases (fun l => indicatorFormula i l (p 0)) ![p 1, p 2]

/-- The higher edge or motion column at a point with formula coordinates. -/
def higherValueFormula (a : PrimitiveIndex (m + 2) → Formula σ) (single : Edge (m + 2) → Bool)
    (y : Fin (m + 2) → Formula σ) (k : Fin 2) : HigherFormulaColumn m → Formula σ
  | .inl ((i, d), b) =>
    ![a (.edgeSlope (crossEdge i d) 0), -1] k * y (Fin.castAdd 2 i) *
      y (Fin.natAdd m d) * y (Fin.natAdd m b)
  | .inr q =>
    let L (d : Fin 2) := Formula.sumFin (fun j =>
      mixedLinearFormula a single (Fin.natAdd m d) (basisQuadraticFormula q) j k * y j)
    y (Fin.natAdd m 0) * y (Fin.natAdd m 1) * (L 1 - L 0)

/-- The scalar sign in a single-edge row is the allowed coordinate `-t`. -/
def higherEntryFormula (a : PrimitiveIndex (m + 2) → Formula σ) (single : Edge (m + 2) → Bool)
    (row : HigherFormulaRow σ m) (col : HigherFormulaColumn m) : Formula σ :=
  match row with
  | .inl (i, b) => -higherValueFormula a single (edgeRowFormula a i b) 1 col
  | .inr (y, k) => higherValueFormula a single y k col

section Evaluation

variable {K : Type*} [Field K] (Q : Parameters K (m + 2)) (x : σ → K)

private theorem matchesZero : Formula.Matches x (0 : Formula σ) (0 : K) := by
  simpa using Formula.Matches.ofNat x 0

private theorem matchesOne : Formula.Matches x (1 : Formula σ) (1 : K) := by
  simpa using Formula.Matches.ofNat x 1

private theorem indicatorFormula_matches {z : Formula σ} {v : K} (h : Formula.Matches x z v)
    (i j : Fin m) : Formula.Matches x (indicatorFormula i j z) (vertexSupport i v j) := by
  by_cases hj : j = i
  · simpa [indicatorFormula, vertexSupport, hj] using h
  · simpa [indicatorFormula, vertexSupport, hj] using matchesZero x

private theorem basisQuadraticFormula_matches (q j : Fin 3) :
    Formula.Matches x (basisQuadraticFormula q j) (basisQuadratic q j : K) := by
  by_cases hj : j = q
  · simpa [basisQuadraticFormula, basisQuadratic, hj] using matchesOne x
  · simpa [basisQuadraticFormula, basisQuadratic, hj] using matchesZero x

theorem pairProbeFormula_matches (i j : Fin m) (l : Fin (m + 2)) :
    Formula.Matches x (pairProbeFormula i j l) (pairProbe i j l) := by
  refine Fin.addCases (fun l => ?_) (fun b => ?_) l
  · simpa only [pairProbeFormula, Fin.addCases_left, pairProbe_old] using
      (indicatorFormula_matches x (matchesOne x) i l).add
        (indicatorFormula_matches x (matchesOne x) j l)
  · simpa only [pairProbeFormula, Fin.addCases_right, pairProbe_new] using matchesOne x

theorem finalProbeFormula_matches (i : Fin m) {p : Fin 3 → Formula σ} {y : Fin 3 → K}
    (hp : ∀ l, Formula.Matches x (p l) (y l)) (l : Fin (m + 2)) :
    Formula.Matches x (finalProbeFormula i p l) (finalProbe i y l) := by
  refine Fin.addCases (fun l => ?_) (fun b => ?_) l
  · simpa only [finalProbeFormula, Fin.addCases_left, finalProbe_old] using
      indicatorFormula_matches x (hp 0) i l
  · rw [finalProbeFormula, Fin.addCases_right, finalProbe_new]
    fin_cases b
    · exact hp 1
    · exact hp 2

variable (a : PrimitiveIndex (m + 2) → Formula σ)
variable (ha : ∀ i, Formula.Matches x (a i) (primitiveValue Q i))

include ha in
theorem edgeRowFormula_matches (p : NewIncidence Q) (l : Fin (m + 2)) :
    Formula.Matches x (edgeRowFormula a p.val.1 p.val.2 l) (edgeRow Q p l) := by
  refine Fin.addCases (fun l => ?_) (fun b => ?_) l
  · simpa only [edgeRowFormula, Fin.addCases_left, edgeRow, edgeSupport_cross_old] using
      indicatorFormula_matches x (matchesOne x) p.val.1 l
  · simpa only [edgeRowFormula, Fin.addCases_right, edgeRow, edgeSupport_cross_new, one_mul, primitiveValue] using
      indicatorFormula_matches x (ha (.edgeLambda (crossEdge p.val.1 p.val.2))) p.val.2 b

/-- Erase a higher column label's dependence on chart admissibility proofs. -/
def higherFormulaColumnLabel : HigherColumn Q → HigherFormulaColumn m
  | .inl (p, b) => .inl (p.val, b)
  | .inr q => .inr q

include ha in
theorem higherValueFormula_matches {y : Fin (m + 2) → Formula σ} {v : Fin (m + 2) → K}
    (hy : ∀ j, Formula.Matches x (y j) (v j)) (k : Fin 2) (col : HigherColumn Q) :
    Formula.Matches x (higherValueFormula a Q.single y k (higherFormulaColumnLabel Q col))
      (MvPolynomial.eval v (higherPolynomial Q col k)) := by
  rcases col with ⟨p, b⟩ | q
  · have hk : Formula.Matches x (![a (.edgeSlope (crossEdge p.val.1 p.val.2) 0), -1] k)
          (Q.edgeLinear (crossSingleEdge Q p) k) := by
      fin_cases k
      · exact ha (.edgeSlope (crossEdge p.val.1 p.val.2) 0)
      · exact (matchesOne x).neg
    simpa only [higherFormulaColumnLabel, higherValueFormula, higherPolynomial, eval_edgeColumn,
      edgeValue] using
      ((hk.mul (hy (Fin.castAdd 2 p.val.1))).mul (hy (Fin.natAdd m p.val.2))).mul
        (hy (Fin.natAdd m b))
  · have hL (b : Fin 2) : Formula.Matches x
        (Formula.sumFin (fun j =>
          mixedLinearFormula a Q.single (Fin.natAdd m b) (basisQuadraticFormula q) j k * y j))
        (∑ j, Q.mixedLinear (Fin.natAdd m b) (basisQuadratic q) j k * v j) :=
      Formula.Matches.sumFin (fun j => (mixedLinearFormula_matches a x Q ha
        (basisQuadraticFormula_matches x q) (Fin.natAdd m b) j k).mul (hy j))
    simpa only [higherFormulaColumnLabel, higherValueFormula, higherPolynomial, eval_motionColumn,
      motionValue] using
      ((hy (Fin.natAdd m 0)).mul (hy (Fin.natAdd m 1))).mul ((hL 1).sub (hL 0))

/-- Relation between a symbolic fixed row and its actual row. -/
def HigherFormulaRow.Matches (row : HigherFormulaRow σ m) (actual : HigherFixedRow Q) : Prop :=
  match row, actual with
  | .inl e, .inl p => e = p.val
  | .inr (y, k), .inr (v, l) => k = l ∧ ∀ j, Formula.Matches x (y j) (v j)
  | _, _ => False

include ha in
theorem higherEntryFormula_matches {row : HigherFormulaRow σ m} {actual : HigherFixedRow Q}
    (hr : HigherFormulaRow.Matches Q x row actual) (col : HigherColumn Q) :
    Formula.Matches x (higherEntryFormula a Q.single row (higherFormulaColumnLabel Q col))
      (higherFixedValue Q actual col) := by
  rcases row with ⟨i, b⟩ | ⟨y, k⟩ <;> rcases actual with p | ⟨v, l⟩
  · change (i, b) = p.val at hr
    have hm := (higherValueFormula_matches Q x a ha (edgeRowFormula_matches Q x a ha p) 1 col).neg
    rw [← hr] at hm
    exact hm
  · contradiction
  · contradiction
  · obtain ⟨rfl, hy⟩ := hr
    exact higherValueFormula_matches Q x a ha hy k col

end Evaluation

section FixedProbes

variable {K : Type*} [Field K] {r : ℕ} (Q : Parameters K (m + 2))
variable (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)

/-- The symbolic paired probes followed by the two final probes. -/
def farPointFormula (p : Fin 2 → Fin 3 → Formula σ) : Fin (r + 2) → Fin (m + 2) → Formula σ :=
  Fin.addCases
    (fun i => pairProbeFormula (pairedIncidence Q pairing i 0).val.1
      (pairedIncidence Q pairing i 1).val.1)
    (fun i => finalProbeFormula (unpairedIncidence Q pairing).val.1 (p i))

/-- Symbolic rows in the same enumeration as the assembled B.4 matrix. -/
def fixedRowFormula (p : Fin 2 → Fin 3 → Formula σ) (i : HigherColumn Q) : HigherFormulaRow σ m :=
  match fixedIndex Q pairing i with
  | .inl e => .inl e.val
  | .inr (j, k) => .inr (farPointFormula Q pairing p j, k)

theorem farPointFormula_matches (x : σ → K) {p : Fin 2 → Fin 3 → Formula σ} {y : Fin 2 → Fin 3 → K}
    (hp : ∀ i j, Formula.Matches x (p i j) (y i j)) (i : Fin (r + 2)) (j : Fin (m + 2)) :
    Formula.Matches x (farPointFormula Q pairing p i j) (farPoint Q pairing y i j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [farPointFormula, farPoint, Fin.addCases_left] using
      pairProbeFormula_matches x (pairedIncidence Q pairing i 0).val.1
        (pairedIncidence Q pairing i 1).val.1 j
  · simpa only [farPointFormula, farPoint, Fin.addCases_right] using
      finalProbeFormula_matches x (unpairedIncidence Q pairing).val.1 (hp i) j

theorem fixedRowFormula_matches (x : σ → K) {p : Fin 2 → Fin 3 → Formula σ} {y : Fin 2 → Fin 3 → K}
    (hp : ∀ i j, Formula.Matches x (p i j) (y i j)) (i : HigherColumn Q) :
    HigherFormulaRow.Matches Q x (fixedRowFormula Q pairing p i) (fixedProbeRow Q pairing y i) := by
  rw [← fixedEnumeration_eq_fixedProbeRow]
  unfold fixedRowFormula B4.fixedEnumeration
  cases hi : fixedIndex Q pairing i with
  | inl e => exact rfl
  | inr j =>
    rcases j with ⟨j, k⟩
    exact ⟨rfl, farPointFormula_matches Q pairing x hp j⟩

/-- The symbolic square B.22 block with a common row and column index. -/
def fixedHigherFormulaMatrix (a : PrimitiveIndex (m + 2) → Formula σ) (p : Fin 2 → Fin 3 → Formula σ) :
    Matrix (HigherColumn Q) (HigherColumn Q) (Formula σ) := fun i j =>
  higherEntryFormula a Q.single (fixedRowFormula Q pairing p i) (higherFormulaColumnLabel Q j)

/-- The denominator-cleared determinant of the actual fixed higher block. -/
def fixedHigherCertificate (a : PrimitiveIndex (m + 2) → Formula σ) (p : Fin 2 → Fin 3 → Formula σ) :
    MvPolynomial σ ℤ :=
  matrixCertificate (fixedHigherFormulaMatrix Q pairing a p)

variable (x : σ → K) (a : PrimitiveIndex (m + 2) → Formula σ)
variable (ha : ∀ i, Formula.Matches x (a i) (primitiveValue Q i))
variable {p : Fin 2 → Fin 3 → Formula σ} {y : Fin 2 → Fin 3 → K}
variable (hp : ∀ i j, Formula.Matches x (p i j) (y i j))

include ha hp in
theorem fixedHigherFormulaMatrix_matches (i j : HigherColumn Q) :
    Formula.Matches x (fixedHigherFormulaMatrix Q pairing a p i j) (fixedHigherMatrix Q pairing y i j) :=
  higherEntryFormula_matches Q x a ha (fixedRowFormula_matches Q pairing x hp i) j

include ha hp in
/-- The integer polynomial detects the fixed higher block determinant on valid data. -/
theorem eval_fixedHigherCertificate_ne_zero_iff :
    evalPolynomial x (fixedHigherCertificate Q pairing a p) ≠ 0 ↔
      (fixedHigherMatrix Q pairing y).det ≠ 0 :=
  eval_matrixCertificate_ne_zero_iff_of_matches x _ _
    (fixedHigherFormulaMatrix_matches Q pairing x a ha hp)

include ha hp in
/-- The symbolic block matches the actual fixed-row evaluations in the B.4 step. -/
theorem fixedHigherFormulaMatrix_matches_parameterPhi {f : ℕ} (base : Fin f → Fin (m + 2) → K)
    (h₂ : (2 : K) ≠ 0) (h₆ : (6 : K) ≠ 0) (i j : HigherColumn Q) :
    Formula.Matches x (fixedHigherFormulaMatrix Q pairing a p i j)
      (B4.fixedValue Q base h₂ h₆ (B4.fixedEnumeration Q (farPoint Q pairing y)
        (fixedIndex Q pairing) i) (highParameter Q j)) := by
  have hm := fixedHigherFormulaMatrix_matches Q pairing x a ha hp i j
  rw [fixedHigherMatrix_eq_actual Q pairing base h₂ h₆ y, Matrix.of_apply] at hm
  exact hm

end FixedProbes

section GraphTransport

variable {K L : Type*} [Field K] [Field L] {r : ℕ}
variable (Q : Parameters K (m + 2)) (R : Parameters L (m + 2))

/-- Same graph flags give the same cross-incidence labels, independently of the field. -/
def incidenceEquivOfGraph (h : Q.single = R.single) : NewIncidence Q ≃ NewIncidence R where
  toFun p := ⟨p.val, h ▸ p.property⟩
  invFun p := ⟨p.val, h.symm ▸ p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1000000 in
/-- The symbolic certificate depends only on the graph and incidence pairing. -/
theorem fixedHigherCertificate_eq_of_graph (h : Q.single = R.single)
    (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)
    (a : PrimitiveIndex (m + 2) → Formula σ) (p : Fin 2 → Fin 3 → Formula σ) :
    fixedHigherCertificate Q pairing a p =
      fixedHigherCertificate R (pairing.trans (incidenceEquivOfGraph Q R h)) a p := by
  cases Q with
  | mk s vs vh es eh el hvs hvh hes heh hel =>
    cases R with
    | mk t vs' vh' es' eh' el' hvs' hvh' hes' heh' hel' =>
      change s = t at h
      subst t
      let U : Parameters K (m + 2) := ⟨s, vs, vh, es, eh, el, hvs, hvh, hes, heh, hel⟩
      let V : Parameters L (m + 2) := ⟨s, vs', vh', es', eh', el', hvs', hvh', hes', heh', hel'⟩
      change fixedHigherCertificate U pairing a p =
        fixedHigherCertificate V (pairing.trans (incidenceEquivOfGraph U V rfl)) a p
      have he : incidenceEquivOfGraph U V rfl = Equiv.refl (NewIncidence U) :=
        Equiv.ext fun _ => rfl
      rw [he, Equiv.trans_refl]
      have hm : fixedHigherFormulaMatrix U pairing a p = fixedHigherFormulaMatrix V pairing a p := by
        apply Matrix.ext
        intro i j
        have hi : fixedIndex U pairing i = fixedIndex V pairing i := by
          rcases i with ⟨e, b⟩ | q <;> rfl
        have hj : higherFormulaColumnLabel U j = higherFormulaColumnLabel V j := by
          rcases j with ⟨e, b⟩ | q <;> rfl
        have hp : farPointFormula U pairing p = farPointFormula V pairing p := by
          funext l
          refine Fin.addCases (fun l => ?_) (fun l => ?_) l
          · simp only [farPointFormula, Fin.addCases_left]
            rfl
          · simp only [farPointFormula, Fin.addCases_right]
            rfl
        have hs : U.single = V.single := rfl
        simp only [fixedHigherFormulaMatrix, fixedRowFormula, hi, hj, hp, hs]
        rcases fixedIndex V pairing i with e | ⟨l, k⟩ <;> rfl
      exact congrArg (matrixCertificate (c := HigherColumn U)) hm

end GraphTransport

/-- The integer-valued sample coordinates of the checked C.4 witness. -/
def c4ProbeFormula : Fin 2 → Fin 3 → Formula σ := ![![1, 1, 1], ![1, 2, 3]]

/-- The final sample coordinates interpreted in an arbitrary field. -/
def c4ProbeValues {K : Type*} [Field K] : Fin 2 → Fin 3 → K := ![![1, 1, 1], ![1, 2, 3]]

theorem c4ProbeFormula_matches_values {K : Type*} [Field K] (x : σ → K) (i : Fin 2) (j : Fin 3) :
    Formula.Matches x (c4ProbeFormula i j) (c4ProbeValues i j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact matchesOne x
    | exact Formula.Matches.ofNat x 2
    | exact Formula.Matches.ofNat x 3

section Split

variable {K : Type*} [Field K] {m r : ℕ} {P : Parameters K m} (Q : Parameters K (m + 2))
variable (pairing : ((Fin r × Fin 2) ⊕ Unit) ≃ NewIncidence Q)

/-- Denominator-cleared B.22 polynomial in split new and old cone coordinates. -/
def splitFixedHigherCertificate : MvPolynomial (NewPrimitiveIndex m ⊕ PrimitiveIndex m) ℤ :=
  fixedHigherCertificate Q pairing (splitPrimitiveVariable m) c4ProbeFormula

/-- The split certificate can be evaluated on a different realization of the same graph. -/
theorem splitFixedHigherCertificate_eq_of_graph {L : Type*} [Field L]
    (R : Parameters L (m + 2)) (h : Q.single = R.single) :
    splitFixedHigherCertificate Q pairing =
      splitFixedHigherCertificate R (pairing.trans (incidenceEquivOfGraph Q R h)) :=
  fixedHigherCertificate_eq_of_graph Q R h pairing (splitPrimitiveVariable m) c4ProbeFormula

theorem eval_splitFixedHigherCertificate_ne_zero_iff (h : Compatible P Q) :
    evalPolynomial
        (Sum.elim (fun j : NewPrimitiveIndex m => primitiveValue Q j.val) (primitiveValue P))
        (splitFixedHigherCertificate Q pairing) ≠ 0 ↔
      (fixedHigherMatrix Q pairing c4ProbeValues).det ≠ 0 :=
  eval_fixedHigherCertificate_ne_zero_iff Q pairing _ _ (splitPrimitiveVariable_matches h)
    (c4ProbeFormula_matches_values _)

open CubicParameterCompatibility in
/-- After specializing the old parameters, the B.22 test is a polynomial in the new ones. -/
theorem eval_specializedFixedHigherCertificate_ne_zero_iff (h : Compatible P Q) :
    MvPolynomial.eval (fun j : NewPrimitiveIndex m => primitiveValue Q j.val)
        (specialize (primitiveValue P) (intSumPolynomial K (splitFixedHigherCertificate Q pairing))) ≠ 0 ↔
      (fixedHigherMatrix Q pairing c4ProbeValues).det ≠ 0 := by
  rw [eval_specialize_intSumPolynomial]
  exact eval_splitFixedHigherCertificate_ne_zero_iff Q pairing h

end Split

/-- Each admissible old rational chart admits a compatible extension where the B.22 certificate
is nonzero, with the old coordinates specialized to that chart. -/
theorem exists_b5_splitFixedHigherCertificate_ne_zero (n : ℕ)
    (P : Parameters ℚ (10 + 2 * n)) (hP : P.single = B5.single) :
    ∃ (Q : Parameters ℚ ((10 + 2 * n) + 2))
      (pairing : ((Fin (n + 3) × Fin 2) ⊕ Unit) ≃ NewIncidence Q),
      Compatible P Q ∧ Q.single = B5.single ∧
        evalPolynomial
          (Sum.elim (fun j : NewPrimitiveIndex (10 + 2 * n) => primitiveValue Q j.val)
            (primitiveValue P)) (splitFixedHigherCertificate Q pairing) ≠ 0 := by
  obtain ⟨Q, pairing, hcompat, hQ, hdet⟩ := exists_b5_fixedHigherWitness n P hP
  exact ⟨Q, pairing, hcompat, hQ, (eval_splitFixedHigherCertificate_ne_zero_iff Q pairing hcompat).mpr hdet⟩

end IdealGeneration.CubicSupported.B22
